package dev.perspective;

import android.app.KeyguardManager;
import android.content.BroadcastReceiver;
import android.content.Context;
import android.content.Intent;
import android.content.IntentFilter;
import android.graphics.BlendMode;
import android.graphics.Camera;
import android.graphics.LinearGradient;
import android.graphics.Matrix;
import android.graphics.RectF;
import android.graphics.RenderEffect;
import android.graphics.Shader;
import android.hardware.Sensor;
import android.hardware.SensorEvent;
import android.hardware.SensorEventListener;
import android.hardware.SensorManager;
import android.os.Build;
import android.os.Handler;
import android.os.Looper;
import android.os.PowerManager;
import android.text.Layout;
import android.util.DisplayMetrics;
import android.util.Log;
import android.view.Choreographer;
import android.view.View;
import android.view.ViewGroup;
import android.view.ViewParent;
import android.widget.TextView;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.WeakHashMap;

/**
 * The effect. The clock is a flat card that keeps facing the direction it faced a moment ago: when the phone
 * turns, the card is turned back by a small part of that turn around its own centre, in 3D, with a close camera,
 * so its perspective changes instead of it spinning in the screen plane.
 *
 * <p>Motion pipeline, built for softness:
 * <ol>
 *   <li>Game rotation vector (gyroscope + accelerometer). The neutral pose slowly follows the hand.</li>
 *   <li>Soft dead zone: hand tremor (about a degree) is squeezed to almost nothing, without a visible step.</li>
 *   <li>Small gain and a tanh limit: a few degrees at most, approached smoothly.</li>
 *   <li>A stiff critically damped spring, stepped on every display frame (Choreographer, vsync), not on sensor
 *       events: it follows the phone without a noticeable delay (it trails a turn by about 2 / FOLLOW_OMEGA s),
 *       and still gives ease-in / ease-out, no overshoot and no judder from sensor timing.</li>
 * </ol>
 * On sleep, unlock or when the clock is hidden, the same spring (a bit stiffer) brings the clock back to straight.
 * The sensor runs only while the screen is on, the keyguard is locked and a clock is shown. Main thread only.
 *
 * <p>Since 1.4 the turn goes through the view's animation matrix, around the centre of what the clock really draws
 * (its text lines / visible child views), measured again on every frame: the turn stays centred when the clock
 * moves, resizes or its digits change width, and the view's own rotation and pivot are left alone. While turned,
 * the edge going away from the viewer gets a light progressive Gaussian blur (none at the centre, the most at
 * that edge), like a shallow depth of field.
 *
 * <p>Since 1.5 the blur is only there while the clock follows the phone and System UI leaves the clock alone. A
 * blurred view is drawn on its own into an offscreen layer; when the clock morphed into the always-on display,
 * System UI drew it with blend modes meant for the real background, and inside that layer they showed up as a black
 * square under the digits. Now the blur is dropped at the first sign of going to sleep, on every way back to
 * straight, and while System UI scales, fades or resizes the clock (and {@link #CALM_NS} after that).
 */
final class Tilt implements SensorEventListener {
    // ------------------------------------------------------------------ feel
    /** Strongest tilt of the clock plane, degrees. Reached smoothly (tanh), never as a hard stop. */
    static final float MAX_DEG = 4f;
    /** Degrees of clock tilt per degree of phone turn. */
    static final float GAIN = 0.3f;
    /** Phone turns well below this (degrees) are mostly ignored: no reaction to hand tremor. */
    static final float DEADZONE_DEG = 1.6f;
    /** Direction of the effect per axis; -1 inverts it. */
    static final float SIGN_X = 1f, SIGN_Y = -1f;   // horizontal (side edges) inverted in 1.2
    /** How fast the neutral pose follows the hand, seconds. */
    static final float NEUTRAL_TAU_S = 2.4f;
    /**
     * Spring stiffness (natural frequency, 1/s) while following the phone: lower = softer, slower.
     * The clock trails a steady turn by about 2 / FOLLOW_OMEGA seconds: 4.6 (up to 1.2) gave ~0.43 s, 20 gives ~0.1 s.
     */
    static final float FOLLOW_OMEGA = 20f;
    /** Sensor sampling period, microseconds: 10 ms = 100 Hz (SENSOR_DELAY_GAME was ~50 Hz). */
    static final int SENSOR_PERIOD_US = 10_000;
    /** Spring stiffness of the way back to straight after unlocking or when the clock is hidden. */
    static final float RETURN_OMEGA = 6f;
    /** Spring stiffness of the way back when the screen goes off: done within the screen-off animation. */
    static final float SLEEP_OMEGA = 8.5f;
    /** The effect fades in over this time after the lock screen appears, seconds. */
    static final float FADE_IN_S = 0.9f;
    /** Camera distance in dp: smaller = stronger perspective. */
    static final float CAMERA_DP = 1100f;
    /**
     * Blur radius at the far edge of the clock at the strongest tilt (MAX_DEG), dp: a light touch. The blur grows
     * from nothing at the clock's centre to this at its edge, and with the tilt. 0 turns the blur off.
     */
    static final float BLUR_MAX_DP = 3f;
    /** Which edge is blurred: true = the one turning away from you, false = the one turning towards you. */
    static final boolean BLUR_FAR_EDGE = true;
    /** Below this radius (px) there is no blur at all, so a straight clock costs nothing. */
    private static final float BLUR_MIN_PX = 0.35f;
    /** Share of the blurred copy from the centre (0) to the far edge (1): position squared, eases in. */
    private static final float[] RAMP_AT = {0f, 0.25f, 0.5f, 0.75f, 1f};
    private static final int[] RAMP_ALPHA = {0x00000000, 0x10000000, 0x40000000, 0x90000000, 0xFF000000};
    /** How often the clock views and the lock state are re-checked while locked, ms. */
    static final long CHECK_MS = 400;
    /** After System UI scales, fades or resizes the clock (its own animations), no blur for this long, ns. */
    static final long CALM_NS = 600_000_000L;

    private static final float SETTLED_DEG = 0.004f, SETTLED_SPEED = 0.02f;
    private static final String TAG = HookEntry.TAG;
    private static final Tilt I = new Tilt();

    private final Handler main = new Handler(Looper.getMainLooper());
    private final Set<View> listened = weakSet(), tracked = weakSet(), touched = weakSet();
    private final List<View> targets = new ArrayList<>();
    private final Runnable check = this::check;
    private final Choreographer.FrameCallback frame = this::onFrame;
    private final float[] q = new float[4], q0 = new float[4], rel = new float[4];
    private final View.OnAttachStateChangeListener clockListener = listener(false), textClockListener = listener(true);
    /** Views wearing our blur, and views whose render effect was set by someone else (System UI's own). */
    private final Set<View> blurred = weakSet(), foreignFx = weakSet();
    /** What was last given to each view: nothing is re-sent while it stays the same. */
    private final Map<View, Matrix> lastTurn = new WeakHashMap<>();
    private final Map<View, float[]> lastBlur = new WeakHashMap<>();
    /** Per view: what System UI last did to it (scale with its parents, alpha, height of what it draws). */
    private final Map<View, float[]> lastLook = new WeakHashMap<>();
    /** Per view: no blur before this frame time (ns), because System UI is animating the clock. */
    private final Map<View, Long> calmUntil = new WeakHashMap<>();
    private final Camera camera = new Camera();
    private final Matrix turn = new Matrix(), anim = new Matrix(), comb = new Matrix();
    private final float[] pt = new float[2], mv = new float[9];
    private final RectF box = new RectF(), part = new RectF();
    private boolean settingFx, blurOff;

    private Context ctx;
    private SensorManager sensors;
    private Sensor sensor;
    private PowerManager power;
    private KeyguardManager keyguard;

    private boolean running, hasNeutral, sleeping, framePosted;
    private long lastNs, neutralNs, lastFrameNs;
    /** Where the sensor wants the clock (degrees) and the spring state that follows it. */
    private float goalX, goalY, x, y, vx, vy;
    private float omega = FOLLOW_OMEGA;

    private final BroadcastReceiver screen = new BroadcastReceiver() {
        @Override public void onReceive(Context c, Intent i) {
            try {
                String a = i.getAction();
                if (Intent.ACTION_SCREEN_OFF.equals(a)) {
                    sleep();
                } else if (Intent.ACTION_SCREEN_ON.equals(a)) {
                    wake();
                } else {
                    kick();
                }
            } catch (Throwable t) {
                Log.e(TAG, "screen", t);
            }
        }
    };

    private Tilt() { }

    private static <T> Set<T> weakSet() {
        return Collections.newSetFromMap(new WeakHashMap<T, Boolean>());
    }

    // ------------------------------------------------------------------ entry points (hooks)

    /** A new clock view (from a hook). {@code textClock}: only used when it sits inside a keyguard view. */
    static void track(View v, boolean textClock) {
        if (v == null) return;
        if (Looper.myLooper() != Looper.getMainLooper()) {
            I.main.post(() -> track(v, textClock));
            return;
        }
        try {
            I.listen(v, textClock);
        } catch (Throwable t) {
            Log.e(TAG, "track", t);
        }
    }

    /** System UI starts going to sleep: the earliest moment, while the screen is still lit. */
    static void goingToSleep() {
        if (Looper.myLooper() != Looper.getMainLooper()) {
            I.main.post(Tilt::goingToSleep);
            return;
        }
        try {
            I.sleep();
        } catch (Throwable t) {
            Log.e(TAG, "sleep", t);
        }
    }

    /** View.setRenderEffect is called (from a hook, before the call); our own calls are skipped. */
    static void renderEffectSet(View v, Object effect) {
        if (v == null || I.settingFx || Looper.myLooper() != Looper.getMainLooper()) return;
        I.blurred.remove(v);
        I.lastBlur.remove(v);
        if (effect != null) I.foreignFx.add(v);
        else I.foreignFx.remove(v);
    }

    // ------------------------------------------------------------------ views

    private View.OnAttachStateChangeListener listener(boolean textClock) {
        return new View.OnAttachStateChangeListener() {
            @Override public void onViewAttachedToWindow(View v) {
                attached(v, textClock);
            }

            @Override public void onViewDetachedFromWindow(View v) {
                detached(v);
            }
        };
    }

    private void listen(View v, boolean textClock) {
        if (!listened.add(v)) return;
        v.addOnAttachStateChangeListener(textClock ? textClockListener : clockListener);
        if (v.isAttachedToWindow()) attached(v, textClock);
    }

    private void attached(View v, boolean textClock) {
        try {
            if (inAod(v) || (textClock && !underKeyguard(v))) return;
            init(v.getContext());
            tracked.add(v);
            kick();
        } catch (Throwable t) {
            Log.e(TAG, "attach", t);
        }
    }

    private void detached(View v) {
        try {
            tracked.remove(v);
            if (targets.remove(v)) reset(v);
            kick();
        } catch (Throwable t) {
            Log.e(TAG, "detach", t);
        }
    }

    /** The always-on display keeps its own, still clock. */
    private static boolean inAod(View v) {
        for (ViewParent p = v.getParent(); p != null; p = p.getParent()) {
            if (p.getClass().getName().toLowerCase(Locale.ROOT).contains("aod")) return true;
        }
        return false;
    }

    /** The nearest telling ancestor decides: keyguard / lock screen yes; status bar, shade, QS, AOD no. */
    private static boolean underKeyguard(View v) {
        for (ViewParent p = v.getParent(); p != null; p = p.getParent()) {
            String n = p.getClass().getName().toLowerCase(Locale.ROOT);
            if (n.contains("statusbar") || n.contains("notification") || n.contains("aod")
                    || n.contains("qspanel") || n.contains("quicksetting") || n.contains("qsfragment")) return false;
            if (n.contains("keyguard") || n.contains("lockscreen")) return true;
        }
        return false;
    }

    // ------------------------------------------------------------------ state

    private void init(Context c) {
        if (ctx != null) return;
        Context app = c.getApplicationContext();
        ctx = app != null ? app : c;
        sensors = ctx.getSystemService(SensorManager.class);
        power = ctx.getSystemService(PowerManager.class);
        keyguard = ctx.getSystemService(KeyguardManager.class);
        if (sensors != null) {
            sensor = sensors.getDefaultSensor(Sensor.TYPE_GAME_ROTATION_VECTOR);
            if (sensor == null) sensor = sensors.getDefaultSensor(Sensor.TYPE_ROTATION_VECTOR);
        }
        IntentFilter f = new IntentFilter();
        f.addAction(Intent.ACTION_SCREEN_ON);
        f.addAction(Intent.ACTION_SCREEN_OFF);
        f.addAction(Intent.ACTION_USER_PRESENT);
        try {
            if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.TIRAMISU) {
                ctx.registerReceiver(screen, f, null, main, Context.RECEIVER_EXPORTED);
            } else {
                ctx.registerReceiver(screen, f, null, main);
            }
        } catch (Throwable t) {
            Log.e(TAG, "screen receiver (falls back to view events)", t);
        }
    }

    private void kick() {
        main.removeCallbacks(check);
        main.post(check);
    }

    private void sleep() {
        if (sleeping) return;
        sleeping = true;
        main.removeCallbacks(check);
        dropBlur();          // at once: the clock is about to morph into the always-on display
        release(SLEEP_OMEGA);
    }

    /** Screen on: if the way back did not finish in the dark, finish it now, before anyone sees a frame. */
    private void wake() {
        sleeping = false;
        if (!running) snapStraight();
        kick();
    }

    private void check() {
        main.removeCallbacks(check);
        try {
            boolean on = interactive();
            boolean lockedAndOn = on && locked();
            boolean want = !sleeping && lockedAndOn && sensor != null && collect();
            if (want) start();
            else release(on ? RETURN_OMEGA : SLEEP_OMEGA);
            // the bouncer, the shade or a re-inflated clock can change what is shown at any time
            if (lockedAndOn && !sleeping && !tracked.isEmpty()) main.postDelayed(check, CHECK_MS);
        } catch (Throwable t) {
            Log.e(TAG, "check", t);
            if (running) sensors.unregisterListener(this);
            running = false;
            snapStraight();
        }
    }

    private boolean interactive() {
        return power == null || power.isInteractive();
    }

    private boolean locked() {
        return keyguard == null || keyguard.isKeyguardLocked();
    }

    /**
     * Picks the views to turn: shown clock views without a clock ancestor. A clock split into sibling views
     * (hours / minutes) turns as one card through their common parent, unless that parent is the whole screen.
     */
    private boolean collect() {
        List<View> shown = new ArrayList<>();
        for (View v : tracked) if (visible(v)) shown.add(v);
        List<View> outer = new ArrayList<>();
        for (View v : shown) if (!hasAncestorIn(v, shown)) outer.add(v);
        Map<ViewParent, Integer> perParent = new HashMap<>();
        for (View v : outer) perParent.merge(v.getParent(), 1, Integer::sum);
        Set<View> next = new LinkedHashSet<>();
        for (View v : outer) {
            ViewParent p = v.getParent();
            Integer n = perParent.get(p);
            if (n != null && n > 1 && p instanceof View && !screenSized((View) p)) next.add((View) p);
            else next.add(v);
        }
        for (View old : targets) if (!next.contains(old)) reset(old);
        targets.clear();
        targets.addAll(next);
        return !targets.isEmpty();
    }

    private static boolean visible(View v) {
        return v.isAttachedToWindow() && v.isShown() && v.getWidth() > 0 && v.getHeight() > 0 && v.getAlpha() > 0.01f;
    }

    private static boolean hasAncestorIn(View v, List<View> views) {
        for (ViewParent p = v.getParent(); p != null; p = p.getParent()) {
            if (p instanceof View && views.contains(p)) return true;
        }
        return false;
    }

    private static boolean screenSized(View p) {
        View root = p.getRootView();
        return root != null && root.getWidth() > 0
                && p.getWidth() >= root.getWidth() * 0.9f && p.getHeight() >= root.getHeight() * 0.5f;
    }

    /** Sensor on; the spring keeps its current state, so a return in progress turns smoothly into following. */
    private void start() {
        omega = FOLLOW_OMEGA;
        if (running || sensors == null || sensor == null) return;
        hasNeutral = false;
        lastNs = 0;
        goalX = goalY = 0;
        running = sensors.registerListener(this, sensor, SENSOR_PERIOD_US, main);
        if (running) postFrame();
    }

    /** Sensor off and the clock springs back to straight; a stiffer request wins over a softer one. */
    private void release(float returnOmega) {
        boolean wasRunning = running;
        if (running) {
            sensors.unregisterListener(this);
            running = false;
        }
        hasNeutral = false;
        goalX = goalY = 0;
        dropBlur();          // no blur on any way back: System UI animates the clock then (sleep, AOD, unlock)
        if (targets.isEmpty()) {
            snapStraight();
            return;
        }
        omega = wasRunning ? returnOmega : Math.max(omega, returnOmega);
        postFrame();
    }

    /** Our blur off at once, on every view wearing it (an effect of System UI stays). */
    private void dropBlur() {
        if (blurred.isEmpty()) return;
        for (View v : new ArrayList<>(blurred)) {
            lastBlur.remove(v);
            setFx(v, null);
        }
    }

    /** Straight at once, without animation: only when nobody can see it (screen just turned on, errors). */
    private void snapStraight() {
        x = y = vx = vy = goalX = goalY = 0;
        for (View v : targets) reset(v);
        targets.clear();
    }

    /** Only views this module turned are put back: no turn, and our blur off (an effect of System UI stays). */
    private void reset(View v) {
        if (!touched.remove(v)) return;
        v.setAnimationMatrix(null);
        lastTurn.remove(v);
        lastBlur.remove(v);
        lastLook.remove(v);
        calmUntil.remove(v);
        if (blurred.contains(v)) setFx(v, null);
    }

    // ------------------------------------------------------------------ sensor: where the clock should go

    @Override public void onSensorChanged(SensorEvent e) {
        if (!running) return;
        try {
            SensorManager.getQuaternionFromVector(q, e.values);          // w, x, y, z
            float dt = lastNs == 0 ? 0.02f : clamp((e.timestamp - lastNs) / 1e9f, 0.001f, 0.1f);
            lastNs = e.timestamp;
            if (!hasNeutral) {
                System.arraycopy(q, 0, q0, 0, 4);
                hasNeutral = true;
                neutralNs = e.timestamp;
                return;
            }
            if (dot(q0, q) < 0) for (int i = 0; i < 4; i++) q[i] = -q[i];
            // the neutral pose slowly follows the hand
            float a = dt / (NEUTRAL_TAU_S + dt);
            for (int i = 0; i < 4; i++) q0[i] += (q[i] - q0[i]) * a;
            normalize(q0);
            // the turn since the neutral pose, in the phone's own axes: conj(q0) * q
            conjMul(q0, q, rel);
            if (rel[0] < 0) for (int i = 0; i < 4; i++) rel[i] = -rel[i];
            float dx = (float) Math.toDegrees(2 * Math.asin(clamp(rel[1], -1f, 1f)));   // top edge to / from you
            float dy = (float) Math.toDegrees(2 * Math.asin(clamp(rel[2], -1f, 1f)));   // side edges to / from you
            float fade = smoothstep(clamp((e.timestamp - neutralNs) / 1e9f / FADE_IN_S, 0f, 1f));
            goalX = soft(SIGN_X * GAIN * fade * deadzone(dx));
            goalY = soft(SIGN_Y * GAIN * fade * deadzone(dy));
        } catch (Throwable t) {
            Log.e(TAG, "sensor", t);
            release(RETURN_OMEGA);
        }
    }

    @Override public void onAccuracyChanged(Sensor s, int accuracy) { }

    // ------------------------------------------------------------------ frames: where the clock is

    private void postFrame() {
        if (framePosted) return;
        framePosted = true;
        lastFrameNs = 0;
        Choreographer.getInstance().postFrameCallback(frame);
    }

    private void onFrame(long nowNs) {
        framePosted = false;
        try {
            float dt = lastFrameNs == 0 ? 1f / 60f : clamp((nowNs - lastFrameNs) / 1e9f, 0.001f, 0.05f);
            lastFrameNs = nowNs;
            spring(true, goalX, dt);
            spring(false, goalY, dt);
            if (!running && settled()) {
                snapStraight();
                return;
            }
            // on every frame: the clock can move or resize while the angle stays; apply() re-sends only changes
            apply();
            framePosted = true;
            Choreographer.getInstance().postFrameCallback(frame);
        } catch (Throwable t) {
            Log.e(TAG, "frame", t);
            snapStraight();
        }
    }

    /** Exact step of a critically damped spring (no overshoot) towards {@code goal}. */
    private void spring(boolean isX, float goal, float dt) {
        float pos = (isX ? x : y) - goal, vel = isX ? vx : vy;
        float e = (float) Math.exp(-omega * dt);
        float c = (vel + omega * pos) * dt;
        float nPos = (pos + c) * e, nVel = (vel - omega * c) * e;
        if (isX) {
            x = nPos + goal;
            vx = nVel;
        } else {
            y = nPos + goal;
            vy = nVel;
        }
    }

    private boolean settled() {
        return Math.abs(x) < SETTLED_DEG && Math.abs(y) < SETTLED_DEG
                && Math.abs(vx) < SETTLED_SPEED && Math.abs(vy) < SETTLED_SPEED;
    }

    /**
     * Draws the current turn on every clock view: the same 3D rotation rotationX / rotationY would give, but through
     * the view's animation matrix and around the centre of what the clock draws on this frame, so the turn stays
     * centred when the clock moves, resizes or its digits change width.
     */
    private void apply() {
        if (ctx == null) return;
        DisplayMetrics dm = ctx.getResources().getDisplayMetrics();
        camera.save();
        camera.setLocation(0f, 0f, -CAMERA_DP * dm.density / dm.densityDpi);   // as View.setCameraDistance
        camera.rotateX(x);
        camera.rotateY(y);
        camera.getMatrix(turn);
        camera.restore();
        float strength = clamp((float) Math.hypot(x, y) / MAX_DEG, 0f, 1f);
        float radius = BLUR_MAX_DP * dm.density * strength;
        for (View v : targets) {
            touched.add(v);
            contentBox(v);
            Matrix own = v.getMatrix();          // the view's own scale / translation (System UI animations)
            pt[0] = box.centerX();
            pt[1] = box.centerY();
            own.mapPoints(pt);                   // where the clock's centre is drawn now
            anim.set(turn);
            anim.preTranslate(-pt[0], -pt[1]);
            anim.postTranslate(pt[0], pt[1]);
            Matrix last = lastTurn.get(v);
            if (last == null || !last.equals(anim)) {
                v.setAnimationMatrix(anim);
                if (last == null) lastTurn.put(v, new Matrix(anim));
                else last.set(anim);
            }
            boolean calm = systemAnimating(v, lastFrameNs);
            if (!blurOff) {
                try {
                    if (running && !sleeping && !calm) {
                        blur(v, own, radius);
                    } else if (blurred.contains(v)) {
                        setFx(v, null);
                        lastBlur.remove(v);
                    }
                } catch (Throwable t) {
                    blurOff = true;
                    Log.e(TAG, "blur (off until System UI restarts)", t);
                    if (blurred.contains(v)) setFx(v, null);
                }
            }
        }
    }

    /**
     * True while System UI animates the clock itself, and for {@link #CALM_NS} after: the scale (its own or a
     * parent's), the alpha or the height of what it draws (font size) changed since the last frame. A blurred view
     * is drawn alone into an offscreen layer, and with the blend modes System UI uses in those animations (the morph
     * into the always-on display above all) its backing then shows as a black square, so the blur waits.
     */
    private boolean systemAnimating(View v, long nowNs) {
        float sx = 1f, sy = 1f, alpha = 1f;
        View c = v;
        for (int depth = 0; c != null && depth < 24; depth++) {
            sx *= c.getScaleX();
            sy *= c.getScaleY();
            alpha *= c.getAlpha();
            ViewParent p = c.getParent();
            c = p instanceof View ? (View) p : null;
        }
        float h = box.height();
        float[] last = lastLook.get(v);
        boolean changed = last == null
                || Math.abs(last[0] - sx) > 1e-3f || Math.abs(last[1] - sy) > 1e-3f
                || Math.abs(last[2] - alpha) > 0.01f || Math.abs(last[3] - h) > 0.5f;
        if (last == null) {
            lastLook.put(v, new float[] {sx, sy, alpha, h});
        } else {
            last[0] = sx;
            last[1] = sy;
            last[2] = alpha;
            last[3] = h;
        }
        if (changed) calmUntil.put(v, nowNs + CALM_NS);
        Long until = calmUntil.get(v);
        return until != null && nowNs < until;
    }

    /**
     * Progressive blur towards the far edge of the clock: the sharp clock and a blurred copy are mixed through a
     * linear ramp that runs from the clock's centre (all sharp) to its far edge (all blurred); the radius grows with
     * the tilt. Nothing at all while the clock is straight, and never over an effect of System UI.
     */
    private void blur(View v, Matrix own, float radius) {
        if (foreignFx.contains(v)) return;
        float ux = 0f, uy = 0f;
        if (radius >= BLUR_MIN_PX) {
            // depth of a point (x, y) of the view: w = m6 * x + m7 * y + m8 of its whole drawing matrix
            comb.set(own);
            comb.postConcat(anim);
            comb.getValues(mv);
            float len = (float) Math.hypot(mv[Matrix.MPERSP_0], mv[Matrix.MPERSP_1]);
            if (len > 1e-12f) {
                float s = BLUR_FAR_EDGE ? 1f : -1f;
                ux = s * mv[Matrix.MPERSP_0] / len;
                uy = s * mv[Matrix.MPERSP_1] / len;
            }
        }
        if (ux == 0f && uy == 0f) {
            if (blurred.contains(v)) setFx(v, null);
            lastBlur.remove(v);
            return;
        }
        float cx = box.centerX(), cy = box.centerY();
        float reach = Math.max(1f, Math.abs(ux) * box.width() / 2f + Math.abs(uy) * box.height() / 2f);
        float ex = cx + ux * reach, ey = cy + uy * reach;
        float[] last = lastBlur.get(v);
        if (last != null && blurred.contains(v) && Math.abs(last[0] - radius) < 0.02f
                && Math.abs(last[1] - cx) < 0.25f && Math.abs(last[2] - cy) < 0.25f
                && Math.abs(last[3] - ex) < 0.25f && Math.abs(last[4] - ey) < 0.25f) return;
        RenderEffect mask = RenderEffect.createShaderEffect(
                new LinearGradient(cx, cy, ex, ey, RAMP_ALPHA, RAMP_AT, Shader.TileMode.CLAMP));
        // blurred copy * ramp + sharp clock * (1 - ramp)
        RenderEffect soft = RenderEffect.createBlendModeEffect(mask,
                RenderEffect.createBlurEffect(radius, radius, Shader.TileMode.DECAL), BlendMode.SRC_IN);
        RenderEffect sharp = RenderEffect.createBlendModeEffect(mask,
                RenderEffect.createOffsetEffect(0f, 0f), BlendMode.SRC_OUT);
        setFx(v, RenderEffect.createBlendModeEffect(sharp, soft, BlendMode.PLUS));
        if (last == null) {
            lastBlur.put(v, new float[] {radius, cx, cy, ex, ey});
        } else {
            last[0] = radius;
            last[1] = cx;
            last[2] = cy;
            last[3] = ex;
            last[4] = ey;
        }
    }

    private void setFx(View v, RenderEffect fx) {
        settingFx = true;
        try {
            v.setRenderEffect(fx);
        } finally {
            settingFx = false;
        }
        if (fx != null) blurred.add(v);
        else blurred.remove(v);
    }

    /** {@link #box}: what the clock really draws, in its own coordinates; the whole view if nothing is found. */
    private void contentBox(View target) {
        box.setEmpty();
        addContent(target, target, 0);
        if (box.width() <= 0f || box.height() <= 0f) box.set(0f, 0f, target.getWidth(), target.getHeight());
    }

    /** Adds the drawn part of {@code v} (its visible children, else itself) to {@link #box}. */
    private boolean addContent(View target, View v, int depth) {
        if (v.getVisibility() != View.VISIBLE || v.getAlpha() <= 0.01f || v.getWidth() <= 0 || v.getHeight() <= 0) {
            return false;
        }
        if (v instanceof ViewGroup && depth < 8) {
            ViewGroup g = (ViewGroup) v;
            boolean any = false;
            for (int i = 0, n = g.getChildCount(); i < n; i++) {
                View c = g.getChildAt(i);
                if (c != null && addContent(target, c, depth + 1)) any = true;
            }
            if (any) return true;
        }
        if (!drawn(v, part)) return false;
        // into the clock's coordinates: positions, translations and scrolling (scales inside the clock are ignored)
        for (View c = v; c != target; ) {
            ViewParent p = c.getParent();
            if (!(p instanceof View)) return false;
            View pv = (View) p;
            part.offset(c.getLeft() + c.getTranslationX() - pv.getScrollX(),
                    c.getTop() + c.getTranslationY() - pv.getScrollY());
            c = pv;
        }
        box.union(part);
        return true;
    }

    /** The part of {@code v} that draws something, in its own coordinates (text lines for text); false if none. */
    private static boolean drawn(View v, RectF out) {
        if (v instanceof TextView) {
            TextView t = (TextView) v;
            if (t.length() == 0) return false;
            Layout l = t.getLayout();
            int n = l == null ? 0 : l.getLineCount();
            if (n > 0) {
                float left = Float.MAX_VALUE, right = -Float.MAX_VALUE;
                for (int i = 0; i < n; i++) {
                    left = Math.min(left, l.getLineLeft(i));
                    right = Math.max(right, l.getLineRight(i));
                }
                float px = t.getTotalPaddingLeft() - t.getScrollX(), py = t.getTotalPaddingTop() - t.getScrollY();
                out.set(px + left, py + l.getLineTop(0), px + right, py + l.getLineBottom(n - 1));
                if (out.width() > 0f && out.height() > 0f) return true;
            }
        } else if (v.willNotDraw() && v.getBackground() == null) {
            return false;
        }
        out.set(0f, 0f, v.getWidth(), v.getHeight());
        return true;
    }

    // ------------------------------------------------------------------ math

    static float soft(float deg) {
        return (float) (MAX_DEG * Math.tanh(deg / MAX_DEG));
    }

    /** Smooth dead zone: ~d for large turns, ~d^3 / dz^2 for tiny ones; no step anywhere. */
    static float deadzone(float d) {
        float d2 = d * d;
        return d * d2 / (d2 + DEADZONE_DEG * DEADZONE_DEG);
    }

    static float smoothstep(float t) {
        return t * t * (3f - 2f * t);
    }

    static float clamp(float v, float lo, float hi) {
        return v < lo ? lo : v > hi ? hi : v;
    }

    static float dot(float[] a, float[] b) {
        return a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3];
    }

    static void normalize(float[] a) {
        float n = (float) Math.sqrt(dot(a, a));
        if (n < 1e-6f) return;
        for (int i = 0; i < 4; i++) a[i] /= n;
    }

    /** out = conj(a) * b, quaternions as w, x, y, z. */
    static void conjMul(float[] a, float[] b, float[] out) {
        float pw = a[0], px = -a[1], py = -a[2], pz = -a[3];
        float qw = b[0], qx = b[1], qy = b[2], qz = b[3];
        out[0] = pw * qw - px * qx - py * qy - pz * qz;
        out[1] = pw * qx + px * qw + py * qz - pz * qy;
        out[2] = pw * qy - px * qz + py * qw + pz * qx;
        out[3] = pw * qz + px * qy - py * qx + pz * qw;
    }
}
