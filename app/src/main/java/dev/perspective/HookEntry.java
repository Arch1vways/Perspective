package dev.perspective;

import android.util.Log;
import android.view.View;
import android.widget.TextClock;
import java.lang.reflect.Constructor;
import java.lang.reflect.Executable;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.WeakHashMap;
import java.util.concurrent.atomic.AtomicBoolean;
import io.github.libxposed.api.XposedInterface;
import io.github.libxposed.api.XposedInterface.HookHandle;
import io.github.libxposed.api.XposedInterface.Hooker;
import io.github.libxposed.api.XposedModule;

/**
 * LSPosed entry point (libxposed API 102). Finds the lock screen clock views and hands them to {@link Tilt}.
 *
 * <ul>
 *   <li>OriginOS: the lock screen clock lives in the vivo System UI plugin, which is loaded lazily, so class loading
 *       is watched for clock / time views of {@code com.vivo.systemuiplugin.keyguard.*}.</li>
 *   <li>AOSP-like ROMs: {@code KeyguardClockSwitch} / {@code AnimatableClockView}.</li>
 *   <li>Fallback: any {@link TextClock} that sits inside a keyguard view.</li>
 * </ul>
 * Only views are collected here; whether one is really tilted is decided by {@link Tilt} (shown, on the lock
 * screen, outermost clock view). Every hook is protective: a failure must never break the lock screen.
 */
public final class HookEntry extends XposedModule {
    static final String TAG = "Perspective";
    static final String SYSTEMUI = "com.android.systemui";
    static final String PLUGIN = "com.vivo.systemuiplugin";
    private static final String VIVO_KEYGUARD = PLUGIN + ".keyguard.";
    private static final String[] AOSP_CLOCKS = {
            "com.android.keyguard.KeyguardClockSwitch",
            "com.android.systemui.shared.clocks.AnimatableClockView",
    };
    /** Clock-like names that are not the lock screen clock itself. */
    private static final String[] NOT_A_CLOCK = {
            "aod", "preview", "setting", "edit", "adapter", "picker", "recycler", "dialog", "timer", "stopwatch",
            "timeout", "worldclock", "calendar", "weather",
    };

    private static final AtomicBoolean WATCHING = new AtomicBoolean(), TEXT_CLOCK = new AtomicBoolean(),
            RENDER_EFFECT = new AtomicBoolean();
    private static final Set<Class<?>> INSTALLED = Collections.newSetFromMap(new WeakHashMap<Class<?>, Boolean>());

    @Override public void onModuleLoaded(ModuleLoadedParam param) {
        xposed = this;
    }

    @Override public void onPackageReady(PackageReadyParam param) {
        String pkg = param.getPackageName();
        if (!SYSTEMUI.equals(pkg) && !PLUGIN.equals(pkg)) return;
        ClassLoader cl = param.getClassLoader();
        for (String name : AOSP_CLOCKS) {
            try {
                install(Class.forName(name, false, cl));
            } catch (Throwable ignored) {
                // not on this ROM
            }
        }
        hookTextClock();
        hookRenderEffect();
        if (SYSTEMUI.equals(pkg)) hookSleep(cl);
        if (WATCHING.compareAndSet(false, true)) {
            try {
                interceptMethods(ClassLoader.class, "loadClass", chain -> {
                    Object result = chain.proceed();
                    if (result instanceof Class) {
                        try {
                            Class<?> loaded = (Class<?>) result;
                            if (isVivoClock(loaded)) install(loaded);
                        } catch (Throwable t) {
                            Log.e(TAG, "class watcher", t);
                        }
                    }
                    return result;
                });
            } catch (Throwable t) {
                hookError("class watcher (only already loaded clocks are used)", t);
            }
        }
    }

    /** A View of the vivo keyguard whose name says clock / time, but not an AOD, editor or preview one. */
    static boolean isVivoClock(Class<?> type) {
        String name = type.getName();
        if (!name.startsWith(VIVO_KEYGUARD)) return false;
        String n = name.toLowerCase(Locale.ROOT);
        if (!n.contains("clock") && !n.contains("time")) return false;
        for (String bad : NOT_A_CLOCK) if (n.contains(bad)) return false;
        return View.class.isAssignableFrom(type);
    }

    /** Every new instance of a clock class is handed to {@link Tilt}, which follows its attach state. */
    private static void install(Class<?> type) {
        if (type == null || !View.class.isAssignableFrom(type)) return;
        synchronized (INSTALLED) {
            if (!INSTALLED.add(type)) return;
        }
        try {
            interceptConstructors(type, chain -> {
                Object result = chain.proceed();
                Object v = chain.getThisObject();
                if (v instanceof View) Tilt.track((View) v, false);
                return result;
            });
        } catch (Throwable t) {
            hookError("hook " + type.getName(), t);
        }
    }

    private static void hookTextClock() {
        if (!TEXT_CLOCK.compareAndSet(false, true)) return;
        try {
            interceptConstructors(TextClock.class, chain -> {
                Object result = chain.proceed();
                Object v = chain.getThisObject();
                if (v instanceof View) Tilt.track((View) v, true);
                return result;
            });
        } catch (Throwable t) {
            hookError("TextClock", t);
        }
    }

    /** Tells {@link Tilt} when someone else sets a render effect on a view, so its blur never covers System UI's. */
    private static void hookRenderEffect() {
        if (!RENDER_EFFECT.compareAndSet(false, true)) return;
        try {
            interceptMethods(View.class, "setRenderEffect", chain -> {
                try {
                    Object v = chain.getThisObject();
                    if (v instanceof View) Tilt.renderEffectSet((View) v, chain.getArg(0));
                } catch (Throwable t) {
                    Log.e(TAG, "render effect", t);
                }
                return chain.proceed();
            });
        } catch (Throwable t) {
            hookError("setRenderEffect (the blur may then cover an effect of System UI)", t);
        }
    }

    /** The earliest "going to sleep" signals of System UI, so the clock returns while the screen is still lit. */
    private static void hookSleep(ClassLoader cl) {
        String[][] points = {
                {"com.android.systemui.keyguard.WakefulnessLifecycle", "dispatchStartedGoingToSleep"},
                {"com.android.systemui.keyguard.KeyguardViewMediator", "onStartedGoingToSleep"},
        };
        for (String[] p : points) {
            try {
                interceptMethods(Class.forName(p[0], false, cl), p[1], chain -> {
                    Object result = chain.proceed();
                    Tilt.goingToSleep();
                    return result;
                });
            } catch (Throwable ignored) {
                // not on this ROM: the screen-off broadcast still starts the way back
            }
        }
    }

    // ------------------------------------------------------------------ libxposed API 102 hooks

    /** Framework interface of the loaded module, set in onModuleLoaded. */
    static volatile XposedInterface xposed;

    /** Intercepts one method or constructor: {@code hook(target).intercept(hooker)}. */
    static HookHandle intercept(Executable target, Hooker hooker) {
        XposedInterface x = xposed;
        if (x == null) throw new IllegalStateException("Xposed module is not loaded");
        return x.hook(target)
                .setExceptionMode(XposedInterface.ExceptionMode.PROTECTIVE)
                .intercept(hooker);
    }

    /** Every non-abstract method with this name declared by {@code type}; fails only if none could be hooked. */
    static List<HookHandle> interceptMethods(Class<?> type, String name, Hooker hooker) {
        List<Executable> targets = new ArrayList<>();
        for (Method m : type.getDeclaredMethods()) {
            if (m.getName().equals(name) && !Modifier.isAbstract(m.getModifiers())) targets.add(m);
        }
        return interceptAll(targets, hooker);
    }

    /** Every constructor declared by {@code type}; fails only if none could be hooked. */
    static List<HookHandle> interceptConstructors(Class<?> type, Hooker hooker) {
        List<Executable> targets = new ArrayList<>();
        for (Constructor<?> c : type.getDeclaredConstructors()) targets.add(c);
        return interceptAll(targets, hooker);
    }

    private static List<HookHandle> interceptAll(List<Executable> targets, Hooker hooker) {
        List<HookHandle> out = new ArrayList<>(targets.size());
        Throwable failure = null;
        for (Executable e : targets) {
            try {
                out.add(intercept(e, hooker));
            } catch (Throwable t) {
                failure = t;
                hookError("hook " + e, t);
            }
        }
        if (out.isEmpty() && failure != null) {
            if (failure instanceof Error) throw (Error) failure;
            throw failure instanceof RuntimeException ? (RuntimeException) failure : new RuntimeException(failure);
        }
        return out;
    }

    static void hookError(String what, Throwable t) {
        XposedInterface x = xposed;
        if (x != null) x.log(Log.ERROR, TAG, what, t);
        else Log.e(TAG, what, t);
    }
}
