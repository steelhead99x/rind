package io.github.steelhead99x.rindbench;

import android.os.Handler;
import android.os.Looper;

import org.json.JSONArray;
import org.json.JSONObject;

/**
 * A device runner's lines for an accepted start, as the library resolves it, logged by the process rather
 * than by a view, so they come once per start even when no activity is left to poll (as with "Don't keep
 * activities", or the app sent to the background while the run's thread lists tests):
 *   RINDBENCH_RUN {"selected":true,"start":N,"sections":[...],"sections_missing":[...]}
 * once the library has picked the run's rows (`sections` are the groups that run, `sections_missing` the
 * groups named that had no row), or
 *   RINDBENCH_RUN {"started":false,"start":N,"reason":...,"after_start":true}
 * when it refused the start once it had listed the tests. N is the start's number, as the started line
 * gives it. Everything runs on the main looper.
 */
final class RunReporter {
    private RunReporter() {}

    private static final Handler MAIN = new Handler(Looper.getMainLooper());
    /** The accepted start not yet resolved, or 0 for none. */
    private static long watching;

    private static final Runnable TICK = new Runnable() {
        @Override public void run() {
            if (watching != 0 && !check()) MAIN.postDelayed(this, 500);
        }
    };

    /** Watches start {@code start}, just accepted; an earlier start still watched is resolved first, from the status as it is. */
    static void watch(long start) {
        flush();
        watching = start;
        MAIN.removeCallbacks(TICK);
        MAIN.post(TICK);
    }

    /**
     * Resolves the watched start from the status as it is, before another start can replace it: a start
     * only goes ahead once the last run has ended, so its final status is still there.
     */
    static void flush() {
        if (watching != 0) check();
    }

    /** Logs the watched start's line once its status resolves it; true once it is resolved. */
    private static boolean check() {
        JSONObject s;
        try {
            s = new JSONObject(Native.status());
        } catch (Exception e) {
            return false;
        }
        long n = watching;
        try {
            if (s.optLong("run_start", -1) == n) {
                JSONArray ran = s.optJSONArray("sections_run"), missing = s.optJSONArray("sections_missing");
                android.util.Log.i("RindBench", "RINDBENCH_RUN " + new JSONObject().put("selected", true).put("start", n)
                        .put("sections", ran != null ? ran : new JSONArray())
                        .put("sections_missing", missing != null ? missing : new JSONArray()));
            } else if (s.optString("run_id", "").isEmpty() && s.optLong("refused_start", -1) == n) {
                android.util.Log.w("RindBench", "RINDBENCH_RUN " + new JSONObject().put("started", false).put("start", n)
                        .put("reason", "the native start refused it: " + s.optString("refused_reason")).put("after_start", true));
            } else if (s.optBoolean("running") || s.optLong("acked_start", -1) != n) {
                // Still listing, or the status isn't this start's yet.
                return false;
            }
            // Otherwise it ended without picking rows (as a panic on its thread): nothing more to say.
        } catch (Exception ignored) {}
        watching = 0;
        return true;
    }
}
