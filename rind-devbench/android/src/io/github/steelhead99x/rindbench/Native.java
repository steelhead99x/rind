package io.github.steelhead99x.rindbench;

/** rind-devbench's C core (librind_devbench.so). All JSON. */
final class Native {
    static { System.loadLibrary("rind_devbench"); }
    /** Every row this build can time (lists rows; runs bench setup once, slow: call off the UI thread). */
    static native String catalog();
    static native String device();
    /** 0 = started. */
    static native int start(String configJson);
    static native String status();
    static native void stop();
    /** Before catalog(): rind-bench's rustls rows read RIND_BENCH_KEYS_DIR while listing. */
    static native void setenv(String key, String value);
}
