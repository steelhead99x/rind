package com.kyledouglas.rindbench;

import android.app.Activity;
import android.content.Intent;
import android.content.res.ColorStateList;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.os.Build;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.os.PowerManager;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowManager;
import android.widget.*;
import org.json.JSONArray;
import org.json.JSONObject;
import java.io.*;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.*;

/**
 * RindBench All (v14) for Android: the same screens, flow and words as the
 * iPad app (ios/main.m). A data-driven list of every library x operation this
 * build of rind-devbench can time, picked per run; nothing here names an
 * operation or a library.
 *
 * The collector fills itself in: USB first (127.0.0.1:PORT, live when the
 * computer ran `adb reverse tcp:PORT tcp:PORT`), then the LAN address baked in
 * at build time (Collector.java). Results are always saved on the phone too.
 *
 * adb: am start -n com.kyledouglas.rindbench/.MainActivity [--es host H --ei port P]
 *      [--es libraries "rind,ring"] [--es sections "AEADs"] [--es preset quick|full] [--ez autostart true]
 */
public class MainActivity extends Activity {
    static final int BG = Color.rgb(15, 18, 23), CARD = Color.rgb(28, 31, 38), MUTED = Color.rgb(166, 166, 166), ACCENT = Color.rgb(250, 191, 51);

    private final Handler ui = new Handler(Looper.getMainLooper());
    private LinearLayout root, libBox, secBox;
    private TextView deviceLbl, statusLbl, resultsLbl, collectorLbl;
    private Switch agree;
    private RadioGroup preset;
    private Button startBtn, stopBtn, clearBtn;
    private JSONObject catalog;
    private final Map<String, Switch> libSw = new LinkedHashMap<>(), secSw = new LinkedHashMap<>();
    private boolean polling, ran;
    private String keysDir;
    private String colHost; private int colPort; private String colHow = "looking…";

    private int dp(float v) { return (int) TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, v, getResources().getDisplayMetrics()); }

    private TextView label(String t, float sp, int style, int color) {
        TextView l = new TextView(this); l.setText(t); l.setTextSize(sp); l.setTextColor(color);
        l.setTypeface(Typeface.create(Typeface.DEFAULT, style)); return l;
    }
    private LinearLayout card(View... views) {
        LinearLayout s = new LinearLayout(this); s.setOrientation(LinearLayout.VERTICAL);
        s.setPadding(dp(16), dp(16), dp(16), dp(16));
        GradientDrawable g = new GradientDrawable(); g.setColor(CARD); g.setCornerRadius(dp(14)); s.setBackground(g);
        for (View v : views) addSpaced(s, v);
        return s;
    }
    private void addSpaced(LinearLayout parent, View v) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
        if (parent.getChildCount() > 0) lp.topMargin = dp(parent == root ? 16 : 10);
        parent.addView(v, lp);
    }
    private Switch makeSwitch(boolean on, boolean en) {
        Switch sw = new Switch(this); sw.setChecked(on); sw.setEnabled(en);
        int[][] st = {{android.R.attr.state_checked}, {}};
        sw.setThumbTintList(new ColorStateList(st, new int[]{ACCENT, Color.rgb(220, 220, 220)}));
        sw.setTrackTintList(new ColorStateList(st, new int[]{Color.argb(140, 250, 191, 51), Color.rgb(80, 80, 88)}));
        return sw;
    }
    private LinearLayout switchRow(String title, boolean on, boolean en, Map<String, Switch> dict, String key) {
        Switch sw = makeSwitch(on, en); dict.put(key, sw);
        TextView l = label(title, 16, Typeface.NORMAL, en ? Color.WHITE : MUTED);
        LinearLayout r = new LinearLayout(this); r.setGravity(Gravity.CENTER_VERTICAL);
        r.addView(sw); LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1); lp.leftMargin = dp(12);
        r.addView(l, lp); l.setOnClickListener(v -> { if (sw.isEnabled()) sw.toggle(); });
        return r;
    }
    private Button button(String t, View.OnClickListener a) {
        Button b = new Button(this); b.setText(t); b.setAllCaps(false); b.setTextSize(18); b.setTextColor(Color.BLACK);
        b.setTypeface(Typeface.DEFAULT_BOLD);
        GradientDrawable g = new GradientDrawable(); g.setColor(ACCENT); g.setCornerRadius(dp(10)); b.setBackground(g);
        b.setPadding(dp(20), dp(10), dp(20), dp(10)); b.setOnClickListener(a); return b;
    }
    private void setEnabledLook(Button b, boolean en) { b.setEnabled(en); b.setAlpha(en ? 1f : 0.4f); }

    @Override protected void onCreate(Bundle b) {
        super.onCreate(b);
        getWindow().setStatusBarColor(BG); getWindow().setNavigationBarColor(BG);
        ScrollView sc = new ScrollView(this); sc.setBackgroundColor(BG); sc.setFillViewport(true);
        root = new LinearLayout(this); root.setOrientation(LinearLayout.VERTICAL); root.setPadding(dp(24), dp(24), dp(24), dp(24));
        sc.addView(root); setContentView(sc);

        addSpaced(root, label("RindBench — every library", 30, Typeface.BOLD, Color.WHITE));
        addSpaced(root, label("Times rind and the libraries it is compared with (aws-lc-rs, ring, RustCrypto, graviola, libcrux, verified-garbage) on this phone, with rind-bench's own benchmarks. Pick what to run below. Nothing runs or connects until you agree and press Start test.", 15, Typeface.NORMAL, MUTED));
        deviceLbl = label("Reading the list of tests…", 14, Typeface.BOLD, ACCENT);
        addSpaced(root, card(deviceLbl));
        libBox = card(label("Libraries", 20, Typeface.BOLD, Color.WHITE));
        secBox = card(label("Operations", 20, Typeface.BOLD, Color.WHITE));
        addSpaced(root, libBox); addSpaced(root, secBox);

        preset = new RadioGroup(this); preset.setOrientation(RadioGroup.HORIZONTAL);
        String[] names = {"Quick: 1 round, 5 × 50 ms", "Full: 3 rounds, 10 × 100 ms"};
        for (int i = 0; i < 2; i++) {
            RadioButton rb = new RadioButton(this); rb.setId(100 + i); rb.setText(names[i]); rb.setTextColor(Color.WHITE);
            rb.setButtonTintList(ColorStateList.valueOf(ACCENT)); preset.addView(rb);
        }
        preset.check(100);
        agree = makeSwitch(false, true);
        TextView agreeL = label("I agree to the above: the run keeps the CPU busy (minutes on Quick, longer on Full), warms the phone, and sends only timings and the model, chip, Android version and CPU features to the computer that installed this app. No name, account, serial or location.", 15, Typeface.NORMAL, Color.WHITE);
        LinearLayout agreeRow = new LinearLayout(this); agreeRow.setGravity(Gravity.CENTER_VERTICAL); agreeRow.addView(agree);
        LinearLayout.LayoutParams alp = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1); alp.leftMargin = dp(12);
        agreeRow.addView(agreeL, alp);
        agreeL.setOnClickListener(v -> { if (agree.isEnabled()) agree.toggle(); });
        agree.setOnCheckedChangeListener((v, on) -> agreeChanged());
        collectorLbl = label("Results go to: looking for the computer that installed this app…", 14, Typeface.NORMAL, MUTED);
        startBtn = button("Start test", v -> startTapped());
        stopBtn = button("Stop", v -> stopTapped()); stopBtn.setVisibility(View.GONE);
        clearBtn = button("Clear", v -> clearTapped()); clearBtn.setVisibility(View.GONE);
        setEnabledLook(startBtn, false);
        LinearLayout btns = new LinearLayout(this);
        for (Button bt : new Button[]{startBtn, stopBtn, clearBtn}) {
            LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT); lp.rightMargin = dp(12);
            btns.addView(bt, lp);
        }
        addSpaced(root, card(label("Timing", 20, Typeface.BOLD, Color.WHITE), preset, agreeRow, collectorLbl, btns));
        statusLbl = label("", 15, Typeface.BOLD, Color.WHITE);
        resultsLbl = label("", 12, Typeface.NORMAL, Color.WHITE); resultsLbl.setTypeface(Typeface.MONOSPACE);
        resultsLbl.setHorizontallyScrolling(false);
        addSpaced(root, card(label("Status", 20, Typeface.BOLD, Color.WHITE), statusLbl, resultsLbl));
        addSpaced(root, label("An unofficial community tool, not run or endorsed by the rind maintainers.", 12, Typeface.NORMAL, MUTED));

        Intent it = getIntent();
        if ("full".equals(it.getStringExtra("preset"))) preset.check(101);
        new Thread(() -> {
            String keys = copyKeys();
            String cat = Native.catalog();
            ui.post(() -> loaded(cat, keys));
        }).start();
        findCollector(null);
    }

    // ---- the collector fills itself in: USB (adb reverse) first, then the LAN address baked in at build time.
    private List<String[]> candidates() {
        List<String[]> c = new ArrayList<>();
        Intent it = getIntent();
        if (it.hasExtra("host")) c.add(new String[]{it.getStringExtra("host"), String.valueOf(it.getIntExtra("port", Collector.PORT)), "set by adb"});
        c.add(new String[]{"127.0.0.1", String.valueOf(Collector.PORT), "over USB"});
        c.add(new String[]{Collector.HOST, String.valueOf(Collector.PORT), "over Wi-Fi"});
        return c;
    }
    private void findCollector(Runnable then) {
        new Thread(() -> {
            List<String[]> cs = candidates();
            String[] hit = null;
            for (String[] c : cs) {
                try (Socket s = new Socket()) { s.connect(new InetSocketAddress(c[0], Integer.parseInt(c[1])), 800); hit = c; break; }
                catch (Exception e) { /* next */ }
            }
            final String[] h = hit;
            ui.post(() -> {
                if (h != null) { colHost = h[0]; colPort = Integer.parseInt(h[1]); colHow = h[2];
                    collectorLbl.setText("Results go to: " + colHost + ":" + colPort + " (" + colHow + ", found automatically). They are also saved on this phone.");
                    collectorLbl.setTextColor(Color.WHITE); }
                else { String[] d = cs.get(cs.size() - 1); colHost = d[0]; colPort = Integer.parseInt(d[1]); colHow = "not reachable now";
                    collectorLbl.setText("Results go to: " + colHost + ":" + colPort + " (could not reach it yet; will try again at Start). They are saved on this phone either way.");
                    collectorLbl.setTextColor(MUTED); }
                if (then != null) then.run();
            });
        }).start();
    }

    /** rind-bench's rustls rows read certificates from RIND_BENCH_KEYS_DIR. */
    private String copyKeys() {
        File dst = new File(getFilesDir(), "keys");
        try {
            for (String dir : getAssets().list("keys")) {
                File d = new File(dst, dir); d.mkdirs();
                for (String f : getAssets().list("keys/" + dir)) {
                    try (InputStream in = getAssets().open("keys/" + dir + "/" + f); OutputStream out = new FileOutputStream(new File(d, f))) {
                        byte[] buf = new byte[8192]; int n; while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
                    }
                }
            }
        } catch (IOException e) { /* rustls rows will fail and be reported as errors */ }
        return dst.getAbsolutePath();
    }

    private void loaded(String cat, String keys) {
        keysDir = keys;
        try { catalog = new JSONObject(cat); } catch (Exception e) { catalog = null; }
        if (catalog == null) { deviceLbl.setText("Could not read the list of tests."); return; }
        try {
            JSONObject d = catalog.getJSONObject("device");
            String sha = catalog.optString("rind_commit"); if (sha.length() > 12) sha = sha.substring(0, 12);
            JSONArray rows = catalog.getJSONArray("rows"), libs = catalog.getJSONArray("libraries"), secs = catalog.getJSONArray("sections");
            deviceLbl.setText(d.optString("product") + " · " + d.optString("cpu") + " · " + d.optString("os") + "\nrind " + sha + " · " + rows.length() + " rows · " +
                libs.length() + " libraries · OpenSSL " + (catalog.optBoolean("openssl") ? "built in" : "not in this build"));
            Map<String, Integer> lc = new HashMap<>(), sc = new HashMap<>();
            for (int i = 0; i < rows.length(); i++) { JSONObject r = rows.getJSONObject(i); lc.merge(r.getString("library"), 1, Integer::sum); sc.merge(r.getString("section"), 1, Integer::sum); }
            Set<String> wantLibs = csv(getIntent().getStringExtra("libraries")), wantSecs = csv(getIntent().getStringExtra("sections"));
            for (int i = 0; i < libs.length(); i++) {
                String l = libs.getString(i);
                addSpaced(libBox, switchRow(l + "  (" + lc.getOrDefault(l, 0) + " rows)", wantLibs.isEmpty() || wantLibs.contains(l), true, libSw, l));
            }
            for (int i = 0; i < secs.length(); i++) {
                String s = secs.getString(i); int n = sc.getOrDefault(s, 0);
                boolean on = n > 0 && (wantSecs.isEmpty() ? !s.startsWith("More: ") : wantSecs.contains(s));
                addSpaced(secBox, switchRow(s + "  (" + n + " rows)", on, n > 0, secSw, s));
            }
            statusLbl.setText("Ready. " + catalog.getJSONArray("operations_without_rows").length() + " report operations have no row on this platform.");
        } catch (Exception e) { statusLbl.setText("Could not read the list of tests: " + e); }
        agreeChanged();
        if (getIntent().getBooleanExtra("autostart", false)) { agree.setChecked(true); startTapped(); }
    }

    private static Set<String> csv(String s) {
        Set<String> out = new HashSet<>();
        if (s != null) for (String p : s.split(",")) if (!p.trim().isEmpty()) out.add(p.trim());
        return out;
    }

    private void agreeChanged() { setEnabledLook(startBtn, agree.isChecked() && catalog != null && !polling); }

    private void startTapped() {
        if (!agree.isChecked() || catalog == null || polling) return;
        List<String> libs = new ArrayList<>(), secs = new ArrayList<>();
        for (Map.Entry<String, Switch> e : libSw.entrySet()) if (e.getValue().isChecked()) libs.add(e.getKey());
        for (Map.Entry<String, Switch> e : secSw.entrySet()) if (e.getValue().isChecked()) secs.add(e.getKey());
        if (libs.isEmpty() || secs.isEmpty()) { statusLbl.setText("Pick at least one library and one group of operations."); return; }
        setEnabledLook(startBtn, false);
        statusLbl.setText("Starting. Connecting to the computer that installed this app.");
        // Look again right before the run, so a cable plugged in (or Wi-Fi joined) since launch is used.
        findCollector(() -> begin(libs, secs));
    }

    private void begin(List<String> libs, List<String> secs) {
        try {
            boolean full = preset.getCheckedRadioButtonId() == 101;
            JSONObject cfg = new JSONObject();
            cfg.put("libraries", new JSONArray(libs)); cfg.put("sections", new JSONArray(secs));
            cfg.put("rounds", full ? 3 : 1); cfg.put("samples", full ? 10 : 5); cfg.put("sample_ms", full ? 100 : 50); cfg.put("warm_ms", full ? 300 : 150);
            File out = getExternalFilesDir(null); if (out == null) out = getFilesDir();
            cfg.put("out_dir", out.getAbsolutePath()); cfg.put("label", "android");
            if (colHost != null) { cfg.put("host", colHost); cfg.put("port", colPort); }
            JSONObject env = new JSONObject(); env.put("RIND_BENCH_KEYS_DIR", keysDir); cfg.put("env", env);
            if (Native.start(cfg.toString()) != 0) {
                statusLbl.setText("Could not start: " + new JSONObject(Native.status()).optString("start_error")); agreeChanged(); return;
            }
            getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            startBtn.setVisibility(View.GONE); clearBtn.setVisibility(View.GONE);
            stopBtn.setVisibility(View.VISIBLE); setEnabledLook(stopBtn, true); agree.setEnabled(false);
            polling = true; ran = true; ui.post(this::poll);
        } catch (Exception e) { statusLbl.setText("Could not start: " + e); agreeChanged(); }
    }

    private void stopTapped() { Native.stop(); setEnabledLook(stopBtn, false); statusLbl.setText("Stopping after the current row…"); }

    private void clearTapped() {
        if (polling) return;
        ran = false; agree.setChecked(false); agree.setEnabled(true);
        resultsLbl.setText(""); clearBtn.setVisibility(View.GONE);
        startBtn.setText("Start test"); startBtn.setVisibility(View.VISIBLE); agreeChanged();
        try { statusLbl.setText("Ready. " + catalog.getJSONArray("operations_without_rows").length() + " report operations have no row on this platform."); } catch (Exception e) { statusLbl.setText("Ready."); }
    }

    /** iOS NSProcessInfo.thermalState words, from Android's thermal status. */
    private String thermal() {
        if (Build.VERSION.SDK_INT < 29) return "unknown";
        int t = ((PowerManager) getSystemService(POWER_SERVICE)).getCurrentThermalStatus();
        if (t <= PowerManager.THERMAL_STATUS_NONE) return "nominal";
        if (t <= PowerManager.THERMAL_STATUS_MODERATE) return "fair";
        if (t == PowerManager.THERMAL_STATUS_SEVERE) return "serious";
        return "critical";
    }

    private void poll() {
        if (!polling) return;
        try {
            JSONObject s = new JSONObject(Native.status());
            boolean running = s.optBoolean("running");
            String th = thermal();
            if (running)
                statusLbl.setText(String.format(Locale.US, "Running %d of %d · round %d of %d\n%s\nerrors %d · sent %d lines (%s) · thermal %s",
                    s.optInt("done"), s.optInt("total"), s.optInt("round"), s.optInt("rounds"), s.optString("current", ""), s.optInt("errors"), s.optInt("lines"), s.optString("sink"), th));
            else
                statusLbl.setText(String.format(Locale.US, "%s · %d rows in %.0f s · errors %d · sent %d lines (%s) · thermal %s",
                    s.optBoolean("stopped") ? "Stopped" : "Finished", s.optInt("done"), s.optDouble("elapsed_s", 0), s.optInt("errors"), s.optInt("lines"), s.optString("sink"), th));
            renderResults(s.optJSONObject("results"));
            if (!running) {
                polling = false; getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
                startBtn.setText("Run again"); startBtn.setVisibility(View.VISIBLE); stopBtn.setVisibility(View.GONE);
                clearBtn.setVisibility(View.VISIBLE); setEnabledLook(clearBtn, true); agree.setEnabled(true); agreeChanged();
                return;
            }
        } catch (Exception e) { statusLbl.setText("status: " + e); }
        ui.postDelayed(this::poll, 1000);
    }

    /** Per operation: each library's median and rind's time as a share of it (as the iPad shows). */
    private void renderResults(JSONObject res) throws Exception {
        if (res == null) return;
        Map<String, Map<String, Double>> byOp = new TreeMap<>();
        List<String> errs = new ArrayList<>();
        for (Iterator<String> it = res.keys(); it.hasNext(); ) {
            String id = it.next(); JSONObject r = res.getJSONObject(id);
            if ("error".equals(r.optString("t"))) { errs.add("ERROR " + id + ": " + r.optString("error")); continue; }
            String op = r.isNull("op") ? id : r.optString("op", id);
            String lib = r.isNull("library") ? "?" : r.optString("library", "?");
            byOp.computeIfAbsent(op, k -> new TreeMap<>()).put(lib, r.optDouble("ns"));
        }
        StringBuilder out = new StringBuilder();
        for (Map.Entry<String, Map<String, Double>> e : byOp.entrySet()) {
            Double rind = e.getValue().get("rind");
            out.append(e.getKey().replace("/{lib}", "")).append('\n');
            for (Map.Entry<String, Double> l : e.getValue().entrySet()) {
                out.append(String.format(Locale.US, "   %-16s %12s", l.getKey(), fmt(l.getValue())));
                if (rind != null && !l.getKey().equals("rind")) out.append(String.format(Locale.US, "   rind %.2f× its time", rind / l.getValue()));
                out.append('\n');
            }
        }
        for (String e : errs) out.append(e).append('\n');
        resultsLbl.setText(out.toString());
    }

    private static String fmt(double ns) {
        if (ns >= 1e6) return String.format(Locale.US, "%.3f ms", ns / 1e6);
        if (ns >= 1e3) return String.format(Locale.US, "%.3f µs", ns / 1e3);
        return String.format(Locale.US, "%.1f ns", ns);
    }
}
