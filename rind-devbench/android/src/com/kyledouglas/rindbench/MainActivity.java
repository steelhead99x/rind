package com.kyledouglas.rindbench;

import android.app.Activity;
import android.content.Intent;
import android.graphics.Color;
import android.graphics.Typeface;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.text.InputType;
import android.view.View;
import android.view.WindowManager;
import android.widget.*;
import org.json.JSONArray;
import org.json.JSONObject;
import java.io.*;
import java.util.*;

/**
 * RindBench for Android: lists every library x operation this build can time
 * (from rind-bench's own bench files, via rind-devbench), lets the user pick
 * libraries and sections, runs them, shows medians and ratios to rind, and
 * streams JSON lines to an optional collector (host:port) as well as to
 * files in the app's external files dir.
 *
 * adb: am start -n com.kyledouglas.rindbench/.MainActivity --es host H --ei port P
 *      [--es libraries "rind,ring"] [--es sections "AEADs"] [--es preset quick|full] [--ez autostart true]
 */
public class MainActivity extends Activity {
    private final Handler ui = new Handler(Looper.getMainLooper());
    private LinearLayout root, libBox, secBox, resultsBox;
    private TextView statusText, deviceText;
    private CheckBox agree;
    private Button startBtn, stopBtn;
    private EditText hostEdit, portEdit;
    private Spinner preset;
    private JSONObject catalog;
    private final Map<String, CheckBox> libChecks = new LinkedHashMap<>(), secChecks = new LinkedHashMap<>();
    private boolean polling;

    private TextView label(String s, int sp, boolean bold) {
        TextView t = new TextView(this);
        t.setText(s); t.setTextSize(sp); t.setTextColor(Color.WHITE);
        if (bold) t.setTypeface(Typeface.DEFAULT_BOLD);
        t.setPadding(0, 12, 0, 6);
        return t;
    }

    @Override protected void onCreate(Bundle b) {
        super.onCreate(b);
        ScrollView sv = new ScrollView(this);
        root = new LinearLayout(this); root.setOrientation(LinearLayout.VERTICAL); root.setPadding(32, 32, 32, 32);
        sv.addView(root); setContentView(sv);
        sv.setBackgroundColor(Color.rgb(16, 18, 24));
        root.addView(label("RindBench — every library", 24, true));
        root.addView(label("Times rind and the libraries it is compared with (aws-lc-rs, ring, RustCrypto, graviola, libcrux, verified-garbage" +
            ", OpenSSL when built in) on this device, using rind-bench's own benchmarks. Nothing runs until you agree and press Start.", 14, false));
        deviceText = label("Reading this device…", 13, false); root.addView(deviceText);
        root.addView(label("Libraries", 18, true));
        libBox = new LinearLayout(this); libBox.setOrientation(LinearLayout.VERTICAL); root.addView(libBox);
        root.addView(label("Operations", 18, true));
        secBox = new LinearLayout(this); secBox.setOrientation(LinearLayout.VERTICAL); root.addView(secBox);
        root.addView(label("Timing", 18, true));
        preset = new Spinner(this);
        preset.setAdapter(new ArrayAdapter<>(this, android.R.layout.simple_spinner_dropdown_item,
            new String[]{"Quick: 1 round, 5 × 50 ms per row", "Full: 3 rounds, 10 × 100 ms per row"}));
        root.addView(preset);
        root.addView(label("Send results to (optional collector, host and port)", 14, false));
        hostEdit = new EditText(this); hostEdit.setHint("e.g. 192.168.90.75"); hostEdit.setTextColor(Color.WHITE); root.addView(hostEdit);
        portEdit = new EditText(this); portEdit.setHint("port, e.g. 9101"); portEdit.setInputType(InputType.TYPE_CLASS_NUMBER); portEdit.setTextColor(Color.WHITE); root.addView(portEdit);
        agree = new CheckBox(this);
        agree.setText("I agree: this keeps the CPU busy for the whole run (minutes on Quick, longer on Full), warms the phone, and sends only timings and the device model/chip/OS/CPU features — no name, account, or serial.");
        agree.setTextColor(Color.WHITE); root.addView(agree);
        LinearLayout row = new LinearLayout(this);
        startBtn = new Button(this); startBtn.setText("Start test"); stopBtn = new Button(this); stopBtn.setText("Stop"); stopBtn.setEnabled(false);
        row.addView(startBtn); row.addView(stopBtn); root.addView(row);
        statusText = label("Loading the list of tests…", 15, false); root.addView(statusText);
        resultsBox = new LinearLayout(this); resultsBox.setOrientation(LinearLayout.VERTICAL); root.addView(resultsBox);
        startBtn.setEnabled(false);
        agree.setOnCheckedChangeListener((v, on) -> startBtn.setEnabled(on && catalog != null));
        startBtn.setOnClickListener(v -> begin());
        stopBtn.setOnClickListener(v -> { Native.stop(); stopBtn.setEnabled(false); statusText.setText("Stopping after the current row…"); });

        Intent it = getIntent();
        if (it.hasExtra("host")) hostEdit.setText(it.getStringExtra("host"));
        if (it.hasExtra("port")) portEdit.setText(String.valueOf(it.getIntExtra("port", 0)));
        if ("full".equals(it.getStringExtra("preset"))) preset.setSelection(1);

        new Thread(() -> {
            String keys = copyKeys();
            String cat = Native.catalog();
            ui.post(() -> onCatalog(cat, keys));
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

    private String keysDir;
    private void onCatalog(String cat, String keys) {
        keysDir = keys;
        try {
            catalog = new JSONObject(cat);
            JSONObject dev = catalog.getJSONObject("device");
            deviceText.setText(dev.optString("product") + " · " + dev.optString("cpu") + " · " + dev.optString("os") +
                "\nrind " + catalog.optString("rind_commit").substring(0, Math.min(12, catalog.optString("rind_commit").length())) +
                " · " + catalog.getJSONArray("rows").length() + " report rows" + (catalog.optBoolean("openssl") ? " · OpenSSL built in" : " · OpenSSL not in this build"));
            Map<String, Integer> libCount = new TreeMap<>(), secCount = new LinkedHashMap<>();
            JSONArray secs = catalog.getJSONArray("sections");
            for (int i = 0; i < secs.length(); i++) secCount.put(secs.getString(i), 0);
            JSONArray rows = catalog.getJSONArray("rows");
            for (int i = 0; i < rows.length(); i++) {
                JSONObject r = rows.getJSONObject(i);
                libCount.merge(r.getString("library"), 1, Integer::sum);
                secCount.merge(r.getString("section"), 1, Integer::sum);
            }
            Set<String> wantLibs = csv(getIntent().getStringExtra("libraries")), wantSecs = csv(getIntent().getStringExtra("sections"));
            for (Map.Entry<String, Integer> e : libCount.entrySet()) {
                CheckBox c = new CheckBox(this); c.setText(e.getKey() + "  (" + e.getValue() + " rows)"); c.setTextColor(Color.WHITE);
                c.setChecked(wantLibs.isEmpty() || wantLibs.contains(e.getKey())); libBox.addView(c); libChecks.put(e.getKey(), c);
            }
            for (Map.Entry<String, Integer> e : secCount.entrySet()) {
                CheckBox c = new CheckBox(this); c.setText(e.getKey() + "  (" + e.getValue() + " rows)"); c.setTextColor(Color.WHITE);
                c.setEnabled(e.getValue() > 0);
                c.setChecked(e.getValue() > 0 && (wantSecs.isEmpty() ? !e.getKey().startsWith("More: ") : wantSecs.contains(e.getKey()))); secBox.addView(c); secChecks.put(e.getKey(), c);
            }
            JSONArray missing = catalog.getJSONArray("operations_without_rows");
            statusText.setText("Ready. " + missing.length() + " report operations have no row on this platform.");
            startBtn.setEnabled(agree.isChecked());
            if (getIntent().getBooleanExtra("autostart", false)) { agree.setChecked(true); begin(); }
        } catch (Exception e) {
            statusText.setText("Could not read the test list: " + e);
        }
    }

    private static Set<String> csv(String s) {
        Set<String> out = new HashSet<>();
        if (s != null) for (String p : s.split(",")) if (!p.trim().isEmpty()) out.add(p.trim());
        return out;
    }

    private void begin() {
        if (catalog == null || !agree.isChecked()) return;
        try {
            JSONObject cfg = new JSONObject();
            JSONArray libs = new JSONArray(), secs = new JSONArray();
            for (Map.Entry<String, CheckBox> e : libChecks.entrySet()) if (e.getValue().isChecked()) libs.put(e.getKey());
            for (Map.Entry<String, CheckBox> e : secChecks.entrySet()) if (e.getValue().isChecked()) secs.put(e.getKey());
            if (libs.length() == 0 || secs.length() == 0) { statusText.setText("Pick at least one library and one operation group."); return; }
            cfg.put("libraries", libs); cfg.put("sections", secs);
            boolean full = preset.getSelectedItemPosition() == 1;
            cfg.put("rounds", full ? 3 : 1); cfg.put("samples", full ? 10 : 5); cfg.put("sample_ms", full ? 100 : 50); cfg.put("warm_ms", full ? 300 : 150);
            String host = hostEdit.getText().toString().trim(), port = portEdit.getText().toString().trim();
            if (!host.isEmpty() && !port.isEmpty()) { cfg.put("host", host); cfg.put("port", Integer.parseInt(port)); }
            File out = getExternalFilesDir(null); if (out == null) out = getFilesDir();
            cfg.put("out_dir", out.getAbsolutePath());
            cfg.put("label", "android");
            JSONObject env = new JSONObject(); env.put("RIND_BENCH_KEYS_DIR", keysDir); cfg.put("env", env);
            int r = Native.start(cfg.toString());
            if (r != 0) { statusText.setText("Could not start: " + new JSONObject(Native.status()).optString("start_error")); return; }
            getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
            startBtn.setEnabled(false); stopBtn.setEnabled(true); agree.setEnabled(false);
            polling = true; ui.post(this::poll);
        } catch (Exception e) { statusText.setText("Could not start: " + e); }
    }

    private void poll() {
        if (!polling) return;
        try {
            JSONObject s = new JSONObject(Native.status());
            boolean running = s.optBoolean("running");
            int done = s.optInt("done"), total = s.optInt("total");
            String sink = s.optString("sink");
            String head = running
                ? String.format(Locale.US, "Running %d of %d · round %d of %d · %s", done, total, s.optInt("round"), s.optInt("rounds"), s.optString("current"))
                : (s.optBoolean("stopped") ? "Stopped" : "Finished") + String.format(Locale.US, " · %d rows in %.0f s", done, s.optDouble("elapsed_s"));
            head += "\nerrors: " + s.optInt("errors") + " · collector: " + sink + " (" + s.optInt("lines") + " lines)";
            statusText.setText(head);
            renderResults(s.optJSONObject("results"));
            if (!running) { polling = false; stopBtn.setEnabled(false); startBtn.setEnabled(true); agree.setEnabled(true); getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON); return; }
        } catch (Exception e) { statusText.setText("status: " + e); }
        ui.postDelayed(this::poll, 1000);
    }

    /** Per operation: each library's latest median and its ratio to rind (below 1 = rind faster... shown as lib/rind). */
    private void renderResults(JSONObject res) throws Exception {
        if (res == null) return;
        Map<String, Map<String, Double>> byOp = new TreeMap<>();
        Map<String, String> errs = new TreeMap<>();
        for (Iterator<String> it = res.keys(); it.hasNext(); ) {
            String id = it.next(); JSONObject r = res.getJSONObject(id);
            String op = r.optString("op", id), lib = r.optString("library", "?");
            if ("error".equals(r.optString("t"))) { errs.put(id, r.optString("error")); continue; }
            byOp.computeIfAbsent(op, k -> new TreeMap<>()).put(lib, r.optDouble("ns"));
        }
        resultsBox.removeAllViews();
        StringBuilder sb = new StringBuilder();
        for (Map.Entry<String, Map<String, Double>> e : byOp.entrySet()) {
            Double rind = e.getValue().get("rind");
            sb.append(e.getKey().replace("/{lib}", "")).append('\n');
            for (Map.Entry<String, Double> l : e.getValue().entrySet()) {
                sb.append(String.format(Locale.US, "   %-16s %12s", l.getKey(), fmt(l.getValue())));
                if (rind != null && !l.getKey().equals("rind")) sb.append(String.format(Locale.US, "   rind is %.2f× its time", rind / l.getValue()));
                sb.append('\n');
            }
        }
        for (Map.Entry<String, String> e : errs.entrySet()) sb.append("ERROR ").append(e.getKey()).append(": ").append(e.getValue()).append('\n');
        TextView t = label(sb.toString(), 12, false); t.setTypeface(Typeface.MONOSPACE); resultsBox.addView(t);
    }

    private static String fmt(double ns) {
        if (ns >= 1e6) return String.format(Locale.US, "%.3f ms", ns / 1e6);
        if (ns >= 1e3) return String.format(Locale.US, "%.3f µs", ns / 1e3);
        return String.format(Locale.US, "%.1f ns", ns);
    }
}
