package io.github.steelhead99x.rindbench;

import android.app.Activity;
import android.content.Context;
import android.content.Intent;
import android.graphics.Typeface;
import android.os.Handler;
import android.os.Looper;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowManager;
import android.widget.Button;
import android.widget.CheckBox;
import android.widget.CompoundButton;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ProgressBar;
import android.widget.ScrollView;
import android.widget.Switch;
import android.widget.TextView;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.File;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.TreeMap;

/**
 * Bench page. Compact width: one scrolling column with consent and Start
 * pinned at the bottom. Medium/expanded width (phone landscape, tablets):
 * two panes, test setup on the left; collector, run status, consent and
 * Start on the right. Panes scroll, so large font sizes wrap instead of
 * truncating, and consent and Start stay pinned and visible.
 */
final class BenchView extends LinearLayout {
    private final Activity host;
    private final Handler ui = new Handler(Looper.getMainLooper());
    private final LinearLayout leftPane, rightPane, colA, colB, footer, testsBlock;
    private final ScrollView scrollA, scrollB;
    private TextView timingHint, statusTitle, statusLbl, resultsTeaser;
    private Theme.Row collector, libsRow, groupsRow, consentRow;
    private LinearLayout statusCard;
    private Button quickBtn, fullBtn;
    private boolean fullPreset;
    private Switch agree;
    private ImageButton shareBtn;
    private Button startBtn, stopBtn, clearBtn, retryBtn, resultsBtn;
    private ProgressBar progress;
    private boolean running, collectorOK, catalogReady;
    private JSONObject catalog;
    private final Map<String, CompoundButton> libSw = new LinkedHashMap<>();
    private final Map<String, CompoundButton> secSw = new LinkedHashMap<>();
    private final List<View> libRows = new ArrayList<>(), groupRows = new ArrayList<>(), moreRows = new ArrayList<>();
    private String resultsText = "";
    private String detailsText = "Loading device and build details...";
    private String keysDir, colHost;
    private int colPort = Collector.PORT;
    private String colHow = "";
    /** The key fixtures, copied and exported once per process; see the constructor. */
    private static String sharedKeysDir;
    /** The native run whose results the person cleared, so a recreated view doesn't bring them back. */
    private static String clearedRun = "";
    /** The late refusal Clear dismissed, so a recreated view doesn't bring it back. */
    private static long clearedRefusal;
    /** The collector a device-runner build was given by intent; a failed probe never forgets it. */
    private String runnerHost;
    private int runnerPort = Collector.PORT;
    private final Runnable poll = this::poll;
    private final boolean restored;
    /** Between the activity's onStart and onStop. */
    private boolean onScreen = true;
    /** A device runner's pending autostart, which leaving the screen or the Bench tab cancels. */
    private Runnable autostart;
    /** A runner launch with `autostart` not yet scheduled: each fresh launch sets it, and scheduling consumes it. */
    private boolean launchPending;
    /**
     * The pending launch's `libraries` and `sections` extras as it named them, null for one it doesn't
     * name: its autostart passes them to the native start unchanged, so a name the picker lacks (as after
     * a list that failed in part) still reaches the library's own check.
     */
    private List<String> launchLibs, launchSecs;
    /** The pending launch left out `host`, so its autostart probes the collector afresh (a blank one keeps it). */
    private boolean launchNoHost;
    /** Whether the Bench tab is the one shown, as MainActivity's tab selection sets it. */
    private boolean tabShown = true;
    /** Set once the list of tests has loaded, so a launch before then waits for it. */
    private boolean loadedOnce;
    /**
     * Launches that arrived while the list loaded, in order, each with whether it sets the whole
     * selection (a runner's) or only what it names; the loaded list then takes them over the first's.
     */
    private final List<Object[]> laterLaunches = new ArrayList<>();

    /**
     * `restored`: the activity is being recreated from saved state, after a
     * configuration change or after Android killed the process. Its launch
     * intent comes back with it, so a device runner's autostart must not fire
     * again; the native run state alone can't tell, since process death
     * clears it.
     */
    BenchView(Activity host, Intent intent, boolean restored) {
        super(host);
        this.host = host;
        this.restored = restored;
        // A restored activity gets its old intent again: only a fresh launch asks for a run.
        launchPending = Collector.RUNNER && !restored && intent != null && intent.getBooleanExtra("autostart", false);
        if (launchPending) setLaunchNames(intent);
        setBackgroundColor(Theme.surface);
        setContentDescription("Bench page");
        int s2 = Theme.dpi(host, 8), s4 = Theme.dpi(host, 16);

        // Collector status: one quiet row, secondary to the run controls.
        retryBtn = Theme.button(host, "Retry", Theme.Btn.TEXT, null);
        retryBtn.setContentDescription("Retry collector connection");
        retryBtn.setOnClickListener(v -> findCollector());
        retryBtn.setVisibility(GONE);
        collector = Theme.row(host, "Checking collector…", null, "ic_cloud_off", retryBtn);
        Theme.type(collector.headline, Theme.Type.BODY_MEDIUM);
        Theme.type(collector.supporting, Theme.Type.BODY_SMALL);
        collector.view.setFocusable(true);

        // Test setup.
        testsBlock = new LinearLayout(host);
        testsBlock.setOrientation(VERTICAL);
        testsBlock.addView(Theme.subheader(host, "Tests"));
        LinearLayout seg = new LinearLayout(host);
        seg.setOrientation(HORIZONTAL);
        seg.setPadding(s4, 0, s4, 0);
        seg.setContentDescription("Test length");
        quickBtn = Theme.segment(host, "Quick test", 0, 2);
        fullBtn = Theme.segment(host, "Full test", 1, 2);
        quickBtn.setOnClickListener(v -> { if (!running) { fullPreset = false; presetChanged(); } });
        fullBtn.setOnClickListener(v -> { if (!running) { fullPreset = true; presetChanged(); } });
        // MATCH_PARENT height keeps both halves the same height when one wraps or carries the check icon.
        seg.addView(quickBtn, new LayoutParams(0, LayoutParams.MATCH_PARENT, 1));
        seg.addView(fullBtn, new LayoutParams(0, LayoutParams.MATCH_PARENT, 1));
        testsBlock.addView(seg);
        timingHint = Theme.text(host, "", Theme.Type.BODY_SMALL, Theme.onSurfaceVariant);
        timingHint.setPadding(s4, Theme.dpi(host, 4), s4, s2);
        testsBlock.addView(timingHint);
        libsRow = Theme.row(host, "Libraries", null, null, chevron());
        Theme.clickable(libsRow.view, v -> openLibraries());
        groupsRow = Theme.row(host, "Groups", null, null, chevron());
        Theme.clickable(groupsRow.view, v -> openGroups());
        testsBlock.addView(libsRow.view);
        testsBlock.addView(groupsRow.view);

        // Run status card.
        statusCard = Theme.card(host);
        statusTitle = Theme.text(host, "Loading tests…", Theme.Type.TITLE_MEDIUM, Theme.primary);
        statusTitle.setTypeface(Typeface.create("sans-serif-condensed", Typeface.BOLD));
        statusTitle.setAccessibilityLiveRegion(ACCESSIBILITY_LIVE_REGION_POLITE);
        statusLbl = Theme.text(host, "", Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        statusLbl.setVisibility(GONE);
        progress = Theme.progress(host);
        progress.setVisibility(GONE);
        progress.setContentDescription("Run progress");
        resultsTeaser = Theme.text(host, "", Theme.Type.BODY_SMALL, Theme.onPrimaryContainer);
        resultsTeaser.setTypeface(Typeface.MONOSPACE);
        resultsTeaser.setBackground(Theme.shape(Theme.primaryContainer, Theme.dp(host, 6)));
        resultsTeaser.setPadding(s2, s2, s2, s2);
        resultsTeaser.setVisibility(GONE);
        resultsBtn = Theme.button(host, "View results", Theme.Btn.TONAL, null);
        resultsBtn.setOnClickListener(v -> openResults());
        clearBtn = Theme.button(host, "Clear", Theme.Btn.TEXT, null);
        clearBtn.setContentDescription("Clear results");
        clearBtn.setOnClickListener(v -> clearTapped());
        resultsBtn.setVisibility(GONE);
        clearBtn.setVisibility(GONE);
        // Header: state and summary on the left, View results on the right so it
        // stays in view on short screens (phone landscape) without scrolling.
        LinearLayout head = new LinearLayout(host);
        head.setOrientation(HORIZONTAL);
        head.setGravity(Gravity.CENTER_VERTICAL);
        LinearLayout headText = new LinearLayout(host);
        headText.setOrientation(VERTICAL);
        headText.addView(statusTitle);
        LayoutParams sl = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        sl.topMargin = Theme.dpi(host, 4);
        headText.addView(statusLbl, sl);
        head.addView(headText, new LayoutParams(0, LayoutParams.WRAP_CONTENT, 1));
        LayoutParams rb = new LayoutParams(LayoutParams.WRAP_CONTENT, LayoutParams.WRAP_CONTENT);
        rb.setMarginStart(s2);
        head.addView(resultsBtn, rb);
        statusCard.addView(head);
        LayoutParams pl = new LayoutParams(LayoutParams.MATCH_PARENT, Theme.dpi(host, 4));
        pl.topMargin = Theme.dpi(host, 12);
        statusCard.addView(progress, pl);
        LayoutParams tl = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        tl.topMargin = Theme.dpi(host, 12);
        statusCard.addView(resultsTeaser, tl);
        LinearLayout acts = new LinearLayout(host);
        acts.setOrientation(HORIZONTAL);
        acts.setGravity(Gravity.CENTER_VERTICAL);
        acts.setGravity(Gravity.END | Gravity.CENTER_VERTICAL);
        acts.addView(clearBtn);
        LayoutParams al = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        al.topMargin = Theme.dpi(host, 4);
        statusCard.addView(acts, al);

        // Footer: consent and Start, always on screen.
        footer = new LinearLayout(host);
        footer.setOrientation(VERTICAL);
        footer.setBackgroundColor(Theme.surface);
        footer.addView(Theme.divider(host));
        shareBtn = Theme.iconButton(host, "ic_info", "What's shared");
        shareBtn.setTooltipText("What's shared");
        shareBtn.setOnClickListener(v -> openShare());
        agree = Theme.switchM3(host, "I agree to share timings");
        agree.setOnCheckedChangeListener((v, on) -> agreeChanged());
        consentRow = Theme.row(host, "I agree to share timings", "Timings and device info only", null, shareBtn, agree);
        Theme.toggleRow(consentRow.view, agree, "I agree to share timings. Timings and device info only.", Switch.class);
        footer.addView(consentRow.view);
        startBtn = Theme.button(host, "Start", Theme.Btn.FILLED, "ic_play");
        startBtn.setEnabled(false);
        startBtn.setOnClickListener(v -> startTapped());
        stopBtn = Theme.button(host, "Stop", Theme.Btn.TONAL, "ic_stop");
        stopBtn.setOnClickListener(v -> stopTapped());
        stopBtn.setVisibility(GONE);
        LayoutParams bl = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        bl.leftMargin = bl.rightMargin = s4;
        bl.bottomMargin = s2;
        footer.addView(startBtn, bl);
        footer.addView(stopBtn, new LayoutParams(bl));

        colA = column();
        colB = column();
        scrollA = scroller(colA);
        scrollB = scroller(colB);
        leftPane = new LinearLayout(host);
        leftPane.setOrientation(VERTICAL);
        leftPane.addView(scrollA, new LayoutParams(LayoutParams.MATCH_PARENT, 0, 1));
        rightPane = new LinearLayout(host);
        rightPane.setOrientation(VERTICAL);
        rightPane.addView(scrollB, new LayoutParams(LayoutParams.MATCH_PARENT, 0, 1));

        onChromeRelayout();
        presetChanged();
        applyIntent(intent);
        findCollector();
        ui.postDelayed(() -> { if (!running && !collectorOK) findCollector(); }, 4000);
        new Thread(() -> {
            // Once per process: a run outlives its activity, and a recreated view must not rewrite the
            // key files that run reads, nor call setenv while its threads read the environment.
            synchronized (BenchView.class) {
                if (sharedKeysDir == null) {
                    sharedKeysDir = copyKeys();
                    Native.setenv("RIND_BENCH_KEYS_DIR", sharedKeysDir);
                }
                keysDir = sharedKeysDir;
            }
            String cat = Native.catalog();
            ui.post(() -> loaded(cat, intent));
        }, "devbench-catalog").start();
    }

    private ImageView chevron() {
        ImageView v = Theme.iconView(host, "ic_chevron_right", Theme.onSurfaceVariant);
        v.setLayoutParams(new LayoutParams(Theme.dpi(host, 24), Theme.dpi(host, 24)));
        return v;
    }

    private LinearLayout column() {
        LinearLayout l = new LinearLayout(host);
        l.setOrientation(VERTICAL);
        l.setPadding(0, 0, 0, Theme.dpi(host, 16));
        return l;
    }

    private ScrollView scroller(View child) {
        ScrollView s = new ScrollView(host);
        s.setFillViewport(true);
        s.addView(child, new ScrollView.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT));
        return s;
    }

    private static void detach(View v) {
        if (v.getParent() instanceof ViewGroup) ((ViewGroup) v.getParent()).removeView(v);
    }

    /** Re-flows the panes for the current window size class. */
    void onChromeRelayout() {
        boolean wide = MainActivity.isWide(host);
        int s4 = Theme.dpi(host, 16);
        removeAllViews();
        colA.removeAllViews();
        colB.removeAllViews();
        detach(collector.view); detach(testsBlock); detach(statusCard); detach(footer);
        LayoutParams foot = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        LayoutParams card = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        card.leftMargin = card.rightMargin = s4;
        card.topMargin = Theme.dpi(host, 8);
        card.bottomMargin = Theme.dpi(host, 8);
        if (wide) {
            setOrientation(HORIZONTAL);
            colA.addView(testsBlock);
            colB.addView(statusCard, card);
            colB.addView(collector.view);
            rightPane.addView(footer, foot);
            addView(leftPane, new LayoutParams(0, LayoutParams.MATCH_PARENT, 1));
            View rule = new View(host);
            rule.setBackgroundColor(Theme.outlineVariant);
            addView(rule, new LayoutParams(Math.max(1, Theme.dpi(host, 1)), LayoutParams.MATCH_PARENT));
            addView(rightPane, new LayoutParams(0, LayoutParams.MATCH_PARENT, 1));
        } else {
            setOrientation(VERTICAL);
            colA.addView(testsBlock);
            colA.addView(statusCard, card);
            colA.addView(collector.view);
            leftPane.addView(footer, foot);
            addView(leftPane, new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));
        }
    }

    void applyIntent(Intent it) {
        if (it == null) return;
        // The launcher is exported, so any app can send these extras. Only a
        // device-runner build (build-apk.sh with DEVICE_RUNNER=1) takes a collector
        // or autostart from them; the other extras only preselect the picker.
        // As the preset buttons, nothing changes while a run is going: its collector was fixed at Start.
        if (running) return;
        // A host that isn't a non-blank string, or a port out of range, leaves the collector as it is.
        String newHost = Collector.RUNNER ? it.getStringExtra("host") : null;
        if (newHost != null) newHost = newHost.trim();
        int newPort = it.getIntExtra("port", Collector.PORT);
        if (newHost != null && !newHost.isEmpty() && newPort > 0 && newPort <= 65535) {
            boolean changed = !newHost.equals(runnerHost) || newPort != runnerPort;
            runnerHost = newHost;
            runnerPort = newPort;
            colHost = runnerHost;
            colPort = runnerPort;
            colHow = "set by adb";
            // After setup, probe the new target; a probe of the old one still out is then ignored.
            if (changed && probeGen > 0) findCollector();
        } else if (!it.hasExtra("host") && runnerHost != null && Collector.RUNNER && it.getBooleanExtra("autostart", false)) {
            // A runner launch without `host` goes to the USB or built-in collector, not the last launch's.
            runnerHost = null;
            runnerPort = Collector.PORT;
            colHost = null;
            colHow = "";
            if (probeGen > 0) findCollector();
        }
        // Each runner launch resolves its own preset, so one without `preset` runs Quick, as in a fresh
        // process, rather than the Full a previous run picked.
        String preset = it.getStringExtra("preset");
        boolean runnerLaunch = Collector.RUNNER && it.getBooleanExtra("autostart", false);
        if ("full".equals(preset)) { fullPreset = true; presetChanged(); }
        else if ("quick".equals(preset) || runnerLaunch) { fullPreset = false; presetChanged(); }
    }

    /** What a status title says about the run: green for ready, running and done; error red for a failure; plain otherwise. */
    private enum Status { OK, NEUTRAL, ERROR }

    /** The one place the status title changes, so its colour always matches what it says. */
    private void setStatus(String text, Status kind) {
        statusTitle.setText(text);
        statusTitle.setTextColor(kind == Status.ERROR ? Theme.error
                : kind == Status.NEUTRAL ? Theme.onSurface : Theme.primary);
    }

    private void setBody(String s) {
        statusLbl.setText(s);
        statusLbl.setVisibility(s == null || s.isEmpty() ? GONE : VISIBLE);
    }

    private void presetChanged() {
        boolean full = fullPreset;
        Theme.selectSegment(quickBtn, !full, !running);
        Theme.selectSegment(fullBtn, full, !running);
        quickBtn.setContentDescription("Quick test" + (!full ? ", selected" : ""));
        fullBtn.setContentDescription("Full test" + (full ? ", selected" : ""));
        timingHint.setText(full ? "3 rounds, 10 × 100 ms, 300 ms warm-up" : "1 round, 5 × 50 ms, 150 ms warm-up");
    }

    private void countsChanged() {
        int lon = 0, gon = 0, mon = 0, mall = 0, gall = 0;
        for (CompoundButton s : libSw.values()) if (s.isChecked()) lon++;
        for (Map.Entry<String, CompoundButton> e : secSw.entrySet()) {
            if (e.getKey().startsWith("More: ")) { mall++; if (e.getValue().isChecked()) mon++; }
            else { gall++; if (e.getValue().isChecked()) gon++; }
        }
        String libs = libSw.isEmpty() ? "" : lon == libSw.size() ? "All " + lon + " selected" : lon + " of " + libSw.size() + " selected";
        String groups = gall == 0 ? "" : gon + " of " + gall + " selected" + (mon > 0 ? ", plus " + mon + " more" : "");
        libsRow.setSupporting(libs);
        groupsRow.setSupporting(groups);
        libsRow.view.setContentDescription("Libraries" + (libs.isEmpty() ? "" : ", " + libs));
        groupsRow.view.setContentDescription("Groups" + (groups.isEmpty() ? "" : ", " + groups));
        agreeChanged();
    }

    private void loaded(String cat, Intent intent) {
        try { catalog = new JSONObject(cat); catalogReady = true; }
        catch (Exception e) {
            catalog = null; catalogReady = false;
            detailsText = "Could not load test list.";
            agreeChanged();
            // A later launch is then scheduled, not left waiting on a list that won't come, and refused.
            laterLaunches.clear();
            loadedOnce = true;
            // A runner's launch waiting on the list gets an outcome too, not silence.
            if (launchPending) {
                launchPending = false;
                notStarted("the list of tests couldn't be read");
            }
            return;
        }
        try {
            JSONObject d = catalog.getJSONObject("device");
            String sha = catalog.optString("rind_commit");
            if (sha.length() > 12) sha = sha.substring(0, 12);
            JSONArray rows = catalog.getJSONArray("rows"), libs = catalog.getJSONArray("libraries"), secs = catalog.getJSONArray("sections");
            detailsText = String.format(Locale.US,
                    "Device: %s\nChip: %s\nSystem: %s\nrind commit: %s\nTests: %d rows across %d libraries\nOpenSSL: %s",
                    d.optString("product"), d.optString("cpu"), d.optString("os"),
                    sha, rows.length(), libs.length(),
                    catalog.optBoolean("openssl") ? "Built in" : "Not in this build");
            Map<String, Integer> lc = new LinkedHashMap<>(), sc = new LinkedHashMap<>();
            for (int i = 0; i < rows.length(); i++) {
                JSONObject r = rows.getJSONObject(i);
                String lib = r.optString("library"), sec = r.optString("section");
                lc.put(lib, lc.getOrDefault(lib, 0) + 1);
                sc.put(sec, sc.getOrDefault(sec, 0) + 1);
            }
            java.util.Set<String> wantLibs = csv(intent == null ? null : intent.getStringExtra("libraries"));
            java.util.Set<String> wantSecs = csv(intent == null ? null : intent.getStringExtra("sections"));
            for (int i = 0; i < libs.length(); i++) {
                String l = libs.getString(i);
                boolean on = wantLibs.isEmpty() || wantLibs.contains(l);
                libRows.add(checkRow(l, lc.getOrDefault(l, 0), on, true, libSw, l));
            }
            for (int i = 0; i < secs.length(); i++) {
                String s = secs.getString(i);
                int n = sc.getOrDefault(s, 0);
                boolean on = n > 0 && (wantSecs.isEmpty() ? !s.startsWith("More: ") : wantSecs.contains(s));
                View row = checkRow(s.startsWith("More: ") ? s.substring(6) : s, n, on, n > 0, secSw, s);
                if (s.startsWith("More: ")) moreRows.add(row); else groupRows.add(row);
            }
            if (!running && resultsText.isEmpty()) {
                setStatus("Ready", Status.OK);
                setBody("");
            }
        } catch (Exception e) {
            setStatus("Could not load tests", Status.ERROR);
        }
        countsChanged();
        agreeChanged();
        JSONObject st = nativeStatus();
        // The launches that came while the list loaded, over the first launch's selection, before
        // anything can start a run from it; none changes the selection of a run that's going.
        if (!st.optBoolean("running"))
            for (Object[] l : laterLaunches) applySelection((Intent) l[0], (Boolean) l[1]);
        laterLaunches.clear();
        loadedOnce = true;
        // The run lives in the native library, past this activity: after a recreation, such as a
        // dark mode switch, pick up a run that's going, or show the results of one that finished.
        if (st.optBoolean("running")) {
            enterRunning();
            scheduleAutostart();
            return;
        }
        String run = st.optString("run_id", "");
        if (!run.isEmpty()) {
            if (!run.equals(clearedRun)) showFinished(st, false);
        } else if (lateRefusal(st) && st.optLong("refused_start") != clearedRefusal) {
            // Refused while no view polled, as across a recreation: show it (RunReporter logs it).
            showLateRefusal(st);
        } else {
            reportLayout("ready");
        }
        // A finished run's results stay up, but a fresh runner launch still starts its own run.
        scheduleAutostart();
    }

    /**
     * A runner launch that reaches the activity already open (onNewIntent): its options apply as
     * applyIntent's do, and its autostart counts as a fresh one.
     */
    void newLaunch(Intent it) {
        applyIntent(it);
        boolean runnerLaunch = Collector.RUNNER && it != null && it.getBooleanExtra("autostart", false);
        // The list's first load reads the first launch's selection; a later one sets it here once the
        // list is up, or, while it loads, once it has (`loaded`), over the first launch's.
        if (loadedOnce) {
            if (!running) applySelection(it, runnerLaunch);
        } else if (it != null && (runnerLaunch || it.hasExtra("libraries") || it.hasExtra("sections"))) {
            // A runner's launch sets the whole selection, so what came before it no longer matters.
            if (runnerLaunch) laterLaunches.clear();
            laterLaunches.add(new Object[]{it, runnerLaunch});
        }
        if (runnerLaunch) {
            // An earlier launch still waiting or queued is replaced: it gets its own outcome first.
            dropLaunch("a later launch replaced it");
            launchPending = true;
            setLaunchNames(it);
            if (loadedOnce) scheduleAutostart();
        }
    }

    /**
     * A later launch's `libraries` and `sections` extras, on the loaded list. A runner's autostart
     * launch sets both, as a first launch does, a missing extra meaning the default (every library,
     * every group but the More ones), so it never runs the last launch's choice; any other launch
     * changes only what it names, leaving the person's own choices.
     */
    private void applySelection(Intent it, boolean whole) {
        if (it == null) return;
        boolean libs = whole || it.hasExtra("libraries"), secs = whole || it.hasExtra("sections");
        java.util.Set<String> wantLibs = csv(it.getStringExtra("libraries"));
        java.util.Set<String> wantSecs = csv(it.getStringExtra("sections"));
        if (libs)
            for (Map.Entry<String, CompoundButton> e : libSw.entrySet())
                e.getValue().setChecked(wantLibs.isEmpty() || wantLibs.contains(e.getKey()));
        if (secs)
            for (Map.Entry<String, CompoundButton> e : secSw.entrySet()) {
                String s = e.getKey();
                e.getValue().setChecked(e.getValue().isEnabled()
                        && (wantSecs.isEmpty() ? !s.startsWith("More: ") : wantSecs.contains(s)));
            }
        if (libs || secs) countsChanged();
    }

    /**
     * Consumes a pending launch's autostart: one run, 3 s later, so a runner can capture the picker
     * first (README). A launch that brings the app back reaches onNewIntent before onStart, so while
     * the app is off screen the launch waits for onStart; onStop drops it. It is dropped, not kept
     * for later, when a run is already going or the Bench tab isn't shown.
     */
    private void scheduleAutostart() {
        if (!launchPending || !onScreen) return;
        launchPending = false;
        cancelAutostart();
        if (running) {
            notStarted("a run is going");
            return;
        }
        if (!tabShown) {
            notStarted("the Bench tab isn't shown");
            return;
        }
        final List<String> libs = launchLibs, secs = launchSecs;
        final boolean noHost = launchNoHost;
        autostart = new Runnable() {
            private boolean probed;

            @Override public void run() {
                // A launch without `host` probes the collector afresh, as it may have changed since the
                // last probe (as `adb reverse` turned on after a run over Wi-Fi), USB first. A blank `host`
                // keeps the collector as it is (README), so it doesn't.
                if (!probed) {
                    probed = true;
                    if (noHost) findCollector();
                }
                // Until the collector probe answers, the run's collector isn't known: wait for it, still queued.
                if (probing) { ui.postDelayed(this, 250); return; }
                autostart = null;
                if (!onScreen || !tabShown || running) {
                    notStarted(running ? "a run is going" : "the app or the Bench tab was left");
                    return;
                }
                // A finished run's results are cleared only now, right before Start, so a launch dropped
                // while it waited leaves them shown; the collector was just probed, so no new probe.
                if (!nativeStatus().optString("run_id", "").isEmpty()) clearResults(false);
                agree.setChecked(true);
                start(libs, secs);
            }
        };
        ui.postDelayed(autostart, 3000);
    }

    /** A start that didn't happen, for a device runner: RINDBENCH_RUN {"started":false,"reason":...}. */
    private static void notStarted(String reason) {
        try {
            android.util.Log.w("RindBench", "RINDBENCH_RUN " + new JSONObject().put("started", false).put("reason", reason));
        } catch (Exception ignored) {}
    }

    /** Whether a finished status is a start the library refused after acknowledging it (on the run's thread). */
    private static boolean lateRefusal(JSONObject s) {
        return s.optString("run_id", "").isEmpty() && s.optLong("refused_start") > 0;
    }

    /** Shows a late refusal as a refused start, not as a finished run. */
    private void showLateRefusal(JSONObject s) {
        String why = s.optString("refused_reason");
        showFinished(s, false);
        progress.setVisibility(GONE);
        setStatus("Could not start", Status.ERROR);
        setBody(why);
        // RunReporter logs it for a device runner, once, whether or not a view sees it.
    }

    private void cancelAutostart() {
        if (autostart != null) {
            ui.removeCallbacks(autostart);
            autostart = null;
        }
    }

    /**
     * One machine-readable line per screen state, for a device runner checking the screen without a person:
     *   RINDBENCH_LAYOUT {"phase":"ready","w":411,"h":914,"wide":false,"folded":true,"fits":true,"clipped":[]}
     * w and h are dp. The library and group pickers open in sheets, so "folded" is true. "clipped" names the
     * run controls, the status card, and the results preview ("score") when one is cut off or out of view;
     * fits is false when any is.
     */
    private void reportLayout(String phase) {
        ui.postDelayed(() -> {
            try {
                List<String> clipped = new ArrayList<>();
                if (!onView(footer) || !whole(footer)) clipped.add("run controls");
                if (!onView(statusCard)) clipped.add("status");
                if (resultsTeaser.getVisibility() == VISIBLE && !onView(resultsTeaser)) clipped.add("score");
                float d = getResources().getDisplayMetrics().density;
                View root = host.getWindow().getDecorView();
                JSONObject o = new JSONObject();
                o.put("phase", phase);
                o.put("w", Math.round(root.getWidth() / d));
                o.put("h", Math.round(root.getHeight() / d));
                o.put("wide", MainActivity.isWide(host));
                o.put("folded", true);
                o.put("fits", clipped.isEmpty());
                o.put("clipped", new JSONArray(clipped));
                android.util.Log.i("RindBench", "RINDBENCH_LAYOUT " + o);
            } catch (Exception e) {
                android.util.Log.w("RindBench", "RINDBENCH_LAYOUT failed: " + e);
            }
        }, 600);
    }

    /** Whether all of v is on screen: shown, laid out, and not clipped by a scrolling pane or the window. */
    private static boolean onView(View v) {
        android.graphics.Rect r = new android.graphics.Rect();
        return v.isShown() && v.getWidth() > 0 && v.getGlobalVisibleRect(r)
                && r.width() >= v.getWidth() && r.height() >= v.getHeight();
    }

    /** Whether v got all the height it asks for at its width. Re-lays out afterwards, since measure() overwrites its size. */
    private static boolean whole(View v) {
        if (v.getWidth() == 0) return false;
        v.measure(MeasureSpec.makeMeasureSpec(v.getWidth(), MeasureSpec.EXACTLY),
                MeasureSpec.makeMeasureSpec(0, MeasureSpec.UNSPECIFIED));
        boolean ok = v.getMeasuredHeight() <= v.getHeight() + 1;
        v.requestLayout();
        return ok;
    }

    private static java.util.Set<String> csv(String s) {
        java.util.Set<String> out = new java.util.LinkedHashSet<>();
        if (s != null) for (String p : s.split(",")) if (!p.trim().isEmpty()) out.add(p.trim());
        return out;
    }

    /** Multi-select list item for the Libraries and Groups sheets. */
    private View checkRow(String title, int count, boolean on, boolean en, Map<String, CompoundButton> dict, String key) {
        LinearLayout row = new LinearLayout(host);
        row.setOrientation(HORIZONTAL);
        row.setGravity(Gravity.CENTER_VERTICAL);
        row.setMinimumHeight(Theme.dpi(host, 56));
        row.setPaddingRelative(Theme.dpi(host, 12), Theme.dpi(host, 4), Theme.dpi(host, 24), Theme.dpi(host, 4));
        CheckBox cb = Theme.checkBox(host);
        cb.setChecked(on);
        cb.setEnabled(en);
        cb.setOnCheckedChangeListener((v, c) -> countsChanged());
        dict.put(key, cb);
        TextView l = Theme.text(host, title, Theme.Type.BODY_LARGE, Theme.onSurface);
        TextView n = Theme.text(host, String.valueOf(count), Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        LayoutParams lp = new LayoutParams(0, LayoutParams.WRAP_CONTENT, 1);
        lp.setMarginStart(Theme.dpi(host, 4));
        lp.setMarginEnd(Theme.dpi(host, 16));
        row.addView(cb);
        row.addView(l, lp);
        row.addView(n);
        String noun = count == 1 ? " test" : " tests";
        Theme.toggleRow(row, cb, title + ", " + count + noun, CheckBox.class);
        row.setEnabled(en);
        if (!en) { l.setAlpha(0.38f); n.setAlpha(0.38f); }
        return row;
    }

    private java.util.List<String[]> candidates() {
        java.util.List<String[]> c = new ArrayList<>();
        // A runner's collector, set by intent, is the only candidate: when it's down, results
        // save on the phone and go nowhere else, rather than to whichever collector answers.
        if (runnerHost != null && !runnerHost.isEmpty()) {
            c.add(new String[]{runnerHost, String.valueOf(runnerPort), "set by adb"});
            return c;
        }
        c.add(new String[]{"127.0.0.1", String.valueOf(Collector.PORT), "over USB"});
        if (Collector.HOST != null && !Collector.HOST.isEmpty())
            c.add(new String[]{Collector.HOST, String.valueOf(Collector.PORT), "over Wi-Fi"});
        return c;
    }

    /** Counts probes, so a slow one that finishes after a newer one started can't overwrite its answer. */
    private int probeGen;

    /** The latest collector probe hasn't answered yet. */
    private boolean probing;

    private void findCollector() {
        // The targets as of now: an intent or Retry since may have changed them.
        final int gen = ++probeGen;
        probing = true;
        final List<String[]> targets = candidates();
        new Thread(() -> {
            String[] hit = null;
            for (String[] c : targets) {
                try (Socket s = new Socket()) {
                    s.connect(new InetSocketAddress(c[0], Integer.parseInt(c[1])), 2000);
                    hit = c;
                    break;
                } catch (Exception ignored) {}
            }
            final String[] h = hit;
            ui.post(() -> { if (gen == probeGen) { probing = false; applyCollector(h); } });
        }, "collector-probe").start();
    }

    private void showCollector(String icon, int tint, String title, String sub, boolean retry) {
        collector.leading.setImageDrawable(Theme.icon(host, icon, tint));
        collector.headline.setText(title);
        collector.setSupporting(sub);
        retryBtn.setVisibility(retry ? VISIBLE : GONE);
        collector.view.setContentDescription(title + (sub.isEmpty() ? "" : ". " + sub));
    }

    private void applyCollector(String[] h) {
        if (h != null) {
            colHost = h[0]; colPort = Integer.parseInt(h[1]); colHow = h[2];
            collectorOK = true;
            showCollector("ic_cloud_done", Theme.primary, "Collector connected",
                    colHost + ":" + colPort + ("over USB".equals(colHow) ? " over USB" : ""), false);
        } else {
            collectorOK = false;
            // A runner's own collector stays the target while it's down; otherwise the last place tried.
            List<String[]> all = candidates();
            String[] d = runnerHost != null && !runnerHost.isEmpty() ? all.get(0) : all.get(all.size() - 1);
            colHost = d[0]; colPort = Integer.parseInt(d[1]); colHow = "not reachable now";
            showCollector("ic_cloud_off", Theme.onSurfaceVariant, "Collector not connected",
                    "Results save on this phone", true);
        }
    }

    private void updateCollectorFromSink(String sink) {
        if (sink == null || sink.isEmpty()) return;
        if ("connected".equals(sink)) {
            collectorOK = true;
            showCollector("ic_cloud_upload", Theme.primary, "Sending to collector",
                    "Results also save on this phone", false);
        } else if ("unreachable".equals(sink)) {
            collectorOK = false;
            showCollector("ic_cloud_off", Theme.onSurfaceVariant, "Collector not connected",
                    "Results save on this phone", true);
        }
    }

    private void agreeChanged() {
        boolean on = agree.isChecked() && catalogReady && !running;
        startBtn.setEnabled(on);
        if (!catalogReady) startBtn.setContentDescription("Start, loading tests");
        else if (!agree.isChecked()) startBtn.setContentDescription("Start, turn on I agree to share timings first");
        else startBtn.setContentDescription("Start");
    }

    private void setControlsEnabled(boolean en) {
        Theme.selectSegment(quickBtn, !fullPreset, en);
        Theme.selectSegment(fullBtn, fullPreset, en);
        libsRow.setEnabled(en);
        groupsRow.setEnabled(en);
    }

    private void setAgreeEnabled(boolean en) {
        agree.setEnabled(en);
        consentRow.setEnabled(en);
        shareBtn.setEnabled(true);
        shareBtn.setAlpha(1f);
    }

    /** Keeps a runner launch's `libraries` and `sections` extras for its autostart, as named. */
    private void setLaunchNames(Intent it) {
        launchNoHost = !it.hasExtra("host");
        launchLibs = it.hasExtra("libraries") ? new ArrayList<>(csv(it.getStringExtra("libraries"))) : null;
        launchSecs = it.hasExtra("sections") ? new ArrayList<>(csv(it.getStringExtra("sections"))) : null;
    }

    private void startTapped() {
        start(null, null);
    }

    /**
     * Starts a run of the picker's selection; an autostart passes the names its launch gave in
     * {@code wantLibs} and {@code wantSecs} (null where it gave none), which go to the native start as
     * given, in place of the picker's, so the library judges names the picker doesn't list.
     */
    private void start(List<String> wantLibs, List<String> wantSecs) {
        // Any start, the person's or the runner's own, takes the place of a queued autostart. The
        // autostart's own start clears it first, so one still queued here is replaced by hand: say so.
        if (autostart != null) notStarted("a start by hand took its place");
        cancelAutostart();
        if (running) return;
        if (!agree.isChecked() || !catalogReady) {
            notStarted(!catalogReady ? "the list of tests hasn't loaded" : "consent isn't given");
            return;
        }
        List<String> libs = new ArrayList<>(), secs = new ArrayList<>();
        for (Map.Entry<String, CompoundButton> e : libSw.entrySet()) if (e.getValue().isChecked()) libs.add(e.getKey());
        for (Map.Entry<String, CompoundButton> e : secSw.entrySet()) if (e.getValue().isChecked()) secs.add(e.getKey());
        if (wantLibs != null && !wantLibs.isEmpty()) libs = wantLibs;
        if (wantSecs != null && !wantSecs.isEmpty()) secs = wantSecs;
        if (libs.isEmpty() || secs.isEmpty()) {
            setStatus("Nothing picked", Status.NEUTRAL);
            setBody("Turn on at least one library and group.");
            // A runner launch whose names matched nothing ends here: say so, as a refused native start does.
            notStarted(libs.isEmpty() ? "no library is picked" : "no group is picked");
            return;
        }
        try {
            boolean full = fullPreset;
            JSONObject cfg = new JSONObject();
            cfg.put("libraries", new JSONArray(libs));
            cfg.put("sections", new JSONArray(secs));
            cfg.put("rounds", full ? 3 : 1);
            cfg.put("samples", full ? 10 : 5);
            cfg.put("sample_ms", full ? 100 : 50);
            cfg.put("warm_ms", full ? 300 : 150);
            File out = host.getExternalFilesDir(null);
            if (out == null) out = host.getFilesDir();
            cfg.put("out_dir", out.getAbsolutePath());
            cfg.put("label", "android");
            if (colHost == null || colHost.isEmpty()) { String[] d = candidates().get(0); colHost = d[0]; colPort = Integer.parseInt(d[1]); }
            cfg.put("host", colHost); cfg.put("port", colPort);
            JSONObject env = new JSONObject();
            env.put("RIND_BENCH_KEYS_DIR", keysDir);
            cfg.put("env", env);
            // The last start's line, if its status hasn't been read yet, before this start replaces that status.
            RunReporter.flush();
            if (Native.start(cfg.toString()) != 0) {
                String why = new JSONObject(Native.status()).optString("start_error");
                notStarted("the native start refused it: " + why);
                setStatus("Could not start", Status.ERROR);
                setBody(why);
                return;
            }
            // What the run takes, for a device runner checking a launch's selection without a person:
            //   RINDBENCH_RUN {"started":true,"start":N,"preset":"quick","libraries":[...],"sections":[...],"host":...,"port":...}
            // logged as the start is accepted, with the libraries and groups asked for; RunReporter then logs
            // the groups that run, or a refusal once listed, under the same start number N.
            long startNo = nativeStatus().optLong("acked_start", 0);
            JSONObject run = new JSONObject();
            run.put("started", true);
            run.put("start", startNo);
            run.put("preset", full ? "full" : "quick");
            run.put("libraries", cfg.get("libraries"));
            run.put("sections", cfg.get("sections"));
            run.put("host", colHost);
            run.put("port", colPort);
            android.util.Log.i("RindBench", "RINDBENCH_RUN " + run);
            if (startNo > 0) RunReporter.watch(startNo);
        } catch (Exception e) {
            setStatus("Could not start", Status.ERROR);
            setBody(String.valueOf(e));
            return;
        }
        Theme.haptic(startBtn, true);
        enterRunning();
    }

    /** Shows a run as going and polls it: one this view started, or one already going when it was made. */
    private void enterRunning() {
        host.getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        startBtn.setVisibility(GONE);
        clearBtn.setVisibility(GONE);
        stopBtn.setVisibility(VISIBLE);
        stopBtn.setEnabled(true);
        setAgreeEnabled(false);
        running = true;
        setControlsEnabled(false);
        resultsTeaser.setVisibility(GONE);
        resultsBtn.setVisibility(GONE);
        progress.setMax(1);
        progress.setProgress(0);
        progress.setVisibility(VISIBLE);
        setStatus("Starting", Status.OK);
        setBody("Warming up…");
        findCollector();
        agreeChanged();
        ui.post(poll);
        reportLayout("run");
    }

    private void stopTapped() {
        Theme.haptic(stopBtn, false);
        Native.stop();
        stopBtn.setEnabled(false);
        setStatus("Stopping", Status.NEUTRAL);
        setBody("Stops after the current test.");
    }

    private void clearTapped() {
        clearResults(true);
    }

    /** Clears a finished run's results, as Clear does; {@code probe} also probes the collector again. */
    private void clearResults(boolean probe) {
        if (running) return;
        JSONObject cleared = nativeStatus();
        clearedRun = cleared.optString("run_id", "");
        clearedRefusal = cleared.optLong("refused_start");
        agree.setChecked(false);
        setAgreeEnabled(true);
        resultsTeaser.setText("");
        resultsTeaser.setVisibility(GONE);
        resultsText = "";
        resultsBtn.setVisibility(GONE);
        clearBtn.setVisibility(GONE);
        startBtn.setVisibility(VISIBLE);
        stopBtn.setVisibility(GONE);
        setControlsEnabled(true);
        progress.setProgress(0);
        progress.setVisibility(GONE);
        setStatus("Ready", Status.OK);
        setBody("");
        agreeChanged();
        if (probe) findCollector();
    }

    private static JSONObject nativeStatus() {
        try {
            return new JSONObject(Native.status());
        } catch (Exception e) {
            return new JSONObject();
        }
    }

    /** The activity's onStart and onStop. */
    void setOnScreen(boolean on) {
        onScreen = on;
        if (!on) {
            // Leaving the app drops a launch's autostart, queued or still waiting, and says so.
            dropLaunch("the app was left before the run started");
        } else if (loadedOnce) {
            scheduleAutostart();
        }
    }

    /** MainActivity's tab selection: leaving the Bench tab cancels a queued autostart. */
    void setTabShown(boolean shown) {
        tabShown = shown;
        if (!shown) {
            // As leaving the app does: a launch still waiting for the list is dropped too, not revived on return.
            dropLaunch("the Bench tab was left before the run started");
        }
    }

    /** Drops a launch that is waiting or queued, logging its outcome; nothing when there is none. */
    private void dropLaunch(String reason) {
        boolean had = launchPending || autostart != null;
        launchPending = false;
        cancelAutostart();
        if (had) notStarted(reason);
    }

    /** Stops polling, for the activity's onDestroy: a recreated activity's new view picks the run up. */
    void dispose() {
        ui.removeCallbacksAndMessages(null);
    }

    private boolean isWarm() {
        if (android.os.Build.VERSION.SDK_INT < 29) return false;
        int t = ((android.os.PowerManager) host.getSystemService(Context.POWER_SERVICE)).getCurrentThermalStatus();
        return t >= android.os.PowerManager.THERMAL_STATUS_SEVERE;
    }

    private void poll() {
        if (!running) return;
        try {
            JSONObject s = new JSONObject(Native.status());
            boolean still = s.optBoolean("running");
            running = still;
            int done = s.optInt("done"), total = Math.max(1, s.optInt("total"));
            progress.setMax(total);
            progress.setProgress(still ? done : (done > 0 ? total : 0));
            progress.setContentDescription("Run progress, " + (still ? done : (done > 0 ? total : 0)) + " of " + total);
            updateCollectorFromSink(s.optString("sink"));
            if (still) {
                setStatus("Running " + s.optInt("round") + " of " + s.optInt("rounds"), Status.OK);
                String cur = s.optString("current", "");
                String warm = isWarm() ? " (warm)" : "";
                setBody(done + " of " + total + (cur.isEmpty() ? "" : " · " + cur) + warm);
            } else if (lateRefusal(s)) {
                showLateRefusal(s);
                return;
            } else {
                showFinished(s, true);
                return;
            }
            renderResults(s.optJSONObject("results"));
        } catch (Exception e) {
            setBody("Status error.");
        }
        ui.postDelayed(poll, 1000);
    }

    /** A finished run's state: as poll sees it end, or as a recreated view finds it. */
    private void showFinished(JSONObject s, boolean justEnded) {
        running = false;
        boolean stopped = s.optBoolean("stopped");
        if (justEnded) Theme.haptic(statusCard, !stopped);
        setStatus(stopped ? "Stopped" : "Done", stopped ? Status.NEUTRAL : Status.OK);
        int errs = s.optInt("errors");
        String errTxt = errs > 0 ? " (" + errs + " errors)" : "";
        setBody(String.format(Locale.US, "%d tests in %.0f s%s",
                s.optInt("done"), s.optDouble("elapsed_s", 0), errTxt));
        int total = Math.max(1, s.optInt("total"));
        progress.setMax(total);
        progress.setProgress(s.optInt("done") > 0 ? total : 0);
        progress.setVisibility(VISIBLE);
        try {
            renderResults(s.optJSONObject("results"));
        } catch (Exception e) {
            setBody("Status error.");
        }
        host.getWindow().clearFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        startBtn.setVisibility(VISIBLE);
        stopBtn.setVisibility(GONE);
        clearBtn.setVisibility(VISIBLE);
        setAgreeEnabled(true);
        setControlsEnabled(true);
        agreeChanged();
        reportLayout("done");
    }

    private void renderResults(JSONObject res) throws Exception {
        if (res == null) return;
        Map<String, Map<String, Double>> byOp = new TreeMap<>();
        List<String> errs = new ArrayList<>();
        for (Iterator<String> it = res.keys(); it.hasNext(); ) {
            String id = it.next();
            JSONObject r = res.getJSONObject(id);
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
                if (rind != null && !"rind".equals(l.getKey()))
                    out.append(String.format(Locale.US, "   rind %.2fx", rind / l.getValue()));
                out.append('\n');
            }
        }
        for (String e : errs) out.append(e).append('\n');
        resultsText = out.toString();
        if (!byOp.isEmpty()) {
            StringBuilder tease = new StringBuilder();
            int show = Math.min(byOp.size(), 4), i = 0;
            for (Map.Entry<String, Map<String, Double>> e : byOp.entrySet()) {
                if (i++ >= show) break;
                Double rind = e.getValue().get("rind");
                tease.append(e.getKey().replace("/{lib}", "")).append("  ").append(rind == null ? "-" : fmt(rind)).append('\n');
            }
            if (byOp.size() > 4) tease.append("+").append(byOp.size() - 4).append(" more");
            resultsTeaser.setText(tease.toString().trim());
            resultsTeaser.setVisibility(VISIBLE);
            resultsBtn.setVisibility(VISIBLE);
        }
    }

    private static String fmt(double ns) {
        if (ns >= 1e6) return String.format(Locale.US, "%.3f ms", ns / 1e6);
        if (ns >= 1e3) return String.format(Locale.US, "%.3f µs", ns / 1e3);
        return String.format(Locale.US, "%.1f ns", ns);
    }

    private String copyKeys() {
        File dst = new File(host.getFilesDir(), "keys");
        try {
            String[] dirs = host.getAssets().list("keys");
            if (dirs == null) return dst.getAbsolutePath();
            for (String dir : dirs) {
                File d = new File(dst, dir);
                d.mkdirs();
                String[] files = host.getAssets().list("keys/" + dir);
                if (files == null) continue;
                for (String f : files) {
                    try (java.io.InputStream in = host.getAssets().open("keys/" + dir + "/" + f);
                         java.io.OutputStream out = new java.io.FileOutputStream(new File(d, f))) {
                        byte[] buf = new byte[8192];
                        int n;
                        while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
                    }
                }
            }
        } catch (Exception ignored) {}
        return dst.getAbsolutePath();
    }

    private LinearLayout listSection(String title, List<View> rows, String empty) {
        LinearLayout s = new LinearLayout(host);
        s.setOrientation(VERTICAL);
        if (title != null) {
            TextView h = Theme.subheader(host, title);
            h.setPaddingRelative(Theme.dpi(host, 24), Theme.dpi(host, 16), Theme.dpi(host, 24), Theme.dpi(host, 4));
            s.addView(h);
        }
        if (rows.isEmpty()) s.addView(Sheet.body(host, empty, false));
        else for (View r : rows) { detach(r); s.addView(r); }
        return s;
    }

    private void openLibraries() { Sheet.show(host, "Libraries", listSection(null, libRows, "No libraries found.")); }

    private void openGroups() {
        LinearLayout s = new LinearLayout(host);
        s.setOrientation(VERTICAL);
        s.addView(listSection("Default groups", groupRows, "None."));
        s.addView(listSection("More groups, off by default", moreRows, "None."));
        Sheet.show(host, "Groups", s);
    }

    private void openShare() {
        Sheet.show(host, "What's shared", Sheet.body(host,
                "When you agree and tap Start, this app runs CPU tests that warm your phone.\n\n"
                + "It sends only timings plus your phone model, chip, system version, and CPU features to the collector. "
                + "It never sends your name, account, serial number, or location.\n\n"
                + "Results always save on this phone too, and you can tap Stop anytime.", false));
    }

    void openDetails() {
        String col = (colHost == null || colHost.isEmpty()) ? "None" : (colHost + ":" + colPort + " (" + colHow + ")");
        LinearLayout panel = new LinearLayout(host);
        panel.setOrientation(VERTICAL);
        LinearLayout publisher = new LinearLayout(host);
        publisher.setGravity(Gravity.CENTER_VERTICAL);
        int inset = Theme.dpi(host, 8);
        ImageView mark = Theme.brandImage(host, "kixel_mark");
        LayoutParams logo = new LayoutParams(Theme.dpi(host, 30), Theme.dpi(host, 30));
        logo.setMarginEnd(inset);
        publisher.addView(mark, logo);
        publisher.addView(Theme.text(host, "Kixel AI", Theme.Type.TITLE_SMALL, Theme.onSurface));
        LayoutParams publisherSize = new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        publisherSize.setMarginStart(Theme.dpi(host, 24));
        publisherSize.bottomMargin = inset;
        panel.addView(publisher, publisherSize);
        panel.addView(Sheet.body(host, detailsText + "\nCollector: " + col, true));
        Sheet.show(host, "Details", panel);
    }

    private void openResults() {
        // Results are a table: keep columns aligned and scroll sideways instead of wrapping.
        TextView tv = Sheet.body(host, resultsText.isEmpty() ? "No results yet." : resultsText, true);
        Theme.type(tv, Theme.Type.BODY_SMALL);
        tv.setTypeface(Typeface.MONOSPACE);
        tv.setHorizontallyScrolling(false);
        tv.setContentDescription("Results");
        android.widget.HorizontalScrollView h = new android.widget.HorizontalScrollView(host);
        h.addView(tv, new android.widget.HorizontalScrollView.LayoutParams(LayoutParams.WRAP_CONTENT, LayoutParams.WRAP_CONTENT));
        Sheet.show(host, "Results", h);
    }
}
