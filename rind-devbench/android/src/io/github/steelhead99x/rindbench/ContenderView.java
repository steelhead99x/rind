package io.github.steelhead99x.rindbench;

import android.app.Activity;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.graphics.Typeface;
import android.os.Handler;
import android.os.Looper;
import android.view.Gravity;
import android.view.inputmethod.EditorInfo;
import android.widget.Button;
import android.widget.EditText;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.Switch;
import android.widget.TextView;

/** Contender is off until turned on and agreed. No network before that. Same list and card styling as Bench. */
final class ContenderView extends LinearLayout {
    static final int REQ_CAMERA = 71;
    static final int REQ_SCAN = 72;

    private final Handler ui = new Handler(Looper.getMainLooper());
    private final Activity host;
    private final ContenderClient client;
    private Switch enable, agree;
    private TextView statusTitle, statusBody, endpointsBody;
    private LinearLayout statusCard, joinCard, sessionCard;
    private Theme.Row enableRow, agreeRow;
    private android.widget.ImageView statusIcon;
    private EditText codeField;
    private TextView sessionName, sessionPresenter, rankBody;
    private boolean enabledOn;

    ContenderView(Activity host) {
        super(host);
        this.host = host;
        setOrientation(VERTICAL);
        setBackgroundColor(Theme.surface);
        setContentDescription("Contender page");
        client = new ContenderClient(ContenderClient.DEFAULT_BASE);
        int s2 = Theme.dpi(host, 8), s4 = Theme.dpi(host, 16);

        ScrollView scroll = new ScrollView(host);
        FrameLayout centre = new FrameLayout(host);
        LinearLayout root = Theme.readable(host, 720);
        root.setPadding(0, s2, 0, Theme.dpi(host, 24));

        TextView lead = Theme.text(host, "Join a live talk demo. Nothing connects until both switches are on.",
                Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        lead.setPadding(s4, s2, s4, s2);
        root.addView(lead);

        enable = Theme.switchM3(host, "Turn on Contender");
        enable.setOnCheckedChangeListener((v, on) -> enableChanged());
        enableRow = Theme.row(host, "Turn on Contender", null, null, enable);
        Theme.toggleRow(enableRow.view, enable, "Turn on Contender", Switch.class);
        root.addView(enableRow.view);

        agree = Theme.switchM3(host, "I agree to share timings");
        agree.setOnCheckedChangeListener((v, on) -> agreeChanged());
        agreeRow = Theme.row(host, "I agree to share timings", "Model and chip only. No name, ID, or IP.", null, agree);
        Theme.toggleRow(agreeRow.view, agree, "I agree to share timings. Model and chip only. No name, ID, or IP.", Switch.class);
        root.addView(agreeRow.view);
        agree.setEnabled(false);
        agreeRow.setEnabled(false);

        statusCard = Theme.card(host);
        LinearLayout sRow = new LinearLayout(host);
        sRow.setOrientation(HORIZONTAL);
        statusIcon = Theme.iconView(host, "ic_power", Theme.onSurfaceVariant);
        LinearLayout.LayoutParams il = new LinearLayout.LayoutParams(Theme.dpi(host, 24), Theme.dpi(host, 24));
        il.setMarginEnd(s4);
        sRow.addView(statusIcon, il);
        LinearLayout sCol = new LinearLayout(host);
        sCol.setOrientation(VERTICAL);
        statusTitle = Theme.text(host, "Contender is off", Theme.Type.TITLE_MEDIUM, Theme.onSurface);
        statusTitle.setAccessibilityLiveRegion(ACCESSIBILITY_LIVE_REGION_POLITE);
        statusBody = Theme.text(host, "Nothing connects while this is off.", Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        endpointsBody = Theme.text(host, ContenderClient.neededEndpointsText(), Theme.Type.BODY_SMALL, Theme.onSurfaceVariant);
        endpointsBody.setTypeface(Typeface.MONOSPACE);
        endpointsBody.setVisibility(GONE);
        sCol.addView(statusTitle);
        LinearLayout.LayoutParams bl = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        bl.topMargin = Theme.dpi(host, 4);
        sCol.addView(statusBody, bl);
        LinearLayout.LayoutParams el = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        el.topMargin = s2;
        sCol.addView(endpointsBody, el);
        sRow.addView(sCol, new LinearLayout.LayoutParams(0, LayoutParams.WRAP_CONTENT, 1));
        statusCard.addView(sRow);
        root.addView(statusCard, cardLp());

        TextView joinHead = Theme.heading(host, "Join a session", Theme.Type.TITLE_MEDIUM, Theme.onSurface);
        TextView hint = Theme.text(host, "Type the session code or scan its QR code.", Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        codeField = new EditText(host);
        codeField.setHint("Session code");
        codeField.setContentDescription("Session code");
        Theme.type(codeField, Theme.Type.BODY_LARGE);
        codeField.setTextColor(Theme.onSurface);
        codeField.setHintTextColor(Theme.onSurfaceVariant);
        codeField.setBackground(fieldBg());
        codeField.setPadding(s4, s4, s4, s4);
        codeField.setMinHeight(Theme.dpi(host, 56));
        codeField.setSingleLine(true);
        codeField.setInputType(android.text.InputType.TYPE_CLASS_TEXT | android.text.InputType.TYPE_TEXT_FLAG_NO_SUGGESTIONS);
        codeField.setImeOptions(EditorInfo.IME_ACTION_GO);
        codeField.setOnEditorActionListener((v, a, e) -> { joinTapped(); return true; });

        Button scanBtn = Theme.button(host, "Scan QR code", Theme.Btn.OUTLINED, "ic_camera");
        scanBtn.setOnClickListener(v -> scanTapped());
        Button joinBtn = Theme.button(host, "Join", Theme.Btn.FILLED, null);
        joinBtn.setContentDescription("Join session");
        joinBtn.setOnClickListener(v -> joinTapped());
        LinearLayout joinBtns = new LinearLayout(host);
        joinBtns.setOrientation(HORIZONTAL);
        joinBtns.setGravity(Gravity.END);
        joinBtns.addView(scanBtn);
        LinearLayout.LayoutParams jl = new LinearLayout.LayoutParams(LayoutParams.WRAP_CONTENT, LayoutParams.WRAP_CONTENT);
        jl.setMarginStart(s2);
        joinBtns.addView(joinBtn, jl);

        joinCard = new LinearLayout(host);
        joinCard.setOrientation(VERTICAL);
        joinCard.setPadding(s4, Theme.dpi(host, 24), s4, 0);
        joinCard.addView(joinHead);
        LinearLayout.LayoutParams hl = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        hl.topMargin = Theme.dpi(host, 4);
        hl.bottomMargin = s4;
        joinCard.addView(hint, hl);
        joinCard.addView(codeField);
        LinearLayout.LayoutParams btl = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        btl.topMargin = s2;
        joinCard.addView(joinBtns, btl);
        joinCard.setVisibility(GONE);
        root.addView(joinCard);

        sessionName = Theme.heading(host, "", Theme.Type.TITLE_LARGE, Theme.onSurface);
        sessionPresenter = Theme.text(host, "", Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        rankBody = Theme.text(host, "", Theme.Type.BODY_MEDIUM, Theme.onSurface);
        Button leaveBtn = Theme.button(host, "Leave", Theme.Btn.OUTLINED, null);
        leaveBtn.setContentDescription("Leave session");
        leaveBtn.setOnClickListener(v -> leaveTapped());
        sessionCard = Theme.card(host);
        sessionCard.addView(sessionName);
        LinearLayout.LayoutParams pl = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        pl.topMargin = Theme.dpi(host, 4);
        sessionCard.addView(sessionPresenter, pl);
        LinearLayout.LayoutParams rl = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        rl.topMargin = s2;
        sessionCard.addView(rankBody, rl);
        LinearLayout.LayoutParams ll = new LinearLayout.LayoutParams(LayoutParams.WRAP_CONTENT, LayoutParams.WRAP_CONTENT);
        ll.topMargin = s2;
        ll.gravity = Gravity.END;
        sessionCard.addView(leaveBtn, ll);
        sessionCard.setVisibility(GONE);
        root.addView(sessionCard, cardLp());

        TextView foot = Theme.text(host, "Uses moq-bench.dev on moq.pro. Off by default.",
                Theme.Type.BODY_SMALL, Theme.onSurfaceVariant);
        foot.setPadding(s4, Theme.dpi(host, 24), s4, 0);
        root.addView(foot);

        centre.addView(root, new FrameLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT,
                Gravity.CENTER_HORIZONTAL));
        scroll.addView(centre, new ScrollView.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT));
        addView(scroll, new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));
        refreshGate();
    }

    private LinearLayout.LayoutParams cardLp() {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT);
        lp.leftMargin = lp.rightMargin = Theme.dpi(host, 16);
        lp.topMargin = Theme.dpi(host, 16);
        return lp;
    }

    /** M3 outlined text field container: 1dp outline, 2dp primary when focused. */
    private android.graphics.drawable.Drawable fieldBg() {
        android.graphics.drawable.StateListDrawable s = new android.graphics.drawable.StateListDrawable();
        android.graphics.drawable.GradientDrawable f = Theme.shape(android.graphics.Color.TRANSPARENT, Theme.dp(host, 4));
        f.setStroke(Theme.dpi(host, 2), Theme.primary);
        android.graphics.drawable.GradientDrawable n = Theme.shape(android.graphics.Color.TRANSPARENT, Theme.dp(host, 4));
        n.setStroke(Math.max(1, Theme.dpi(host, 1)), Theme.outline);
        s.addState(new int[]{android.R.attr.state_focused}, f);
        s.addState(new int[]{}, n);
        return s;
    }

    private void enableChanged() {
        if (!enable.isChecked()) {
            agree.setChecked(false);
            leaveTapped();
        }
        refreshGate();
        if (enable.isChecked() && agree.isChecked()) probe();
    }

    private void agreeChanged() {
        refreshGate();
        if (enable.isChecked() && agree.isChecked()) probe();
        else if (enable.isChecked() && !agree.isChecked()) {
            setStatus("Turn on I agree", ASK, "Nothing connects until you agree.", false);
            joinCard.setVisibility(GONE);
        }
    }

    private void refreshGate() {
        agree.setEnabled(enable.isChecked());
        agreeRow.setEnabled(enable.isChecked());
        enabledOn = enable.isChecked() && agree.isChecked();
        // Turning Contender or I agree off drops any probe or lookup still out.
        if (!enabledOn) { probeSeq++; lookupSeq++; lookingUp = false; }
        joinCard.setVisibility((enabledOn && sessionCard.getVisibility() != VISIBLE) ? VISIBLE : GONE);
        if (!enable.isChecked()) {
            setStatus("Contender is off", OFF, "Nothing connects while this is off.", false);
            joinCard.setVisibility(GONE);
            sessionCard.setVisibility(GONE);
        } else if (!agree.isChecked()) {
            setStatus("Turn on I agree", ASK, "Nothing connects until you agree.", false);
            joinCard.setVisibility(GONE);
        }
    }

    private static final int OFF = 0, BUSY = 1, OK = 2, BAD = 3, ASK = 4;

    private void setStatus(String title, int kind, String body, boolean showEndpoints) {
        statusTitle.setText(title);
        statusTitle.setTextColor(kind == BAD ? Theme.error : Theme.onSurface);
        statusBody.setText(body);
        endpointsBody.setVisibility(showEndpoints ? VISIBLE : GONE);
        String icon = kind == OFF ? "ic_power" : kind == BUSY ? "ic_refresh" : kind == OK ? "ic_check_circle"
                : kind == BAD ? "ic_error" : "ic_info";
        int tint = kind == OK ? Theme.primary : kind == BAD ? Theme.error : Theme.onSurfaceVariant;
        statusIcon.setImageDrawable(Theme.icon(host, icon, tint));
    }

    private void probe() {
        setStatus("Checking moq-bench.dev…", BUSY, "Looking for the live session service.", false);
        final int seq = ++probeSeq;
        client.probeHealth(h -> ui.post(() -> {
            if (!enabledOn || seq != probeSeq) return;
            if (h.status == ContenderClient.AVAILABLE) {
                setStatus(h.isLabReferee ? "Lab referee ready" : "Session service ready",
                        OK, client.baseURL, false);
                joinCard.setVisibility(sessionCard.getVisibility() == VISIBLE ? GONE : VISIBLE);
            } else {
                String body = h.status == ContenderClient.UNREACHABLE
                        ? "Could not reach moq-bench.dev."
                        : "moq-bench.dev is not ready for live sessions yet.";
                setStatus("Session service not available yet", BAD, body, true);
                joinCard.setVisibility(VISIBLE);
            }
        }));
    }

    void scanTapped() {
        if (!enabledOn) return;
        if (host.checkSelfPermission(android.Manifest.permission.CAMERA) == PackageManager.PERMISSION_GRANTED) {
            openScanner();
        } else {
            host.requestPermissions(new String[]{android.Manifest.permission.CAMERA}, REQ_CAMERA);
        }
    }

    void onPermissionResult(int code, int[] grant) {
        if (code != REQ_CAMERA) return;
        if (grant != null && grant.length > 0 && grant[0] == PackageManager.PERMISSION_GRANTED) openScanner();
        else cameraDenied();
    }

    void onScanResult(int result, Intent data) {
        if (result != Activity.RESULT_OK || data == null) return;
        String code = data.getStringExtra(QrScannerActivity.EXTRA_CODE);
        if (code != null) {
            codeField.setText(code);
            joinTapped();
        }
    }

    private void openScanner() {
        host.startActivityForResult(new Intent(host, QrScannerActivity.class), REQ_SCAN);
    }

    private void cameraDenied() {
        setStatus("Camera is off", ASK,
                "Type the session code instead, or allow the camera in Settings.", false);
    }

    /** Count health probes and session lookups: a lookup supersedes a probe and earlier lookups, and Leave
     *  supersedes lookups, so only the latest answer is shown. */
    private int probeSeq, lookupSeq;
    /** A lookup is out and its "Looking up session…" status is showing. */
    private boolean lookingUp;

    private void joinTapped() {
        if (!enabledOn) return;
        String code = ContenderClient.codeFromQRString(codeField.getText() == null ? "" : codeField.getText().toString());
        // Lookups can overlap each other or the health probe, a second Join or scan before the first
        // answers: only the newest may change the screen, so an older, slower answer can't replace it.
        // Every Join counts, one with no code too, so a lookup still out can't open a code since cleared.
        final int seq = ++lookupSeq;
        if (code == null || code.isEmpty()) {
            lookingUp = false;
            setStatus("Enter a code", ASK, "Type the session code or scan its QR code.", false);
            return;
        }
        setStatus("Looking up session…", BUSY, "Checking code " + code + ".", false);
        probeSeq++;
        lookingUp = true;
        client.lookupSession(code, (session, error) -> ui.post(() -> {
            if (!enabledOn || seq != lookupSeq) return;
            lookingUp = false;
            if (error != null || session == null) {
                boolean unavail = error != null && error.contains("not available");
                String title = unavail ? "Session service not available yet" : (error != null ? error : "Could not join");
                String body = unavail ? "moq-bench.dev is not ready for live sessions yet." : (error != null ? error : "Could not open that session.");
                setStatus(title, BAD, body, unavail);
                sessionCard.setVisibility(GONE);
                joinCard.setVisibility(VISIBLE);
                return;
            }
            sessionName.setText(session.name);
            sessionPresenter.setText(session.presenter != null && !session.presenter.isEmpty()
                    ? "Presenter: " + session.presenter : "Waiting for presenter.");
            if ("running".equals(session.state))
                rankBody.setText("Running. Live rank appears here.");
            else if ("finished".equals(session.state))
                rankBody.setText("Session finished.");
            else
                rankBody.setText("Waiting for the presenter to start.");
            sessionCard.setVisibility(VISIBLE);
            joinCard.setVisibility(GONE);
            // The lookup only finds the session: "Joined" waits for a join the service confirms,
            // which this app doesn't send yet.
            setStatus("Session found", OK,
                    "Not joined yet: the app only looks a session up for now. Only scrubbed results are ever shared.", false);
        }));
    }

    private void leaveTapped() {
        lookupSeq++; // a lookup still out can't bring the session back; a probe still finishes
        // A lookup cut off here showed "Looking up session…", which nothing else would replace.
        if (lookingUp) { lookingUp = false; if (enabledOn) probe(); }
        sessionCard.setVisibility(GONE);
        sessionName.setText("");
        if (enabledOn) joinCard.setVisibility(VISIBLE);
    }
}
