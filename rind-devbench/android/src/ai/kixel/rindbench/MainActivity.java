package ai.kixel.rindbench;

import android.app.Activity;
import android.content.Intent;
import android.content.res.Configuration;
import android.os.Build;
import android.os.Bundle;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.WindowInsets;
import android.widget.FrameLayout;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.TextView;

/**
 * Root chrome: a top app bar with the RindBench mark, name, and "by kixel.ai", then
 * Bench / Learn / Contender. Window size class picks the navigation:
 * compact width (under 600dp) gets a bottom navigation bar, medium and
 * expanded width (phone landscape, tablets) get a navigation rail.
 */
public class MainActivity extends Activity {
    static final int WIDE_DP = 600;
    private static final String[] TAB_NAMES = {"Bench", "Learn", "Contender"};
    private static final String[] TAB_ICONS = {"ic_attitude", "ic_help", "ic_groups"};

    private LinearLayout root, appBar, column, navBar, rail;
    private FrameLayout content;
    private final View[] pages = new View[3];
    private final NavItem[] barItems = new NavItem[3], railItems = new NavItem[3];
    private int selected;
    private BenchView bench;
    private ContenderView contender;
    private ImageButton detailsBtn;
    private int insetL, insetT, insetR, insetB;

    @Override protected void onCreate(Bundle b) {
        super.onCreate(b);
        Theme.init(this);
        Theme.styleWindow(getWindow());

        root = new LinearLayout(this);
        root.setBackgroundColor(Theme.surface);
        root.setOnApplyWindowInsetsListener((v, insets) -> {
            if (Build.VERSION.SDK_INT >= 30) {
                android.graphics.Insets s = insets.getInsets(
                        WindowInsets.Type.systemBars() | WindowInsets.Type.displayCutout());
                insetL = s.left; insetT = s.top; insetR = s.right; insetB = s.bottom;
            } else {
                insetL = insets.getSystemWindowInsetLeft();
                insetT = insets.getSystemWindowInsetTop();
                insetR = insets.getSystemWindowInsetRight();
                insetB = insets.getSystemWindowInsetBottom();
            }
            relayout();
            return insets;
        });

        bench = new BenchView(this, getIntent(), b != null);
        LearnView learn = new LearnView(this);
        contender = new ContenderView(this);
        pages[0] = bench; pages[1] = learn; pages[2] = contender;

        appBar = makeAppBar();
        content = new FrameLayout(this);
        for (View p : pages) {
            p.setVisibility(View.GONE);
            content.addView(p, new FrameLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        }
        column = new LinearLayout(this);
        column.setOrientation(LinearLayout.VERTICAL);

        navBar = new LinearLayout(this);
        navBar.setOrientation(LinearLayout.HORIZONTAL);
        navBar.setBackgroundColor(Theme.surfaceContainer);
        rail = new LinearLayout(this);
        rail.setOrientation(LinearLayout.VERTICAL);
        rail.setGravity(Gravity.CENTER_HORIZONTAL);
        rail.setBackgroundColor(Theme.surfaceContainerLow);
        for (int i = 0; i < 3; i++) {
            barItems[i] = new NavItem(i, false);
            LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1);
            navBar.addView(barItems[i].view, lp);
            railItems[i] = new NavItem(i, true);
            LinearLayout.LayoutParams rp = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            rp.bottomMargin = Theme.dpi(this, 12);
            rail.addView(railItems[i].view, rp);
        }
        relayout();
        selectTab(0);
        setContentView(root);
    }

    private LinearLayout makeAppBar() {
        LinearLayout h = new LinearLayout(this);
        h.setOrientation(LinearLayout.HORIZONTAL);
        h.setGravity(Gravity.CENTER_VERTICAL);
        h.setBackgroundColor(Theme.surface);
        h.setMinimumHeight(Theme.dpi(this, 64));
        ImageView mark = Theme.brandImage(this, "rindbench_mark");
        LinearLayout.LayoutParams markSize = new LinearLayout.LayoutParams(
                Theme.dpi(this, 40), Theme.dpi(this, 40));
        markSize.setMarginEnd(Theme.dpi(this, 12));
        h.addView(mark, markSize);
        // The name, with its publisher under it: RindBench, by kixel.ai.
        LinearLayout name = new LinearLayout(this);
        name.setOrientation(LinearLayout.VERTICAL);
        TextView title = Theme.heading(this, "RindBench", Theme.Type.TITLE_LARGE, Theme.onSurface);
        title.setSingleLine(true);
        title.setTypeface(android.graphics.Typeface.create("sans-serif", android.graphics.Typeface.BOLD));
        name.addView(title);
        name.addView(Theme.text(this, "by kixel.ai", Theme.Type.LABEL_MEDIUM, Theme.onSurfaceVariant));
        LinearLayout.LayoutParams tl = new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1);
        tl.topMargin = tl.bottomMargin = Theme.dpi(this, 8);
        h.addView(name, tl);
        detailsBtn = Theme.iconButton(this, "ic_info", "Details");
        detailsBtn.setTooltipText("Details");
        detailsBtn.setOnClickListener(v -> { if (bench != null) bench.openDetails(); });
        h.addView(detailsBtn);
        return h;
    }

    /** M3 navigation bar / rail destination: icon in an active-indicator pill, label below. */
    private final class NavItem {
        final LinearLayout view;
        final FrameLayout pill;
        final ImageView icon;
        final TextView label;
        final int index;

        NavItem(int i, boolean forRail) {
            index = i;
            view = new LinearLayout(MainActivity.this);
            view.setOrientation(LinearLayout.VERTICAL);
            view.setGravity(Gravity.CENTER_HORIZONTAL);
            int top = forRail ? 4 : 12, bottom = forRail ? 4 : 16;
            view.setPadding(Theme.dpi(MainActivity.this, 4), Theme.dpi(MainActivity.this, top),
                    Theme.dpi(MainActivity.this, 4), Theme.dpi(MainActivity.this, bottom));
            view.setMinimumWidth(Theme.dpi(MainActivity.this, forRail ? 80 : 48));
            view.setMinimumHeight(Theme.dpi(MainActivity.this, forRail ? 56 : 80));
            pill = new FrameLayout(MainActivity.this);
            icon = Theme.iconView(MainActivity.this, TAB_ICONS[i], Theme.onSurfaceVariant);
            pill.addView(icon, new FrameLayout.LayoutParams(Theme.dpi(MainActivity.this, 24),
                    Theme.dpi(MainActivity.this, 24), Gravity.CENTER));
            view.addView(pill, new LinearLayout.LayoutParams(Theme.dpi(MainActivity.this, forRail ? 56 : 64),
                    Theme.dpi(MainActivity.this, 32)));
            label = Theme.text(MainActivity.this, TAB_NAMES[i], Theme.Type.LABEL_MEDIUM, Theme.onSurfaceVariant);
            label.setGravity(Gravity.CENTER);
            label.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
            LinearLayout.LayoutParams ll = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            ll.topMargin = Theme.dpi(MainActivity.this, 4);
            view.addView(label, ll);
            view.setBackground(Theme.ripple(Theme.onSurface, null, null));
            view.setFocusable(true);
            view.setClickable(true);
            view.setOnClickListener(v -> selectTab(index));
        }

        void setSelected(boolean on) {
            pill.setBackground(on ? Theme.shape(Theme.secondaryContainer, Theme.dp(MainActivity.this, 8)) : null);
            icon.setImageDrawable(Theme.icon(MainActivity.this, TAB_ICONS[index],
                    on ? Theme.onSecondaryContainer : Theme.onSurfaceVariant));
            label.setTextColor(on ? Theme.onSurface : Theme.onSurfaceVariant);
            view.setSelected(on);
            view.setContentDescription(TAB_NAMES[index] + (on ? ", selected" : "") + ", tab " + (index + 1) + " of 3");
        }
    }

    private void selectTab(int i) {
        selected = i;
        for (int n = 0; n < pages.length; n++) {
            pages[n].setVisibility(n == i ? View.VISIBLE : View.GONE);
            pages[n].setImportantForAccessibility(n == i
                    ? View.IMPORTANT_FOR_ACCESSIBILITY_YES
                    : View.IMPORTANT_FOR_ACCESSIBILITY_NO_HIDE_DESCENDANTS);
        }
        detailsBtn.setVisibility(i == 0 ? View.VISIBLE : View.GONE);
        if (bench != null) bench.setTabShown(i == 0);
        for (int n = 0; n < 3; n++) { barItems[n].setSelected(n == i); railItems[n].setSelected(n == i); }
    }

    static boolean isWide(Activity a) {
        return a.getResources().getConfiguration().screenWidthDp >= WIDE_DP;
    }

    private void relayout() {
        root.removeAllViews();
        column.removeAllViews();
        int s4 = Theme.dpi(this, 16);
        boolean wide = isWide(this);
        appBar.setPaddingRelative(s4 + (wide ? 0 : insetL), insetT, Theme.dpi(this, 4) + insetR, 0);
        column.addView(appBar, new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        column.addView(content, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
        if (wide) {
            root.setOrientation(LinearLayout.HORIZONTAL);
            rail.setPadding(insetL, insetT + Theme.dpi(this, 12), 0, insetB);
            content.setPadding(0, 0, insetR, insetB);
            root.addView(rail, new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT));
            root.addView(column, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));
        } else {
            root.setOrientation(LinearLayout.VERTICAL);
            content.setPadding(insetL, 0, insetR, 0);
            navBar.setPadding(insetL, 0, insetR, insetB);
            root.addView(column, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
            root.addView(navBar, new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        }
        if (bench != null) bench.onChromeRelayout();
    }

    @Override protected void onStart() {
        super.onStart();
        if (bench != null) bench.setOnScreen(true);
    }

    @Override protected void onStop() {
        if (bench != null) bench.setOnScreen(false);
        super.onStop();
    }

    @Override protected void onDestroy() {
        if (bench != null) bench.dispose();
        super.onDestroy();
    }

    @Override public void onConfigurationChanged(Configuration cfg) {
        super.onConfigurationChanged(cfg);
        relayout();
    }

    @Override public void onRequestPermissionsResult(int c, String[] p, int[] g) {
        super.onRequestPermissionsResult(c, p, g);
        if (contender != null) contender.onPermissionResult(c, g);
    }

    @Override protected void onActivityResult(int req, int res, Intent data) {
        super.onActivityResult(req, res, data);
        if (contender != null && req == ContenderView.REQ_SCAN) contender.onScanResult(res, data);
    }

    @Override protected void onNewIntent(Intent i) {
        super.onNewIntent(i);
        setIntent(i);
        // A device runner's launch asks for the Bench tab's run, so it brings that tab up.
        if (Collector.RUNNER && i != null && i.getBooleanExtra("autostart", false)) selectTab(0);
        if (bench != null) bench.newLaunch(i);
    }
}
