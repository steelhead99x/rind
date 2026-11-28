package ai.kixel.rindbench;

import android.content.Context;
import android.view.Gravity;
import android.view.View;
import android.widget.FrameLayout;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;

/** Learn: short plain-language answers as an expandable list. */
final class LearnView extends LinearLayout {
    LearnView(Context c) {
        super(c);
        setOrientation(VERTICAL);
        setBackgroundColor(Theme.surface);
        setContentDescription("Learn page");

        ScrollView scroll = new ScrollView(c);
        FrameLayout centre = new FrameLayout(c);
        LinearLayout root = Theme.readable(c, 720);
        root.setPadding(0, Theme.dpi(c, 8), 0, Theme.dpi(c, 24));

        String[][] items = topics();
        for (int i = 0; i < items.length; i++) {
            if (i > 0) root.addView(Theme.divider(c));
            root.addView(row(c, items[i][0], items[i][1]));
        }

        TextView foot = Theme.text(c, "Published by kixel.ai. Results are community measurements, not official rind benchmarks.",
                Theme.Type.BODY_SMALL, Theme.onSurfaceVariant);
        foot.setPadding(Theme.dpi(c, 16), Theme.dpi(c, 24), Theme.dpi(c, 16), 0);
        root.addView(foot);

        centre.addView(root, new FrameLayout.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT,
                Gravity.CENTER_HORIZONTAL));
        scroll.addView(centre, new ScrollView.LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.WRAP_CONTENT));
        addView(scroll, new LayoutParams(LayoutParams.MATCH_PARENT, LayoutParams.MATCH_PARENT));
    }

    private static View row(Context c, String title, String body) {
        LinearLayout item = new LinearLayout(c);
        item.setOrientation(VERTICAL);
        ImageView chev = Theme.iconView(c, "ic_expand_more", Theme.onSurfaceVariant);
        chev.setLayoutParams(new LayoutParams(Theme.dpi(c, 24), Theme.dpi(c, 24)));
        Theme.Row head = Theme.row(c, title, null, null, chev);
        head.view.setPaddingRelative(Theme.dpi(c, 16), Theme.dpi(c, 8), Theme.dpi(c, 16), Theme.dpi(c, 8));
        head.view.setContentDescription(title + ", collapsed");

        TextView bodyL = Theme.text(c, body, Theme.Type.BODY_MEDIUM, Theme.onSurfaceVariant);
        bodyL.setPadding(Theme.dpi(c, 16), 0, Theme.dpi(c, 56), Theme.dpi(c, 16));
        bodyL.setVisibility(GONE);

        final boolean[] open = {false};
        Theme.clickable(head.view, v -> {
            open[0] = !open[0];
            bodyL.setVisibility(open[0] ? VISIBLE : GONE);
            chev.setImageDrawable(Theme.icon(c, open[0] ? "ic_expand_less" : "ic_expand_more", Theme.onSurfaceVariant));
            v.setContentDescription(title + (open[0] ? ", expanded" : ", collapsed"));
            v.announceForAccessibility(open[0] ? "Expanded" : "Collapsed");
        });
        item.addView(head.view);
        item.addView(bodyL);
        return item;
    }

    static String[][] topics() {
        return new String[][]{
            {"What is this app?",
                "It times how fast this phone runs math that keeps data safe. Nothing runs or leaves your phone until you agree and tap Start."},
            {"What is rind?",
                "rind is a Rust software library that protects data with math like scrambling and signatures. This app times rind next to other libraries doing the same jobs."},
            {"What are the libraries?",
                "They are code packages that do safety math, like rind, ring, and OpenSSL. You can pick which libraries and groups to run on the Bench tab."},
            {"Quick test vs Full test",
                "Quick test runs 1 round (5 tries of 50 ms) for a fast check. Full test runs 3 rounds (10 tries of 100 ms) for steadier numbers, and More groups add extra tests."},
            {"What do the numbers mean?",
                "Numbers show how long one test took in ns, µs, or ms, so smaller is faster. If another library says 2.00x, rind took twice as long; under 1.00x means rind was faster."},
            {"Why does the phone get warm?",
                "The tests make the chip work hard on purpose to measure real speed. Working chips make heat, and you can tap Stop anytime."},
            {"What is shared?",
                "If you agree, Bench sends timings plus your phone model, chip, and OS to the collector, while Contender shares model and chip only. Neither sends your name, serial, ID, or IP."},
            {"How do I read results?",
                "While it runs, the progress bar fills up and shows the current test. When it finishes, tap View results to compare each library side by side."},
            {"How to report a problem",
                "On the Bench tab, tap Details (the info button at the top) to note your commit, phone model, and preset. Send that note to the person who installed this app."},
        };
    }
}
