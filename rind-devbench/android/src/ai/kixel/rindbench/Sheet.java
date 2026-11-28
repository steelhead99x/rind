package ai.kixel.rindbench;

import android.app.Activity;
import android.app.Dialog;
import android.content.Context;
import android.graphics.drawable.ColorDrawable;
import android.graphics.drawable.GradientDrawable;
import android.view.Gravity;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.view.WindowManager;
import android.widget.Button;
import android.widget.LinearLayout;
import android.widget.ScrollView;
import android.widget.TextView;

/** M3 modal bottom sheet: drag handle, title, Done, scrolling body, at most 90% of the screen. */
final class Sheet {
    private Sheet() {}

    static Dialog show(Activity a, String title, View content) {
        Dialog d = new Dialog(a);
        d.requestWindowFeature(Window.FEATURE_NO_TITLE);

        LinearLayout box = new LinearLayout(a) {
            @Override protected void onMeasure(int w, int h) {
                int max = Math.round(getResources().getDisplayMetrics().heightPixels * 0.9f);
                int size = MeasureSpec.getMode(h) == MeasureSpec.UNSPECIFIED ? max : Math.min(MeasureSpec.getSize(h), max);
                super.onMeasure(w, MeasureSpec.makeMeasureSpec(size, MeasureSpec.AT_MOST));
            }
        };
        box.setOrientation(LinearLayout.VERTICAL);
        float r = Theme.dp(a, 28);
        GradientDrawable bg = new GradientDrawable();
        bg.setColor(Theme.surfaceContainerLow);
        bg.setCornerRadii(new float[]{r, r, r, r, 0, 0, 0, 0});
        box.setBackground(bg);
        box.setPadding(0, 0, 0, Theme.dpi(a, 16));

        View handle = new View(a);
        handle.setBackground(Theme.shape(Theme.alpha(Theme.onSurfaceVariant, 0.4f), Theme.dp(a, 2)));
        handle.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        LinearLayout.LayoutParams hl = new LinearLayout.LayoutParams(Theme.dpi(a, 32), Theme.dpi(a, 4));
        hl.gravity = Gravity.CENTER_HORIZONTAL;
        hl.topMargin = Theme.dpi(a, 16);
        hl.bottomMargin = Theme.dpi(a, 8);
        box.addView(handle, hl);

        LinearLayout top = new LinearLayout(a);
        top.setOrientation(LinearLayout.HORIZONTAL);
        top.setGravity(Gravity.CENTER_VERTICAL);
        top.setPaddingRelative(Theme.dpi(a, 24), 0, Theme.dpi(a, 12), 0);
        TextView t = Theme.heading(a, title, Theme.Type.TITLE_LARGE, Theme.onSurface);
        top.addView(t, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        Button done = Theme.button(a, "Done", Theme.Btn.TEXT, null);
        done.setOnClickListener(v -> d.dismiss());
        top.addView(done);
        box.addView(top);

        ScrollView sc = new ScrollView(a);
        if (content.getParent() instanceof ViewGroup) ((ViewGroup) content.getParent()).removeView(content);
        sc.addView(content, new ScrollView.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.WRAP_CONTENT));
        box.addView(sc, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));

        d.setContentView(box);
        d.setCanceledOnTouchOutside(true);
        Window w = d.getWindow();
        if (w != null) {
            w.setBackgroundDrawable(new ColorDrawable(0));
            int sw = a.getResources().getDisplayMetrics().widthPixels;
            w.setLayout(Math.min(sw, Theme.dpi(a, 640)), ViewGroup.LayoutParams.WRAP_CONTENT);
            w.setGravity(Gravity.BOTTOM | Gravity.CENTER_HORIZONTAL);
            w.addFlags(WindowManager.LayoutParams.FLAG_DIM_BEHIND);
            w.setDimAmount(0.32f);
        }
        d.show();
        return d;
    }

    /** Body text inside a sheet, with the sheet's 24dp side margins. */
    static TextView body(Context c, CharSequence s, boolean mono) {
        TextView t = Theme.text(c, s, Theme.Type.BODY_MEDIUM, Theme.onSurface);
        if (mono) t.setTypeface(android.graphics.Typeface.MONOSPACE);
        t.setTextIsSelectable(true);
        t.setPadding(Theme.dpi(c, 24), Theme.dpi(c, 8), Theme.dpi(c, 24), Theme.dpi(c, 8));
        return t;
    }
}
