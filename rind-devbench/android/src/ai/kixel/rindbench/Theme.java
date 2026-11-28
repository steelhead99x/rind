package ai.kixel.rindbench;

import android.content.Context;
import android.content.res.ColorStateList;
import android.content.res.Configuration;
import android.graphics.Color;
import android.graphics.Typeface;
import android.graphics.drawable.ClipDrawable;
import android.graphics.drawable.ColorDrawable;
import android.graphics.drawable.Drawable;
import android.graphics.drawable.GradientDrawable;
import android.graphics.drawable.InsetDrawable;
import android.graphics.drawable.LayerDrawable;
import android.graphics.drawable.RippleDrawable;
import android.graphics.drawable.StateListDrawable;
import android.os.Build;
import android.util.TypedValue;
import android.view.Gravity;
import android.view.HapticFeedbackConstants;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.widget.Button;
import android.widget.CheckBox;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.LinearLayout;
import android.widget.ProgressBar;
import android.widget.Switch;
import android.widget.TextView;

/**
 * Instrument-panel colours on platform widgets, with day and night palettes.
 * The type scale uses sp so labels and readouts follow the system font size.
 */
final class Theme {
    // Colour roles, set by init().
    static int primary, onPrimary, primaryContainer, onPrimaryContainer;
    static int secondaryContainer, onSecondaryContainer;
    static int surface, surfaceContainerLow, surfaceContainer, surfaceContainerHigh, surfaceContainerHighest;
    static int onSurface, onSurfaceVariant, outline, outlineVariant;
    static int error, errorContainer, onErrorContainer;
    static boolean dark;

    static void init(Context c) {
        dark = (c.getResources().getConfiguration().uiMode & Configuration.UI_MODE_NIGHT_MASK)
                == Configuration.UI_MODE_NIGHT_YES;
        instrumentColors();
        error = dark ? 0xFFFFB4AB : 0xFFBA1A1A;
        errorContainer = dark ? 0xFF93000A : 0xFFFFDAD6;
        onErrorContainer = dark ? 0xFFFFDAD6 : 0xFF410002;
    }

    /** Kixel's palette: graphite surfaces, Kixel amber for controls and the timing display (BRANDING.md). */
    private static void instrumentColors() {
        if (dark) {
            primary = 0xFFFFB020; onPrimary = 0xFF07090D;
            primaryContainer = 0xFF35270E; onPrimaryContainer = 0xFFFFB020;
            secondaryContainer = 0xFF3A2C10; onSecondaryContainer = 0xFFFFDDA0;
            surface = 0xFF07090D; surfaceContainerLow = 0xFF0D1118; surfaceContainer = 0xFF121820;
            surfaceContainerHigh = 0xFF1B2430; surfaceContainerHighest = 0xFF253140;
            onSurface = 0xFFE7ECF2; onSurfaceVariant = 0xFFB5C0CE;
            outline = 0xFF8B96A5; outlineVariant = 0xFF2A3340;
        } else {
            primary = 0xFF8A5300; onPrimary = 0xFFFFFFFF;
            primaryContainer = 0xFFFBEBCB; onPrimaryContainer = 0xFF704400;
            secondaryContainer = 0xFFFFE9C2; onSecondaryContainer = 0xFF4A3000;
            surface = 0xFFF5F6F8; surfaceContainerLow = 0xFFFCFDFE; surfaceContainer = 0xFFEBEEF2;
            surfaceContainerHigh = 0xFFE1E6ED; surfaceContainerHighest = 0xFFD7DEE7;
            onSurface = 0xFF161C24; onSurfaceVariant = 0xFF425064;
            outline = 0xFF566579; outlineVariant = 0xFF9FAFC1;
        }
    }

    /** Brand art retains its original colors. */
    static ImageView brandImage(Context c, String name) {
        ImageView image = new ImageView(c);
        image.setImageResource(c.getResources().getIdentifier(name, "drawable", c.getPackageName()));
        image.setScaleType(ImageView.ScaleType.FIT_CENTER);
        image.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        return image;
    }

    static int alpha(int color, float a) { return (color & 0x00FFFFFF) | (Math.round(a * 255) << 24); }

    /** Transparent bars, light or dark icons to match the theme. */
    static void styleWindow(Window w) {
        w.getDecorView(); // creates the decor so the insets controller exists
        w.setStatusBarColor(Color.TRANSPARENT);
        w.setNavigationBarColor(Color.TRANSPARENT);
        w.setBackgroundDrawable(new ColorDrawable(surface));
        if (Build.VERSION.SDK_INT >= 29) w.setNavigationBarContrastEnforced(false);
        if (Build.VERSION.SDK_INT >= 30) {
            w.setDecorFitsSystemWindows(false);
            int light = android.view.WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS
                    | android.view.WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS;
            android.view.WindowInsetsController ic = w.getInsetsController();
            if (ic != null) ic.setSystemBarsAppearance(dark ? 0 : light, light);
        } else {
            int f = View.SYSTEM_UI_FLAG_LAYOUT_STABLE | View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN
                    | View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION;
            if (!dark) f |= View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR | View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR;
            w.getDecorView().setSystemUiVisibility(f);
        }
    }

    // Spacing on the 8dp grid.
    static final int S1 = 4, S2 = 8, S3 = 12, S4 = 16, S6 = 24;

    static float dp(Context c, float v) {
        return TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_DIP, v, c.getResources().getDisplayMetrics());
    }
    static int dpi(Context c, float v) { return Math.round(dp(c, v)); }

    // ---- Type scale (M3). size sp, line height sp, medium weight.
    enum Type {
        HEADLINE_SMALL(24, 32, false), TITLE_LARGE(22, 28, false), TITLE_MEDIUM(16, 24, true),
        TITLE_SMALL(14, 20, true), BODY_LARGE(16, 24, false), BODY_MEDIUM(14, 20, false),
        BODY_SMALL(12, 16, false), LABEL_LARGE(14, 20, true), LABEL_MEDIUM(12, 16, true);
        final float size, line; final boolean medium;
        Type(float s, float l, boolean m) { size = s; line = l; medium = m; }
    }

    static Typeface face(boolean medium) {
        return Typeface.create(medium ? "sans-serif-medium" : "sans-serif", Typeface.NORMAL);
    }

    static void type(TextView t, Type r) {
        t.setTextSize(TypedValue.COMPLEX_UNIT_SP, r.size);
        t.setTypeface(face(r.medium));
        float linePx = TypedValue.applyDimension(TypedValue.COMPLEX_UNIT_SP, r.line, t.getResources().getDisplayMetrics());
        if (Build.VERSION.SDK_INT >= 28) t.setLineHeight(Math.round(linePx));
        else t.setLineSpacing(0f, r.line / r.size / 1.17f);
    }

    /** Wrapping text, never truncated. */
    static TextView text(Context c, CharSequence s, Type r, int color) {
        TextView t = new TextView(c);
        t.setText(s);
        t.setTextColor(color);
        type(t, r);
        t.setIncludeFontPadding(false);
        return t;
    }

    static TextView heading(Context c, CharSequence s, Type r, int color) {
        TextView t = text(c, s, r, color);
        // API 28; the app runs from 26, where the call would throw NoSuchMethodError.
        if (Build.VERSION.SDK_INT >= 28) t.setAccessibilityHeading(true);
        return t;
    }

    // ---- Icons (vector drawables in res/drawable).
    static Drawable icon(Context c, String name, int tint) {
        int id = c.getResources().getIdentifier(name, "drawable", c.getPackageName());
        if (id == 0) return null;
        Drawable d = c.getDrawable(id).mutate();
        d.setTint(tint);
        return d;
    }

    static ImageView iconView(Context c, String name, int tint) {
        ImageView v = new ImageView(c);
        v.setImageDrawable(icon(c, name, tint));
        v.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        return v;
    }

    // ---- Shapes and states.
    static GradientDrawable shape(int color, float radiusPx) {
        GradientDrawable g = new GradientDrawable();
        g.setColor(color);
        g.setCornerRadius(radiusPx);
        return g;
    }

    static RippleDrawable ripple(int rippleBase, Drawable content, Drawable mask) {
        return new RippleDrawable(ColorStateList.valueOf(alpha(rippleBase, 0.12f)), content, mask);
    }

    /** Bounded ripple for a full-width row. */
    static Drawable rowRipple() {
        return ripple(onSurface, null, new ColorDrawable(Color.WHITE));
    }

    private static ColorStateList enabledList(int on, int off) {
        return new ColorStateList(new int[][]{new int[]{android.R.attr.state_enabled}, new int[]{}}, new int[]{on, off});
    }

    /**
     * Button whose optional leading icon is an inline image span, so icon and
     * label stay centred together and the icon greys out with the label.
     */
    static final class M3Button extends Button {
        String label = "", iconName;
        /** The description relabel() last set, so a later label replaces it but a caller's own is kept. */
        private CharSequence autoDesc;
        int fgOn, fgOff;
        M3Button(Context c) { super(c, null, 0); }
        @Override public void setEnabled(boolean e) { super.setEnabled(e); relabel(); }
        void setLabel(String l) { label = l; relabel(); }
        void relabel() {
            int color = isEnabled() ? fgOn : fgOff;
            setTextColor(color);
            if (iconName == null) { setText(label); return; }
            Drawable d = icon(getContext(), iconName, color);
            if (d == null) { setText(label); return; }
            int s = dpi(getContext(), 18);
            d.setBounds(0, 0, s, s);
            android.text.SpannableStringBuilder sb = new android.text.SpannableStringBuilder("\uFFFC\u2002" + label);
            int align = Build.VERSION.SDK_INT >= 29 ? android.text.style.DynamicDrawableSpan.ALIGN_CENTER
                    : android.text.style.DynamicDrawableSpan.ALIGN_BASELINE;
            sb.setSpan(new android.text.style.ImageSpan(d, align), 0, 1, android.text.Spanned.SPAN_EXCLUSIVE_EXCLUSIVE);
            setText(sb);
            CharSequence cd = getContentDescription();
            if (cd == null || (autoDesc != null && autoDesc.toString().contentEquals(cd))) {
                setContentDescription(label);
                autoDesc = label;
            }
        }
    }

    // ---- Buttons. 48dp tall (40dp visual + touch), compact corners, sentence case.
    enum Btn { FILLED, TONAL, OUTLINED, TEXT }

    static Button button(Context c, String title, Btn kind, String iconName) {
        M3Button b = new M3Button(c);
        b.label = title;
        b.setAllCaps(false);
        b.setGravity(Gravity.CENTER);
        type(b, Type.LABEL_LARGE);
        b.setIncludeFontPadding(false);
        b.setMinHeight(dpi(c, 48)); b.setMinimumHeight(dpi(c, 48));
        b.setMinWidth(dpi(c, 48)); b.setMinimumWidth(dpi(c, 48));
        b.setStateListAnimator(null);
        int hp = kind == Btn.TEXT ? 12 : 24;
        b.setPadding(dpi(c, hp), dpi(c, 10), dpi(c, hp), dpi(c, 10));
        styleButton(b, kind, iconName);
        return b;
    }

    static void styleButton(Button b, Btn kind, String iconName) {  // b must come from button()
        Context c = b.getContext();
        float r = dp(c, 10);
        int fg, bg;
        switch (kind) {
            case FILLED: fg = onPrimary; bg = primary; break;
            case TONAL: fg = onSecondaryContainer; bg = secondaryContainer; break;
            default: fg = primary; bg = Color.TRANSPARENT; break;
        }
        int fgOff = alpha(onSurface, 0.38f);
        GradientDrawable g = new GradientDrawable();
        g.setCornerRadius(r);
        boolean filledish = kind == Btn.FILLED || kind == Btn.TONAL;
        g.setColor(filledish ? enabledList(bg, alpha(onSurface, 0.12f)) : ColorStateList.valueOf(Color.TRANSPARENT));
        if (kind == Btn.OUTLINED) g.setStroke(dpi(c, 1), enabledList(outline, alpha(onSurface, 0.12f)));
        // Inset 4dp top/bottom so the visual is 40dp inside a 48dp target.
        InsetDrawable inset = new InsetDrawable(g, 0, dpi(c, 4), 0, dpi(c, 4));
        InsetDrawable mask = new InsetDrawable(shape(Color.WHITE, r), 0, dpi(c, 4), 0, dpi(c, 4));
        b.setBackground(ripple(fg, inset, mask));
        M3Button m = (M3Button) b;
        m.fgOn = fg; m.fgOff = fgOff; m.iconName = iconName;
        m.relabel();
    }

    static ImageButton iconButton(Context c, String iconName, String desc) {
        ImageButton b = new ImageButton(c);
        b.setImageDrawable(icon(c, iconName, onSurfaceVariant));
        b.setContentDescription(desc);
        b.setBackground(ripple(onSurfaceVariant, null, null));
        b.setScaleType(ImageView.ScaleType.CENTER);
        int s = dpi(c, 48);
        b.setMinimumWidth(s); b.setMinimumHeight(s);
        b.setLayoutParams(new LinearLayout.LayoutParams(s, s));
        return b;
    }

    // ---- Segmented button (two or more options, single select).
    static Button segment(Context c, String title, int index, int count) {
        M3Button b = new M3Button(c);
        b.label = title;
        b.setAllCaps(false);
        b.setGravity(Gravity.CENTER);
        type(b, Type.LABEL_LARGE);
        b.setIncludeFontPadding(false);
        b.setStateListAnimator(null);
        b.setMinHeight(dpi(c, 48)); b.setMinimumHeight(dpi(c, 48));
        b.setPadding(dpi(c, 12), dpi(c, 10), dpi(c, 12), dpi(c, 10));
        b.setTag(new int[]{index, count});
        return b;
    }

    static void selectSegment(Button b, boolean selected, boolean enabled) {
        Context c = b.getContext();
        int[] ic = (int[]) b.getTag();
        float r = dp(c, 10);
        float[] radii = ic[0] == 0 ? new float[]{r, r, 0, 0, 0, 0, r, r}
                : ic[0] == ic[1] - 1 ? new float[]{0, 0, r, r, r, r, 0, 0} : new float[8];
        GradientDrawable g = new GradientDrawable();
        g.setCornerRadii(radii);
        g.setColor(selected ? (enabled ? secondaryContainer : alpha(onSurface, 0.12f)) : Color.TRANSPARENT);
        g.setStroke(dpi(c, 1), enabled ? outline : alpha(onSurface, 0.12f));
        GradientDrawable m = new GradientDrawable();
        m.setCornerRadii(radii);
        m.setColor(Color.WHITE);
        // Overlap the shared 1dp edge so the two outlines read as one line.
        int over = ic[0] == 0 ? 0 : -dpi(c, 1);
        b.setBackground(ripple(onSurface, new InsetDrawable(g, over, dpi(c, 4), 0, dpi(c, 4)),
                new InsetDrawable(m, over, dpi(c, 4), 0, dpi(c, 4))));
        M3Button mb = (M3Button) b;
        mb.fgOn = selected ? onSecondaryContainer : onSurface;
        mb.fgOff = alpha(onSurface, 0.38f);
        mb.iconName = selected ? "ic_check" : null;
        b.setSelected(selected);
        b.setEnabled(enabled);
    }

    // ---- Selection controls.
    static Switch switchM3(Context c, String desc) {
        Switch s = new Switch(c);
        s.setContentDescription(desc);
        s.setShowText(false);
        s.setBackground(null);
        s.setTrackDrawable(switchTrack(c));
        s.setThumbDrawable(switchThumb(c));
        s.setThumbTintList(null);
        s.setTrackTintList(null);
        s.setMinimumHeight(dpi(c, 48));
        s.setMinHeight(dpi(c, 48));
        s.setSwitchPadding(0);
        s.setSwitchMinWidth(dpi(c, 52));
        return s;
    }

    private static Drawable switchTrack(Context c) {
        int w = dpi(c, 52), h = dpi(c, 32);
        StateListDrawable s = new StateListDrawable();
        s.addState(new int[]{-android.R.attr.state_enabled, android.R.attr.state_checked},
                track(c, w, h, alpha(onSurface, 0.12f), 0));
        s.addState(new int[]{-android.R.attr.state_enabled},
                track(c, w, h, alpha(surfaceContainerHighest, 0.12f), alpha(onSurface, 0.12f)));
        s.addState(new int[]{android.R.attr.state_checked}, track(c, w, h, primary, 0));
        s.addState(new int[]{}, track(c, w, h, surfaceContainerHighest, outline));
        return s;
    }

    private static GradientDrawable track(Context c, int w, int h, int fill, int stroke) {
        GradientDrawable g = new GradientDrawable();
        g.setColor(fill);
        g.setCornerRadius(h / 2f);
        g.setSize(w, h);
        if (stroke != 0) g.setStroke(dpi(c, 2), stroke);
        return g;
    }

    private static Drawable switchThumb(Context c) {
        StateListDrawable s = new StateListDrawable();
        s.addState(new int[]{-android.R.attr.state_enabled, android.R.attr.state_checked}, thumb(c, 24, surface));
        s.addState(new int[]{-android.R.attr.state_enabled}, thumb(c, 16, alpha(onSurface, 0.38f)));
        s.addState(new int[]{android.R.attr.state_checked}, thumb(c, 24, onPrimary));
        s.addState(new int[]{}, thumb(c, 16, outline));
        return s;
    }

    private static Drawable thumb(Context c, int sizeDp, int color) {
        // 26 x 32 box so two thumbs make the 52dp track; the dot is centred in it.
        // LayerDrawable (not InsetDrawable) so the insets don't count as padding.
        GradientDrawable g = new GradientDrawable();
        g.setShape(GradientDrawable.OVAL);
        g.setColor(color);
        int bw = dpi(c, 26), bh = dpi(c, 32), s = dpi(c, sizeDp);
        g.setSize(s, s);
        int ix = (bw - s) / 2, iy = (bh - s) / 2;
        LayerDrawable d = new LayerDrawable(new Drawable[]{g});
        d.setLayerInset(0, ix, iy, bw - s - ix, bh - s - iy);
        return d;
    }

    static CheckBox checkBox(Context c) {
        CheckBox b = new CheckBox(c);
        b.setButtonTintList(new ColorStateList(new int[][]{
                new int[]{-android.R.attr.state_enabled}, new int[]{android.R.attr.state_checked}, new int[]{}},
                new int[]{alpha(onSurface, 0.38f), primary, onSurfaceVariant}));
        b.setBackground(ripple(primary, null, null));
        b.setMinimumWidth(dpi(c, 48)); b.setMinimumHeight(dpi(c, 48));
        return b;
    }

    // ---- Lists.
    /** One- to three-line list item: optional leading icon, text column, optional trailing views. */
    static final class Row {
        final LinearLayout view;
        final TextView headline, supporting;
        final ImageView leading;
        Row(LinearLayout v, TextView h, TextView s, ImageView l) { view = v; headline = h; supporting = s; leading = l; }
        void setSupporting(CharSequence s) {
            supporting.setText(s);
            supporting.setVisibility(s == null || s.length() == 0 ? View.GONE : View.VISIBLE);
        }
        void setEnabled(boolean en) {
            view.setEnabled(en);
            float a = en ? 1f : 0.38f;
            headline.setAlpha(a); supporting.setAlpha(a);
            if (leading != null) leading.setAlpha(a);
            for (int i = 0; i < view.getChildCount(); i++) view.getChildAt(i).setEnabled(en);
        }
    }

    static Row row(Context c, String headline, String supporting, String leadingIcon, View... trailing) {
        LinearLayout v = new LinearLayout(c);
        v.setOrientation(LinearLayout.HORIZONTAL);
        v.setGravity(Gravity.CENTER_VERTICAL);
        v.setMinimumHeight(dpi(c, 56));
        v.setPaddingRelative(dpi(c, S4), dpi(c, S2), dpi(c, trailing.length > 0 ? S2 : S4), dpi(c, S2));
        ImageView lead = null;
        if (leadingIcon != null) {
            lead = iconView(c, leadingIcon, onSurfaceVariant);
            LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(dpi(c, 24), dpi(c, 24));
            lp.setMarginEnd(dpi(c, S4));
            v.addView(lead, lp);
        }
        LinearLayout col = new LinearLayout(c);
        col.setOrientation(LinearLayout.VERTICAL);
        TextView h = text(c, headline, Type.BODY_LARGE, onSurface);
        TextView s = text(c, supporting == null ? "" : supporting, Type.BODY_MEDIUM, onSurfaceVariant);
        col.addView(h);
        col.addView(s);
        v.addView(col, new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        for (View t : trailing) {
            LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
                    ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT);
            lp.setMarginStart(dpi(c, S2));
            if (t.getLayoutParams() instanceof LinearLayout.LayoutParams) {
                LinearLayout.LayoutParams o = (LinearLayout.LayoutParams) t.getLayoutParams();
                lp.width = o.width; lp.height = o.height;
            }
            v.addView(t, lp);
        }
        Row r = new Row(v, h, s, lead);
        r.setSupporting(supporting);
        return r;
    }

    static void clickable(View v, View.OnClickListener l) {
        v.setBackground(rowRipple());
        v.setFocusable(true);
        v.setClickable(true);
        v.setOnClickListener(l);
    }

    /**
     * Makes a whole row the single touch and TalkBack target for a switch or
     * checkbox inside it (M3 list item with a trailing or leading control).
     */
    static void toggleRow(View row, android.widget.CompoundButton cb, String desc, Class<?> role) {
        cb.setClickable(false);
        cb.setFocusable(false);
        cb.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        clickable(row, v -> { if (cb.isEnabled()) cb.toggle(); });
        row.setContentDescription(desc);
        row.setAccessibilityDelegate(new View.AccessibilityDelegate() {
            @Override public void onInitializeAccessibilityNodeInfo(View h, android.view.accessibility.AccessibilityNodeInfo info) {
                super.onInitializeAccessibilityNodeInfo(h, info);
                info.setClassName(role.getName());
                info.setCheckable(true);
                info.setChecked(cb.isChecked());
                info.setEnabled(cb.isEnabled());
            }
        });
    }

    /** Vertical column capped at maxDp wide and centred, for readable line lengths on tablets. */
    static LinearLayout readable(Context c, int maxDp) {
        int max = dpi(c, maxDp);
        LinearLayout l = new LinearLayout(c) {
            @Override protected void onMeasure(int w, int h) {
                int size = View.MeasureSpec.getSize(w);
                if (size > max) w = View.MeasureSpec.makeMeasureSpec(max, View.MeasureSpec.EXACTLY);
                super.onMeasure(w, h);
            }
        };
        l.setOrientation(LinearLayout.VERTICAL);
        return l;
    }

    static View divider(Context c) {
        View v = new View(c);
        v.setBackgroundColor(outlineVariant);
        v.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        v.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, Math.max(1, dpi(c, 1))));
        return v;
    }

    static TextView subheader(Context c, String s) {
        TextView t = heading(c, s, Type.TITLE_SMALL, primary);
        t.setPaddingRelative(dpi(c, S4), dpi(c, S4), dpi(c, S4), dpi(c, S2));
        return t;
    }

    /** Instrument panel with a thin outline and compact corners. */
    static LinearLayout card(Context c) {
        LinearLayout l = new LinearLayout(c);
        l.setOrientation(LinearLayout.VERTICAL);
        l.setPadding(dpi(c, S4), dpi(c, S4), dpi(c, S4), dpi(c, S4));
        GradientDrawable panel = shape(surfaceContainer, dp(c, 8));
        panel.setStroke(Math.max(1, dpi(c, 1)), outlineVariant);
        l.setBackground(panel);
        return l;
    }

    static ProgressBar progress(Context c) {
        ProgressBar p = new ProgressBar(c, null, android.R.attr.progressBarStyleHorizontal);
        float r = dp(c, 2);
        GradientDrawable track = shape(secondaryContainer, r);
        ClipDrawable fill = new ClipDrawable(shape(primary, r), Gravity.START, ClipDrawable.HORIZONTAL);
        LayerDrawable ld = new LayerDrawable(new Drawable[]{track, fill});
        ld.setId(0, android.R.id.background);
        ld.setId(1, android.R.id.progress);
        p.setProgressDrawable(ld);
        p.setIndeterminate(false);
        p.setMax(1);
        return p;
    }

    static void space(LinearLayout root, int dp) {
        View v = new View(root.getContext());
        v.setImportantForAccessibility(View.IMPORTANT_FOR_ACCESSIBILITY_NO);
        root.addView(v, new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, dpi(root.getContext(), dp)));
    }

    static void haptic(View v, boolean confirm) {
        if (v == null) return;
        int flag = (confirm && Build.VERSION.SDK_INT >= 30)
                ? HapticFeedbackConstants.CONFIRM
                : HapticFeedbackConstants.CONTEXT_CLICK;
        v.performHapticFeedback(flag);
    }
}
