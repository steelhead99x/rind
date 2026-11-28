package ai.kixel.rindbench;

import android.app.Activity;
import android.content.Intent;
import android.graphics.ImageFormat;
import android.hardware.camera2.CameraAccessException;
import android.hardware.camera2.CameraCaptureSession;
import android.hardware.camera2.CameraCharacteristics;
import android.hardware.camera2.CameraDevice;
import android.hardware.camera2.CameraManager;
import android.hardware.camera2.CaptureRequest;
import android.media.Image;
import android.media.ImageReader;
import android.os.Bundle;
import android.os.Handler;
import android.os.HandlerThread;
import android.util.Size;
import android.view.Surface;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.view.WindowManager;
import android.widget.FrameLayout;
import android.widget.LinearLayout;
import android.widget.TextView;

import com.google.zxing.BinaryBitmap;
import com.google.zxing.PlanarYUVLuminanceSource;
import com.google.zxing.Result;
import com.google.zxing.common.HybridBinarizer;
import com.google.zxing.qrcode.QRCodeReader;

import java.nio.ByteBuffer;
import java.util.Arrays;

/** Camera is opened only on the Scan path. Decodes a session QR and returns the code. */
public class QrScannerActivity extends Activity implements SurfaceHolder.Callback {
    public static final String EXTRA_CODE = "code";
    private SurfaceView preview;
    private CameraDevice camera;
    private CameraCaptureSession session;
    private ImageReader reader;
    private HandlerThread thread;
    private Handler handler;
    private boolean sent;
    private final QRCodeReader qr = new QRCodeReader();

    @Override protected void onCreate(Bundle b) {
        super.onCreate(b);
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        Theme.init(this);
        // Camera screens stay dark in either theme: black behind the preview, light bar text and icons.
        getWindow().setStatusBarColor(0xFF000000);
        getWindow().setNavigationBarColor(0xFF000000);
        // The light theme asks for dark bar icons, which would vanish on black; on Android 15
        // the bars are transparent over the preview, so set light icons in both themes.
        getWindow().getDecorView(); // creates the decor so the insets controller exists
        if (android.os.Build.VERSION.SDK_INT >= 30) {
            android.view.WindowInsetsController ic = getWindow().getInsetsController();
            if (ic != null) ic.setSystemBarsAppearance(0, android.view.WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS
                    | android.view.WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS);
        } else {
            View d = getWindow().getDecorView();
            d.setSystemUiVisibility(d.getSystemUiVisibility()
                    & ~(View.SYSTEM_UI_FLAG_LIGHT_STATUS_BAR | View.SYSTEM_UI_FLAG_LIGHT_NAVIGATION_BAR));
        }
        FrameLayout root = new FrameLayout(this);
        root.setBackgroundColor(0xFF000000);
        preview = new SurfaceView(this);
        preview.getHolder().addCallback(this);
        root.addView(preview, new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT));
        LinearLayout bar = new LinearLayout(this);
        bar.setOrientation(LinearLayout.HORIZONTAL);
        bar.setGravity(android.view.Gravity.CENTER_VERTICAL);
        bar.setBackgroundColor(0x99000000);
        bar.setMinimumHeight(Theme.dpi(this, 64));
        int p = Theme.dpi(this, 4);
        bar.setPadding(p, 0, Theme.dpi(this, 16), 0);
        bar.setOnApplyWindowInsetsListener((view, insets) -> {
            int top = android.os.Build.VERSION.SDK_INT >= 30
                    ? insets.getInsets(android.view.WindowInsets.Type.systemBars()).top
                    : insets.getSystemWindowInsetTop();
            view.setPadding(p, top, Theme.dpi(this, 16), 0);
            return insets;
        });
        android.widget.ImageButton cancel = Theme.iconButton(this, "ic_close", "Cancel scan");
        cancel.setImageDrawable(Theme.icon(this, "ic_close", 0xFFFFFFFF));
        cancel.setBackground(Theme.ripple(0xFFFFFFFF, null, null));
        cancel.setOnClickListener(v -> finish());
        TextView title = Theme.heading(this, "Scan a session code", Theme.Type.TITLE_LARGE, 0xFFFFFFFF);
        LinearLayout.LayoutParams tl = new LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1);
        tl.setMarginStart(Theme.dpi(this, 4));
        tl.topMargin = tl.bottomMargin = Theme.dpi(this, 8);
        bar.addView(cancel);
        bar.addView(title, tl);
        FrameLayout.LayoutParams blp = new FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT);
        blp.gravity = android.view.Gravity.TOP;
        root.addView(bar, blp);
        setContentView(root);
        setTitle("Scan a session code");
    }

    @Override public void surfaceCreated(SurfaceHolder holder) { openCamera(holder.getSurface()); }
    @Override public void surfaceChanged(SurfaceHolder holder, int format, int w, int h) {}
    @Override public void surfaceDestroyed(SurfaceHolder holder) { closeCamera(); }

    private void openCamera(Surface surface) {
        thread = new HandlerThread("qr-cam");
        thread.start();
        handler = new Handler(thread.getLooper());
        CameraManager mgr = (CameraManager) getSystemService(CAMERA_SERVICE);
        try {
            String id = backCamera(mgr);
            if (id == null) { noCamera(); return; }
            CameraCharacteristics ch = mgr.getCameraCharacteristics(id);
            android.hardware.camera2.params.StreamConfigurationMap map =
                    ch.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP);
            Size size = pick(map.getOutputSizes(SurfaceHolder.class));
            reader = ImageReader.newInstance(size.getWidth(), size.getHeight(), ImageFormat.YUV_420_888, 2);
            reader.setOnImageAvailableListener(this::onImage, handler);
            mgr.openCamera(id, new CameraDevice.StateCallback() {
                @Override public void onOpened(CameraDevice d) {
                    camera = d;
                    try {
                        d.createCaptureSession(Arrays.asList(surface, reader.getSurface()),
                                new CameraCaptureSession.StateCallback() {
                                    @Override public void onConfigured(CameraCaptureSession s) {
                                        session = s;
                                        try {
                                            CaptureRequest.Builder b = d.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW);
                                            b.addTarget(surface);
                                            b.addTarget(reader.getSurface());
                                            b.set(CaptureRequest.CONTROL_AF_MODE, CaptureRequest.CONTROL_AF_MODE_CONTINUOUS_PICTURE);
                                            s.setRepeatingRequest(b.build(), null, handler);
                                        } catch (Exception e) { finish(); }
                                    }
                                    @Override public void onConfigureFailed(CameraCaptureSession s) { finish(); }
                                }, handler);
                    } catch (Exception e) { finish(); }
                }
                @Override public void onDisconnected(CameraDevice d) { closeCamera(); }
                @Override public void onError(CameraDevice d, int error) { closeCamera(); finish(); }
            }, handler);
        } catch (SecurityException e) {
            setResult(RESULT_CANCELED);
            finish();
        } catch (CameraAccessException e) {
            noCamera();
        }
    }

    private void noCamera() {
        runOnUiThread(() -> {
            android.widget.Toast.makeText(this,
                    "This phone has no camera to scan a code. Type the session code instead.",
                    android.widget.Toast.LENGTH_LONG).show();
            finish();
        });
    }

    private void onImage(ImageReader r) {
        Image img = r.acquireLatestImage();
        if (img == null || sent) { if (img != null) img.close(); return; }
        try {
            byte[] nv21 = yuv(img);
            int w = img.getWidth(), h = img.getHeight();
            PlanarYUVLuminanceSource src = new PlanarYUVLuminanceSource(nv21, w, h, 0, 0, w, h, false);
            Result result = qr.decode(new BinaryBitmap(new HybridBinarizer(src)));
            String code = ContenderClient.codeFromQRString(result.getText());
            if (code != null && !code.isEmpty()) {
                sent = true;
                Intent data = new Intent();
                data.putExtra(EXTRA_CODE, code);
                setResult(RESULT_OK, data);
                runOnUiThread(this::finish);
            }
        } catch (Exception ignored) {
        } finally {
            qr.reset();
            img.close();
        }
    }

    private static byte[] yuv(Image img) {
        Image.Plane y = img.getPlanes()[0];
        Image.Plane u = img.getPlanes()[1];
        Image.Plane v = img.getPlanes()[2];
        int w = img.getWidth(), h = img.getHeight();
        byte[] out = new byte[w * h * 3 / 2];
        ByteBuffer yb = y.getBuffer();
        int yRow = y.getRowStride();
        int pos = 0;
        for (int row = 0; row < h; row++) {
            yb.position(row * yRow);
            yb.get(out, pos, w);
            pos += w;
        }
        // NV21: VU interleaved.
        ByteBuffer vb = v.getBuffer();
        int vRow = v.getRowStride(), vPix = v.getPixelStride();
        int chromaH = h / 2, chromaW = w / 2;
        int di = w * h;
        ByteBuffer ub = u.getBuffer();
        int uRow = u.getRowStride(), uPix = u.getPixelStride();
        di = w * h;
        for (int row = 0; row < chromaH; row++) {
            for (int col = 0; col < chromaW; col++) {
                int vi = row * vRow + col * vPix;
                int ui = row * uRow + col * uPix;
                if (di + 1 < out.length) {
                    out[di++] = vi < vb.limit() ? vb.get(vi) : 0;
                    out[di++] = ui < ub.limit() ? ub.get(ui) : 0;
                }
            }
        }
        return out;
    }

    private static String backCamera(CameraManager mgr) throws CameraAccessException {
        String fallback = null;
        for (String id : mgr.getCameraIdList()) {
            Integer facing = mgr.getCameraCharacteristics(id).get(CameraCharacteristics.LENS_FACING);
            if (facing != null && facing == CameraCharacteristics.LENS_FACING_BACK) return id;
            if (fallback == null) fallback = id;
        }
        return fallback;
    }

    private static Size pick(Size[] sizes) {
        if (sizes == null || sizes.length == 0) return new Size(1280, 720);
        Size best = sizes[0];
        int bestScore = Integer.MAX_VALUE;
        for (Size s : sizes) {
            int score = Math.abs(s.getWidth() * s.getHeight() - 1280 * 720);
            if (score < bestScore) { bestScore = score; best = s; }
        }
        return best;
    }

    private void closeCamera() {
        try { if (session != null) session.close(); } catch (Exception ignored) {}
        session = null;
        try { if (camera != null) camera.close(); } catch (Exception ignored) {}
        camera = null;
        try { if (reader != null) reader.close(); } catch (Exception ignored) {}
        reader = null;
        if (thread != null) { thread.quitSafely(); thread = null; }
    }

    @Override protected void onDestroy() { closeCamera(); super.onDestroy(); }
}
