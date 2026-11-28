package io.github.steelhead99x.rindbench;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.ByteArrayOutputStream;
import java.io.InputStream;
import java.net.HttpURLConnection;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

/**
 * Contender talks to moq-bench.dev for live demo sessions.
 * If health is missing, redirected to a login page, or not JSON, the app shows
 * "Session service not available yet" and does not invent a live session.
 */
final class ContenderClient {
    static final int AVAILABLE = 0, UNAVAILABLE = 1, UNREACHABLE = 2;
    static final String DEFAULT_BASE = "https://moq-bench.dev";

    final String baseURL;

    ContenderClient(String baseURL) {
        this.baseURL = baseURL == null || baseURL.isEmpty() ? DEFAULT_BASE : baseURL;
    }

    static final class Health {
        int status = UNAVAILABLE;
        String detail = "";
        String serviceName = "";
        boolean isLabReferee;
        String baseURL;
    }

    static final class Session {
        String code, name, presenter, state;
        List<JSONObject> ranks = new ArrayList<>();
    }

    interface HealthCb { void done(Health h); }
    interface SessionCb { void done(Session session, String error); }

    static final class HttpResult {
        int code;
        byte[] raw;
        String location = "";
        Exception err;
        String body() { return raw == null ? "" : new String(raw, StandardCharsets.UTF_8); }
        boolean ok() { return code >= 200 && code < 300; }
        /** The body as a JSON object, or null when it isn't one or carries an "error". */
        JSONObject json() {
            try {
                JSONObject o = raw == null ? null : new JSONObject(new String(raw, StandardCharsets.UTF_8));
                return o == null || o.has("error") ? null : o;
            } catch (Exception e) { return null; }
        }
    }

    void get(String path, java.util.function.Consumer<HttpResult> done) {
        new Thread(() -> {
            HttpResult r = new HttpResult();
            HttpURLConnection c = null;
            try {
                URL url = new URL(baseURL + path);
                c = (HttpURLConnection) url.openConnection();
                c.setInstanceFollowRedirects(false);
                c.setConnectTimeout(8000);
                c.setReadTimeout(8000);
                c.setRequestMethod("GET");
                c.setRequestProperty("Accept", "application/json");
                c.setUseCaches(false);
                try { c.setRequestProperty("Cookie", ""); } catch (Exception ignored) {}
                r.code = c.getResponseCode();
                String loc = c.getHeaderField("Location");
                if (loc != null) r.location = loc;
                InputStream in = r.code >= 400 ? c.getErrorStream() : c.getInputStream();
                if (in != null) {
                    ByteArrayOutputStream out = new ByteArrayOutputStream();
                    byte[] buf = new byte[4096];
                    int n;
                    while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
                    r.raw = out.toByteArray();
                }
            } catch (Exception e) {
                r.err = e;
            } finally {
                if (c != null) c.disconnect();
            }
            done.accept(r);
        }, "contender-http").start();
    }

    void probeHealth(HealthCb done) {
        Health h = new Health();
        h.baseURL = baseURL;
        if (baseURL == null || baseURL.isEmpty()) {
            h.status = UNAVAILABLE;
            h.detail = "No session address is set.";
            done.done(h);
            return;
        }
        get("/api/health", r -> {
            if (r.err != null) {
                h.status = UNREACHABLE;
                h.detail = "Could not reach moq-bench.dev.";
                done.done(h);
                return;
            }
            String body = r.body();
            boolean access = r.location.contains("cloudflareaccess.com")
                    || body.contains("Log in to moq-bench.dev")
                    || body.contains("Under construction");
            if (access || r.code == 302 || r.code == 401 || r.code == 403) {
                h.status = UNAVAILABLE;
                h.detail = "Session service not available yet.";
                done.done(h);
                return;
            }
            // Only a 2xx JSON body that names the service is a healthy one: an error page
            // or a 500's JSON error body is not.
            JSONObject json = r.ok() ? r.json() : null;
            if (json != null && !json.optString("name", "").isEmpty()) {
                h.serviceName = json.optString("name", "");
                h.isLabReferee = "moq-contender-referee".equals(h.serviceName);
                h.status = AVAILABLE;
                h.detail = h.isLabReferee ? "Lab referee ready." : "Session service ready.";
                done.done(h);
                return;
            }
            h.status = UNAVAILABLE;
            h.detail = "Session service not available yet.";
            done.done(h);
        });
    }

    void lookupSession(String code, SessionCb done) {
        String enc;
        try { enc = java.net.URLEncoder.encode(code, "UTF-8").replace("+", "%20"); }
        catch (Exception e) { enc = code; }
        get("/api/sessions/" + enc, r -> {
            if (r.err != null) { done.done(null, "Could not reach moq-bench.dev."); return; }
            if (r.code == 404) { done.done(null, "No session matches that code."); return; }
            String body = r.body();
            JSONObject json = r.json();
            if (r.code == 302 || r.code == 401 || r.code == 403
                    || r.location.contains("cloudflareaccess.com")
                    || body.contains("Log in to moq-bench.dev")) {
                done.done(null, "Session service not available yet.");
                return;
            }
            // The service answered, but with an error: a JSON error body, or a 4xx or 5xx. That code can't be
            // opened; the service itself is up, so don't say it isn't.
            if (isErrorBody(body) || (r.code >= 400 && json == null)) {
                done.done(null, "Could not open that session.");
                return;
            }
            if (json == null) {
                done.done(null, "Session service not available yet.");
                return;
            }
            // A session is a 2xx answer that names it; anything else, such as a 500, is no session.
            if (!r.ok() || (json.optString("name", "").isEmpty() && json.optString("title", "").isEmpty())) {
                done.done(null, "Could not open that session.");
                return;
            }
            Session s = new Session();
            s.code = code;
            s.name = first(json, "name", "title", "Session");
            s.presenter = first(json, "presenter", "host", "");
            s.state = first(json, "state", "status", "waiting");
            JSONArray ranks = json.optJSONArray("ranks");
            if (ranks != null) {
                for (int i = 0; i < ranks.length(); i++) s.ranks.add(ranks.optJSONObject(i));
            }
            done.done(s, null);
        });
    }

    private static String first(JSONObject o, String a, String b, String fallback) {
        String v = o.optString(a, "");
        if (!v.isEmpty()) return v;
        v = o.optString(b, "");
        return v.isEmpty() ? fallback : v;
    }

    static String codeFromQRString(String raw) {
        if (raw == null) return null;
        String s = raw.trim();
        if (s.isEmpty()) return null;
        try {
            URL u = new URL(s);
            String path = u.getPath() == null ? "" : u.getPath();
            String[] parts = path.split("/");
            java.util.ArrayList<String> bits = new java.util.ArrayList<>();
            for (String p : parts) if (p != null && !p.isEmpty()) bits.add(p);
            if (bits.size() >= 2) {
                String prev = bits.get(bits.size() - 2);
                if ("join".equals(prev) || "s".equals(prev) || "session".equals(prev))
                    return bits.get(bits.size() - 1);
            }
            if (bits.size() == 1) return bits.get(0);
        } catch (Exception ignored) {}
        String rest = Pattern.compile("[^A-Za-z0-9\\-_]").matcher(s).replaceAll("");
        return rest.isEmpty() ? null : rest;
    }

    static JSONObject scrubbedDeviceFromCatalog(JSONObject catalog) {
        JSONObject d = catalog != null ? catalog.optJSONObject("device") : null;
        if (d == null) d = new JSONObject();
        JSONObject out = new JSONObject();
        try {
            out.put("model", d.optString("product", "phone"));
            out.put("soc", d.optString("cpu", "unknown"));
        } catch (Exception ignored) {}
        return out;
    }

    static String neededEndpointsText() {
        return "Needed on moq-bench.dev:\n"
                + "GET /api/health\n"
                + "GET /api/sessions/{code}\n"
                + "POST /api/sessions/{code}/join\n"
                + "GET /api/sessions/{code}/status\n"
                + "POST /api/sessions/{code}/results";
    }

    /** Whether body is a JSON object carrying an "error", as the service answers a code it can't open. */
    private static boolean isErrorBody(String body) {
        try {
            return new JSONObject(body).has("error");
        } catch (Exception e) {
            return false;
        }
    }

}
