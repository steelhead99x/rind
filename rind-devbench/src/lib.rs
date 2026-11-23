//! rind-devbench: run rind-bench's benches (every library, every report
//! operation the target builds) inside an iOS or Android app.
//!
//! C API (iOS, and the JNI wrappers in `android.rs` call the same functions):
//! - `devbench_catalog_json()`: the rows this build can time, as data:
//!   `{schema, rind_commit, target, device, sections[], libraries[], rows[{id, op, section, row, library, file}], extra[]}`.
//! - `devbench_start(config_json)`: starts a run on a background thread.
//! - `devbench_status_json()`: progress and the latest result per row.
//! - `devbench_stop()`, `devbench_free(ptr)`.
//!
//! Output: JSON lines (`t` = start | row | error | round | done | stopped |
//! report) streamed to an optional TCP sink (a plain `ncat -l -k`
//! collector, see tools/listen-devbench.sh) and written to `<out_dir>/<run_id>.jsonl`; the
//! final `report` line and `<run_id>.json` are a bench-report host result
//! (schema 1: host, commit, cpu, os, libraries, results[{operation, library,
//! id, ns, ns_low, ns_high, throughput}]) so rind-results' tooling can read it.
mod benches;
mod device;
mod ops;
#[cfg(target_os = "android")]
mod android;

use criterion::{Mode, Plan, Sample, Throughput};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::{CStr, CString, c_char};
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

pub const SCHEMA: &str = "rind-devbench/1";
pub const RIND_COMMIT: &str = env!("DEVBENCH_RIND_COMMIT");
pub const CRATE_VERSIONS: &str = env!("DEVBENCH_CRATE_VERSIONS");
pub const TARGET: &str = env!("DEVBENCH_TARGET");

static STOP: AtomicBool = AtomicBool::new(false);
static RUNNING: AtomicBool = AtomicBool::new(false);
static STATUS: Mutex<Option<Value>> = Mutex::new(None);
static CATALOG: OnceLock<Value> = OnceLock::new();

fn stop_flag() -> bool {
    STOP.load(Ordering::Relaxed)
}

/// The CPU features this build denies, from `RIND_DEVBENCH_DENY` at build time
/// (comma-separated `RIND_CPU_DISABLE_<id>` ids such as `sha3,dit`); empty if unset.
pub const CPU_DENIED: &str = match option_env!("RIND_DEVBENCH_DENY") {
    Some(ids) => ids,
    None => "",
};

static DENIES_APPLIED: AtomicBool = AtomicBool::new(false);

/// Sets `RIND_CPU_DISABLE_<id>` for each id in [`CPU_DENIED`], before rind's
/// first call: rind reads the CPU's features once and keeps them. Takes effect
/// only if rind was built with `--cfg rind_cpu_disable` (`build-ios.sh` does,
/// when `RIND_DEVBENCH_DENY` is set). An app has no shell to set them from.
///
/// # Safety
/// `std::env::set_var` is not safe to call while another thread may read the
/// environment, so the caller must guarantee that no other thread exists or
/// reads the environment: run this once, from the process's first
/// thread, before it starts any other: an iOS app calls `devbench_apply_denies`
/// at the top of `main`, before `UIApplicationMain`, and a command-line host at
/// the top of `main`. It does nothing after the first call, and nothing here
/// calls it from a worker thread: [`catalog`] and [`start`] refuse a build that
/// denies features when it was not called.
pub unsafe fn apply_build_denies() {
    if DENIES_APPLIED.swap(true, Ordering::SeqCst) {
        return;
    }
    for id in CPU_DENIED.split(',').filter(|id| !id.is_empty() && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')) {
        // SAFETY: the caller's contract above: no other thread exists or reads the environment.
        unsafe { std::env::set_var(format!("RIND_CPU_DISABLE_{id}"), "1") };
    }
}

/// Whether this build denies features whose variables were never set, so a
/// run would time rind with them enabled while reporting them denied.
fn denies_missing() -> bool {
    !CPU_DENIED.is_empty() && !DENIES_APPLIED.load(Ordering::SeqCst)
}

const DENIES_MISSING: &str = "this build denies CPU features but apply_build_denies (devbench_apply_denies) was not called at the top of main, before any thread started";

/// The report library and operation of a criterion row ID, as bench-report's
/// `operation_of` matches them.
pub fn operation_of(id: &str) -> Option<(&'static str, &'static str, String)> {
    for (section, op) in ops::OPERATIONS {
        let (pre, post) = op.split_once("{lib}").unwrap();
        if id.len() > pre.len() + post.len() && id.starts_with(pre) && id.ends_with(post) {
            let lib = &id[pre.len()..id.len() - post.len()];
            if !lib.contains('/') {
                return Some((section, op, lib.to_string()));
            }
        }
    }
    None
}

/// (operation template, report library) of a row, from the catalog.
fn row_meta(id: &str) -> (Value, Value) {
    catalog()["rows"]
        .as_array()
        .and_then(|rows| rows.iter().find(|r| r["id"] == id))
        .map(|r| (r["op"].clone(), r["library"].clone()))
        .unwrap_or((Value::Null, Value::Null))
}

fn libs_has(rows: &[Value], lib: &str) -> bool {
    rows.iter().any(|r| r["extra"] != true && r["library"] == lib)
}

fn report_library(row: &str) -> Option<&'static str> {
    ops::LIBRARIES.iter().find(|(r, _)| *r == row).map(|(_, n)| *n)
}

fn throughput_json(t: Option<Throughput>) -> Value {
    match t {
        Some(Throughput::Bytes(n)) => json!({"Bytes": n}),
        Some(Throughput::BytesDecimal(n)) => json!({"BytesDecimal": n}),
        Some(Throughput::Elements(n)) => json!({"Elements": n}),
        Some(Throughput::ElementsAndBytes { elements, bytes }) => json!({"Elements": elements, "Bytes": bytes}),
        None => Value::Null,
    }
}

fn now_rfc3339() -> String {
    let s = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs() as i64;
    let (days, rem) = (s.div_euclid(86400), s.rem_euclid(86400));
    // civil-from-days (Howard Hinnant)
    let z = days + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!("{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}+00:00", rem / 3600, rem % 3600 / 60, rem % 60)
}

/// Lists every row of every bench file (setup code runs; nothing is timed).
pub fn catalog() -> &'static Value {
    // Bench setup code wants a big stack; the caller may be a GCD or JNI thread.
    CATALOG.get_or_init(|| {
        if denies_missing() {
            return json!({"schema": SCHEMA, "error": DENIES_MISSING, "rows": [], "extra": [], "sections": [], "libraries": [], "operations_without_rows": [], "device": device::capabilities()});
        }
        std::thread::Builder::new()
            .name("devbench-catalog".into())
            .stack_size(64 << 20)
            .spawn(build_catalog)
            .ok()
            .and_then(|h| h.join().ok())
            .unwrap_or_else(|| json!({"schema": SCHEMA, "error": "listing panicked", "rows": [], "extra": [], "sections": [], "libraries": [], "operations_without_rows": [], "device": device::capabilities()}))
    })
}

fn build_catalog() -> Value {
    {
        let mut rows = Vec::new();
        let mut extra = Vec::new();
        let mut failed = Vec::new();
        for (file, main) in benches::FILES {
            let plan = Plan { mode: Mode::List, listed: vec![], results: vec![], on_row: None, stop: None };
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| criterion::with_plan(plan, || main())));
            match r {
                Ok(plan) => {
                    for (id, _t) in plan.listed {
                        match operation_of(&id) {
                            Some((section, op, row)) => {
                                let library = report_library(&row);
                                rows.push(json!({"id": id, "op": op, "section": section, "row": row,
                                    "library": library.unwrap_or("?"), "file": file}));
                            }
                            None => {
                                // Not a report operation: rind-bench's other rows (SLH-DSA, PBKDF2,
                                // AES-KW, AES-CBC/CTR, JWT, larger RSA, more sizes, ...), offered
                                // as "More: <file>" groups, off by default.
                                let segs: Vec<&str> = id.split('/').collect();
                                let pos = segs.iter().position(|s| report_library(s).is_some())
                                    .or_else(|| segs.iter().position(|s| s.starts_with("rind")))
                                    .unwrap_or(segs.len() - 1);
                                let row = segs[pos];
                                let library = report_library(row).unwrap_or(if row.starts_with("rind") { "rind" } else { row });
                                let mut op_segs: Vec<&str> = segs.clone();
                                op_segs[pos] = "{lib}";
                                let section = format!("More: {file}");
                                extra.push(json!({"id": id, "file": file}));
                                rows.push(json!({"id": id, "op": op_segs.join("/"), "section": section, "row": row,
                                    "library": library, "file": file, "extra": true}));
                            }
                        }
                    }
                }
                Err(_) => failed.push(json!(file)),
            }
        }
        let mut libs: Vec<&str> = rows.iter().filter(|r| r["extra"] != true).filter_map(|r| r["library"].as_str()).collect();
        let mut more_libs: Vec<&str> = rows.iter().filter(|r| r["extra"] == true).filter_map(|r| r["library"].as_str()).filter(|l| !libs_has(&rows, l)).collect();
        more_libs.sort();
        more_libs.dedup();
        libs.sort();
        libs.dedup();
        let sections: Vec<&str> = {
            let mut v: Vec<&str> = vec![];
            for (s, _) in ops::OPERATIONS {
                if !v.contains(s) {
                    v.push(s)
                }
            }
            for r in &rows {
                if let Some(sec) = r["section"].as_str() {
                    if r["extra"] == true && !v.contains(&sec) {
                        v.push(sec)
                    }
                }
            }
            v
        };
        let missing: Vec<String> = ops::OPERATIONS
            .iter()
            .filter(|(_, op)| !rows.iter().any(|r| r["extra"] != true && r["op"] == *op))
            .map(|(_, op)| op.to_string())
            .collect();
        json!({
            "schema": SCHEMA, "rind_commit": RIND_COMMIT, "target": TARGET,
            "openssl": cfg!(feature = "__bench_openssl"),
            "device": device::capabilities(),
            "sections": sections, "libraries": libs, "more_libraries": more_libs, "rows": rows, "extra_count": extra.len(),
            "operations_without_rows": missing, "files_failed_to_list": failed,
        })
    }
}

#[derive(serde::Deserialize, Default)]
#[serde(default)]
struct Config {
    /// Row IDs to time; empty = every report row in the catalog.
    ids: Vec<String>,
    /// Or select by report library names and/or sections (applied when `ids` is empty).
    libraries: Vec<String>,
    sections: Vec<String>,
    /// Include rows that are not report operations.
    include_extra: bool,
    rounds: Option<u32>,
    warm_ms: Option<u64>,
    sample_ms: Option<u64>,
    samples: Option<usize>,
    host: Option<String>,
    port: Option<u16>,
    out_dir: Option<String>,
    /// e.g. the rustls keys dir copied into the app bundle.
    env: BTreeMap<String, String>,
    label: Option<String>,
}

struct Sink {
    tcp: Option<std::net::TcpStream>,
    file: Option<std::fs::File>,
    state: &'static str,
    lines: u64,
}

impl Sink {
    fn send(&mut self, v: &Value) {
        let mut line = serde_json::to_string(v).unwrap();
        line.push('\n');
        if let Some(f) = self.file.as_mut() {
            let _ = f.write_all(line.as_bytes());
        }
        if let Some(t) = self.tcp.as_mut() {
            if t.write_all(line.as_bytes()).is_err() {
                self.tcp = None;
                self.state = "lost";
            }
        }
        self.lines += 1;
    }
}

fn set_status(f: impl FnOnce(&mut Value)) {
    let mut s = STATUS.lock().unwrap();
    let v = s.get_or_insert_with(|| json!({}));
    f(v);
}

fn median(v: &mut [f64]) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = v.len();
    if n % 2 == 1 { v[n / 2] } else { (v[n / 2 - 1] + v[n / 2]) / 2.0 }
}

fn run(cfg: Config) {
    for (k, v) in &cfg.env {
        // SAFETY: set before any bench thread starts; the app does not read env concurrently.
        unsafe { std::env::set_var(k, v) };
    }
    let cat = catalog();
    let rows = cat["rows"].as_array().unwrap();
    let mut selected: Vec<(String, String)> = Vec::new(); // (id, file)
    let want_ids: HashSet<&str> = cfg.ids.iter().map(|s| s.as_str()).collect();
    for r in rows {
        let id = r["id"].as_str().unwrap();
        let extra = r["extra"] == true;
        let lib_ok = cfg.libraries.is_empty() || r["library"].as_str().is_some_and(|l| cfg.libraries.iter().any(|x| x == l))
            // "More" groups may name libraries the report does not (fips205): take them when their group is picked.
            || (extra && r["library"].as_str().is_some_and(|l| !libs_has(rows, l)));
        let sec_named = r["section"].as_str().is_some_and(|s| cfg.sections.iter().any(|x| x == s));
        let ok = if !want_ids.is_empty() {
            want_ids.contains(id)
        } else if extra {
            lib_ok && (sec_named || cfg.include_extra)
        } else {
            lib_ok && (cfg.sections.is_empty() || sec_named)
        };
        if ok {
            selected.push((id.to_string(), r["file"].as_str().unwrap().to_string()));
        }
    }
    let rounds = cfg.rounds.unwrap_or(3).max(1);
    let warm_ms = cfg.warm_ms.unwrap_or(300);
    let sample_ms = cfg.sample_ms.unwrap_or(100);
    let samples = cfg.samples.unwrap_or(10).max(1);
    let started = now_rfc3339();
    let run_id = format!("{}-{}", cfg.label.clone().unwrap_or_else(|| "run".into()), started.replace([':', '+'], ""));
    let mut sink = Sink { tcp: None, file: None, state: "none", lines: 0 };
    if let Some(dir) = &cfg.out_dir {
        let _ = std::fs::create_dir_all(dir);
        sink.file = std::fs::File::create(format!("{dir}/{run_id}.jsonl")).ok();
    }
    if let (Some(h), Some(p)) = (&cfg.host, cfg.port) {
        use std::net::ToSocketAddrs;
        sink.state = "unreachable";
        if let Ok(mut addrs) = (h.as_str(), p).to_socket_addrs() {
            if let Some(a) = addrs.next() {
                if let Ok(t) = std::net::TcpStream::connect_timeout(&a, std::time::Duration::from_secs(10)) {
                    sink.tcp = Some(t);
                    sink.state = "connected";
                }
            }
        }
    }
    let files: Vec<String> = {
        let mut v: Vec<String> = selected.iter().map(|(_, f)| f.clone()).collect();
        v.dedup();
        let mut seen = HashSet::new();
        v.retain(|f| seen.insert(f.clone()));
        v
    };
    let total = selected.len() * rounds as usize;
    set_status(|s| {
        *s = json!({"running": true, "run_id": run_id, "started": started, "total": total, "done": 0,
            "round": 0, "rounds": rounds, "current": null, "sink": sink.state, "lines": 0, "errors": 0,
            "results": {}, "rind_commit": RIND_COMMIT});
    });
    sink.send(&json!({"t": "start", "schema": SCHEMA, "run_id": run_id, "started": started,
        "rind_commit": RIND_COMMIT, "target": TARGET, "device": cat["device"],
        "config": {"rows": selected.len(), "rounds": rounds, "warm_ms": warm_ms, "sample_ms": sample_ms, "samples": samples,
                   "openssl": cfg!(feature = "__bench_openssl")},
        "crates": serde_json::from_str::<Value>(CRATE_VERSIONS).unwrap_or(Value::Null)}));
    let t0 = Instant::now();
    let select: HashSet<String> = selected.iter().map(|(i, _)| i.clone()).collect();
    let mut per_id: HashMap<String, (Vec<f64>, Vec<f64>, Value)> = HashMap::new(); // medians per round, all samples, throughput
    let mut errors: Vec<Value> = vec![];
    let sink = std::rc::Rc::new(std::cell::RefCell::new(sink));
    'rounds: for round in 1..=rounds {
        set_status(|s| s["round"] = json!(round));
        // Alternate the file order each round, so no library always runs first or last.
        let order: Vec<&String> = if round % 2 == 0 { files.iter().rev().collect() } else { files.iter().collect() };
        for file in order {
            if stop_flag() {
                break 'rounds;
            }
            let main = benches::FILES.iter().find(|(f, _)| f == file).unwrap().1;
            let sk = sink.clone();
            let on_row: Box<dyn FnMut(&str, Option<&Sample>)> = Box::new(move |id, s| match s {
                None => set_status(|st| st["current"] = json!(id)),
                Some(s) => {
                    let mut line = if let Some(e) = &s.error {
                        json!({"t": "error", "round": round, "id": id, "error": e})
                    } else {
                        let mut v = s.samples_ns.clone();
                        let med = median(&mut v);
                        json!({"t": "row", "round": round, "id": id, "ns": med,
                            "ns_low": v.first(), "ns_high": v.last(), "samples_ns": s.samples_ns,
                            "iters": s.iters_per_sample, "throughput": throughput_json(s.throughput)})
                    };
                    let (op, lib) = row_meta(id);
                    line["op"] = op;
                    line["library"] = lib;
                    let mut k = sk.borrow_mut();
                    k.send(&line);
                    let (state, lines) = (k.state, k.lines);
                    drop(k);
                    set_status(|st| {
                        st["done"] = json!(st["done"].as_u64().unwrap_or(0) + 1);
                        st["sink"] = json!(state);
                        st["lines"] = json!(lines);
                        if line["t"] == "error" {
                            st["errors"] = json!(st["errors"].as_u64().unwrap_or(0) + 1);
                        }
                        st["results"][id] = line.clone();
                    });
                }
            });
            let plan = Plan {
                mode: Mode::Run { select: Some(select.clone()), warm_ms, sample_ms, samples },
                listed: vec![], results: vec![], on_row: Some(on_row), stop: Some(stop_flag),
            };
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| criterion::with_plan(plan, || main())));
            match r {
                Ok(plan) => {
                    for s in plan.results {
                        if let Some(e) = s.error {
                            errors.push(json!({"id": s.id, "round": round, "error": e}));
                            continue;
                        }
                        let mut v = s.samples_ns.clone();
                        let e = per_id.entry(s.id.clone()).or_insert_with(|| (vec![], vec![], throughput_json(s.throughput)));
                        e.0.push(median(&mut v));
                        e.1.extend(s.samples_ns);
                    }
                }
                Err(_) => {
                    let line = json!({"t": "error", "round": round, "file": file, "error": "bench file setup panicked"});
                    sink.borrow_mut().send(&line);
                    errors.push(line);
                }
            }
        }
        sink.borrow_mut().send(&json!({"t": "round", "round": round, "elapsed_s": t0.elapsed().as_secs_f64()}));
    }
    let stopped = stop_flag();
    // bench-report-shaped result: per row, the median of the per-round medians;
    // ns_low/ns_high are the lowest/highest per-round medians (not criterion CIs).
    let mut results = vec![];
    for (id, _) in &selected {
        if let Some((meds, _all, tp)) = per_id.get(id) {
            let mut m = meds.clone();
            let med = median(&mut m);
            let (op, lib) = row_meta(id);
            results.push(json!({"operation": op, "library": lib, "id": id, "ns": med,
                "ns_low": m.first(), "ns_high": m.last(), "rounds": m.len(), "throughput": tp}));
        }
    }
    let dev = &cat["device"];
    let report = json!({
        "schema": 1, "producer": SCHEMA, "host": dev["host_slug"], "commit": RIND_COMMIT,
        "started": started, "finished": now_rfc3339(),
        "cpu": dev["cpu"], "os": dev["os"], "toolchain": {"rustc": env!("DEVBENCH_RUSTC"), "target": TARGET},
        "libraries": serde_json::from_str::<Value>(CRATE_VERSIONS).unwrap_or(Value::Null),
        "status": if stopped { "stopped" } else { "ok" },
        "device": dev, "timing": {"rounds": rounds, "warm_ms": warm_ms, "sample_ms": sample_ms, "samples": samples,
            "ns": "median of per-round medians", "ns_low_high": "min/max per-round median"},
        "errors": errors, "results": results,
        "cpu_denied": CPU_DENIED,
    });
    {
        let mut k = sink.borrow_mut();
        k.send(&json!({"t": if stopped { "stopped" } else { "done" }, "elapsed_s": t0.elapsed().as_secs_f64(), "rows": results.len()}));
        k.send(&json!({"t": "report", "report": report}));
    }
    if let Some(dir) = &cfg.out_dir {
        let _ = std::fs::write(format!("{dir}/{run_id}.json"), serde_json::to_vec_pretty(&report).unwrap());
    }
    let (state, lines) = { let k = sink.borrow(); (k.state, k.lines) };
    set_status(|s| {
        s["running"] = json!(false);
        s["finished"] = json!(true);
        s["stopped"] = json!(stopped);
        s["sink"] = json!(state);
        s["lines"] = json!(lines);
        s["elapsed_s"] = json!(t0.elapsed().as_secs_f64());
        s["current"] = Value::Null;
    });
}

/// Start a run (JSON config); false if one is already running or the JSON is bad.
pub fn start(config_json: &str) -> Result<(), String> {
    let cfg: Config = serde_json::from_str(config_json).map_err(|e| e.to_string())?;
    if denies_missing() {
        return Err(DENIES_MISSING.into());
    }
    if RUNNING.swap(true, Ordering::SeqCst) {
        return Err("already running".into());
    }
    STOP.store(false, Ordering::SeqCst);
    std::thread::Builder::new()
        .name("devbench".into())
        .stack_size(64 << 20)
        .spawn(move || {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(cfg)));
            if r.is_err() {
                set_status(|s| {
                    s["running"] = json!(false);
                    s["error"] = json!("runner panicked");
                });
            }
            RUNNING.store(false, Ordering::SeqCst);
        })
        .map_err(|e| e.to_string())?;
    Ok(())
}

pub fn status() -> Value {
    let mut v = STATUS.lock().unwrap().clone().unwrap_or_else(|| json!({"running": false}));
    v["running"] = json!(RUNNING.load(Ordering::SeqCst));
    v
}

pub fn stop() {
    STOP.store(true, Ordering::SeqCst);
}

fn to_c(s: String) -> *mut c_char {
    CString::new(s).unwrap_or_default().into_raw()
}

#[unsafe(no_mangle)]
pub extern "C" fn devbench_catalog_json() -> *mut c_char {
    to_c(catalog().to_string())
}

#[unsafe(no_mangle)]
pub extern "C" fn devbench_device_json() -> *mut c_char {
    to_c(device::capabilities().to_string())
}

/// 0 = started; otherwise an error string is in `devbench_status_json`'s `start_error`.
///
/// # Safety
/// `config` is a NUL-terminated UTF-8 string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn devbench_start(config: *const c_char) -> i32 {
    let s = unsafe { CStr::from_ptr(config) }.to_string_lossy().into_owned();
    match start(&s) {
        Ok(()) => 0,
        Err(e) => {
            set_status(|st| st["start_error"] = json!(e));
            1
        }
    }
}

/// Applies the build's CPU denies. Call it first thing in `main`, before the
/// process starts any other thread (see [`apply_build_denies`]).
///
/// # Safety
/// As [`apply_build_denies`]: the process must have no other thread yet.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn devbench_apply_denies() {
    // SAFETY: the caller's contract above.
    unsafe { apply_build_denies() };
}

/// Set an environment variable before the catalog is read (rind-bench's
/// rustls rows read RIND_BENCH_KEYS_DIR while listing, not only when timed).
///
/// # Safety
/// NUL-terminated UTF-8 strings; call before any run starts.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn devbench_setenv(key: *const c_char, value: *const c_char) {
    let k = unsafe { CStr::from_ptr(key) }.to_string_lossy().into_owned();
    let v = unsafe { CStr::from_ptr(value) }.to_string_lossy().into_owned();
    unsafe { std::env::set_var(k, v) };
}

#[unsafe(no_mangle)]
pub extern "C" fn devbench_status_json() -> *mut c_char {
    to_c(status().to_string())
}

#[unsafe(no_mangle)]
pub extern "C" fn devbench_stop() {
    stop()
}

/// # Safety
/// `p` came from one of the `*_json` functions here.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn devbench_free(p: *mut c_char) {
    if !p.is_null() {
        drop(unsafe { CString::from_raw(p) });
    }
}
