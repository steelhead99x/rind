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
#[cfg_attr(not(test), allow(dead_code))]
mod deny;
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
use std::sync::{Arc, Mutex, MutexGuard, Once};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

pub const SCHEMA: &str = "rind-devbench/1";
pub const RIND_COMMIT: &str = env!("DEVBENCH_RIND_COMMIT");
pub const CRATE_VERSIONS: &str = env!("DEVBENCH_CRATE_VERSIONS");
pub const TARGET: &str = env!("DEVBENCH_TARGET");

static STOP: AtomicBool = AtomicBool::new(false);
static RUNNING: AtomicBool = AtomicBool::new(false);
/// Held while the run slot is taken and its STOP cleared, and by stop(), so a stop() of a run that shows as
/// running is never cleared by that run's start.
static RUN_SLOT: Mutex<()> = Mutex::new(());
/// Counts acknowledged starts, so an app can tell one start's refusal on the run's thread from another's.
static STARTS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static STATUS: Mutex<Option<Value>> = Mutex::new(None);
/// The environment a catalog was listed with that decides its rows: rind-bench's rustls rows read
/// `RIND_BENCH_KEYS_DIR` while listing, `RIND_BENCH_LOW_MEMORY` drops rows, `RIND_CPU_DISABLE_*` changes what
/// rind offers, and `NOISY_BENCHMARKS` adds the RSA key-generation rows (`rind-bench/benches/rsa_gen.rs`).
type ListingEnv = Vec<(std::ffi::OsString, std::ffi::OsString)>;

fn listing_env() -> ListingEnv {
    let mut v: ListingEnv = std::env::vars_os().filter(|(k, _)| k.to_string_lossy().starts_with("RIND_") || k == "NOISY_BENCHMARKS").collect();
    v.sort();
    v
}

/// Catalogs listed so far, by the environment each was listed with, so a catalog never answers for a
/// different setting. Its lock is held while a catalog is listed and while start() or devbench_setenv
/// writes the environment, so a listing reads the settings its key names.
static CATALOGS: Mutex<Vec<(ListingEnv, Arc<Value>)>> = Mutex::new(Vec::new());

fn catalogs() -> MutexGuard<'static, Vec<(ListingEnv, Arc<Value>)>> {
    CATALOGS.lock().unwrap_or_else(|e| e.into_inner())
}

fn stop_flag() -> bool {
    STOP.load(Ordering::Relaxed)
}

/// The CPU features this build denies, from `RIND_DEVBENCH_DENY` at build time
/// (comma-separated `RIND_CPU_DISABLE_<id>` ids such as `sha3,dit`); empty if unset.
/// build.rs refuses a list with an empty or malformed entry, an id rind does not
/// read on the target, or an optimised rind built without `--cfg
/// rind_cpu_disable`, so every id here is one rind denies; this is the checked
/// list, dots dropped and each once, which the report publishes.
pub const CPU_DENIED: &str = env!("DEVBENCH_DENY_IDS");

/// Set only once every variable is written, so [`denies_missing`] never sees
/// a half-applied build as applied.
static DENIES_APPLIED: AtomicBool = AtomicBool::new(false);
/// Runs [`apply_build_denies`]'s writes once; a second caller waits for them.
static DENIES_ONCE: Once = Once::new();

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
    DENIES_ONCE.call_once(|| {
        for id in CPU_DENIED.split(',').filter(|id| !id.is_empty()) {
            // SAFETY: the caller's contract above: no other thread exists or reads the environment.
            unsafe { std::env::set_var(format!("RIND_CPU_DISABLE_{id}"), "1") };
        }
        // After the writes: a reader that sees the flag sees every variable.
        DENIES_APPLIED.store(true, Ordering::SeqCst);
    });
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
fn row_meta(cat: &Value, id: &str) -> (Value, Value) {
    cat["rows"]
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
///
/// A listing that failed in part, as with a keys directory not filled in yet, is listed again here (the apps
/// call this off their UI thread), but not while a run is going: a listing then would load the cores the
/// run is timing on, so the cached catalog answers.
pub fn catalog() -> Arc<Value> {
    catalog_in(&mut catalogs(), !RUNNING.load(Ordering::SeqCst))
}

/// What failed to list in a catalog: its `error`, or the files that failed; `None` when it all listed.
fn listing_failure(c: &Value) -> Option<String> {
    if let Some(e) = c.get("error") {
        return Some(e.as_str().unwrap_or("listing failed").to_string());
    }
    let f = c["files_failed_to_list"].as_array().filter(|f| !f.is_empty())?;
    Some(format!("{} failed to list", f.iter().filter_map(|v| v.as_str()).collect::<Vec<_>>().join(", ")))
}

/// [`catalog`], with the cache's lock already held. `retry_failed`: list a cached catalog that failed in
/// part again, rather than reuse it.
fn catalog_in(cache: &mut Vec<(ListingEnv, Arc<Value>)>, retry_failed: bool) -> Arc<Value> {
    let keys = listing_env();
    let at = cache.iter().position(|(k, _)| *k == keys);
    if let Some(i) = at
        && (!retry_failed || listing_failure(&cache[i].1).is_none())
    {
        return cache[i].1.clone();
    }
    let c = Arc::new(list_catalog());
    match at {
        Some(i) => cache[i].1 = c.clone(),
        None => {
            // A process normally uses one setting; a host that varies it keeps only the latest few.
            if cache.len() >= 4 {
                cache.remove(0);
            }
            cache.push((keys, c.clone()));
        }
    }
    c
}

fn list_catalog() -> Value {
    // Bench setup code wants a big stack; the caller may be a GCD or JNI thread.
    {
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
    }
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

/// The rows a run takes, as (id, file): by id when it names ids, otherwise by library and group.
fn select(cfg: &Config, rows: &[Value]) -> Vec<(String, String)> {
    let mut selected: Vec<(String, String)> = Vec::new(); // (id, file)
    let want_ids: HashSet<&str> = cfg.ids.iter().map(|s| s.as_str()).collect();
    // A library filter that names no library the catalog has selects nothing, before the "More" fallback
    // below could take rows for it, as it would for a misspelt name beside a More group.
    if want_ids.is_empty() && !cfg.libraries.is_empty() && !cfg.libraries.iter().any(|l| rows.iter().any(|r| r["library"] == l.as_str())) {
        return selected;
    }
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
    selected
}

/// Puts back the environment entries a start set; the caller holds the catalog lock.
fn restore_env(before: &[(String, Option<std::ffi::OsString>)]) {
    for (k, v) in before {
        // SAFETY: the run slot is the caller's, so no bench thread reads the environment, and the catalog
        // lock keeps listings out.
        match v {
            Some(v) => unsafe { std::env::set_var(k, v) },
            None => unsafe { std::env::remove_var(k) },
        }
    }
}

/// [`restore_env`], taking the catalog lock.
fn restore_env_listed(before: &[(String, Option<std::ffi::OsString>)]) {
    let _listing = catalogs();
    restore_env(before);
}

/// A catalog's rows, borrowed.
fn rows_of(c: &Value) -> &[Value] {
    c["rows"].as_array().map_or(&[][..], |r| r.as_slice())
}

/// Whether `rows` has a row for every name `cfg` selects by: its ids when it names ids, as [`select`] goes
/// by them alone, otherwise its libraries and groups.
fn covers(cfg: &Config, rows: &[Value]) -> bool {
    let has = |field: &str, v: &str| rows.iter().any(|r| r[field] == v);
    if !cfg.ids.is_empty() {
        return cfg.ids.iter().all(|v| has("id", v));
    }
    cfg.libraries.iter().all(|v| has("library", v)) && cfg.sections.iter().all(|v| has("section", v))
}

/// The catalog a run uses after its thread listed again: the relisted one, unless it selects nothing where
/// the one start() checked selects rows, so a relist that failed outright can't leave the run with nothing.
fn after_relist(cfg: &Config, checked: Arc<Value>, relisted: Arc<Value>) -> Arc<Value> {
    if select(cfg, rows_of(&relisted)).is_empty() && !select(cfg, rows_of(&checked)).is_empty() {
        checked
    } else {
        relisted
    }
}

/// The values of `field` (`"section"` or `"library"`) that `selected` takes rows from, in catalog order, and
/// the ones `named` lists that it takes none from (none when `cfg` selects by ids, which ignore both).
fn taken(cfg: &Config, rows: &[Value], selected: &[(String, String)], field: &str, named: &[String]) -> (Vec<String>, Vec<String>) {
    let ids: HashSet<&str> = selected.iter().map(|(i, _)| i.as_str()).collect();
    let mut ran: Vec<String> = Vec::new();
    for r in rows {
        if let (Some(id), Some(v)) = (r["id"].as_str(), r[field].as_str()) {
            if ids.contains(id) && !ran.iter().any(|x| x == v) {
                ran.push(v.to_string());
            }
        }
    }
    let missing = if cfg.ids.is_empty() { named.iter().filter(|s| !ran.contains(s)).cloned().collect() } else { vec![] };
    (ran, missing)
}

/// [`taken`] for groups.
fn groups_run(cfg: &Config, rows: &[Value], selected: &[(String, String)]) -> (Vec<String>, Vec<String>) {
    taken(cfg, rows, selected, "section", &cfg.sections)
}

/// [`taken`] for libraries.
fn libraries_run(cfg: &Config, rows: &[Value], selected: &[(String, String)]) -> (Vec<String>, Vec<String>) {
    taken(cfg, rows, selected, "library", &cfg.libraries)
}

/// `cat` is the catalog `start()` checked the selection against, or the one the run's thread listed again
/// when that one failed in part (see [`after_relist`]). `start_no` is the start's number, as `acked_start`.
fn run(cfg: Config, cat: Arc<Value>, start_no: u64) {
    let selected = select(&cfg, cat["rows"].as_array().unwrap());
    let (sections_run, sections_missing) = groups_run(&cfg, rows_of(&cat), &selected);
    let (libraries_run, libraries_missing) = libraries_run(&cfg, rows_of(&cat), &selected);
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
        // `run_start` and the groups once the rows are picked, so an app can report what this start runs.
        *s = json!({"running": true, "run_id": run_id, "started": started, "total": total, "done": 0,
            "round": 0, "rounds": rounds, "current": null, "sink": sink.state, "lines": 0, "errors": 0,
            "results": {}, "rind_commit": RIND_COMMIT, "acked_start": start_no, "run_start": start_no,
            "sections_run": sections_run, "sections_missing": sections_missing,
            "libraries_run": libraries_run, "libraries_missing": libraries_missing});
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
            let cat_rows = cat.clone();
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
                    let (op, lib) = row_meta(&cat_rows, id);
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
            let (op, lib) = row_meta(&cat, id);
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
    // set_var panics on these, and a panic here would escape the C boundary holding the run slot.
    if let Some(k) = cfg.env.iter().find(|(k, v)| k.is_empty() || k.contains(['=', '\0']) || v.contains('\0')).map(|(k, _)| k) {
        return Err(format!("environment entry {k:?} has an empty name, or a name with '=' or NUL, or a value with NUL"));
    }
    {
        // The slot and its STOP in one step: a stop() once the run shows as running stops this run.
        let _slot = RUN_SLOT.lock().unwrap_or_else(|e| e.into_inner());
        if RUNNING.swap(true, Ordering::SeqCst) {
            return Err("already running".into());
        }
        STOP.store(false, Ordering::SeqCst);
    }
    // No catalog is listed while the environment holds this start's settings unchecked, or put back.
    let cache = catalogs();
    // The configured environment goes in before the catalog is listed, since rind-bench's rustls rows read
    // RIND_BENCH_KEYS_DIR while listing. A refused start puts back what was there.
    let before: Vec<(String, Option<std::ffi::OsString>)> = cfg.env.keys().map(|k| (k.clone(), std::env::var_os(k))).collect();
    let refuse = |e: String| {
        restore_env(&before);
        RUNNING.store(false, Ordering::SeqCst);
        e
    };
    for (k, v) in &cfg.env {
        // SAFETY: no run is going (RUNNING was false), so no bench thread reads the environment; the app
        // does not read it concurrently, and the catalog lock keeps listings out.
        unsafe { std::env::set_var(k, v) };
    }
    // start() runs on the apps' UI thread, so it never lists: it decides from the catalog cached for these
    // settings, and leaves any listing to the run's thread.
    let cached = cache.iter().find(|(k, _)| *k == listing_env()).map(|(_, c)| c.clone());
    let list_on_thread = match &cached {
        // A complete catalog decides: a selection that matches no row would run nothing yet end "done",
        // with status "ok", so it is refused before the start is acknowledged. Each library and group can
        // be valid alone and still select nothing together, as ring with ML-KEM does.
        Some(c) if listing_failure(c).is_none() => {
            if select(&cfg, rows_of(c)).is_empty() {
                return Err(refuse("no test matches the libraries and groups picked".into()));
            }
            false
        }
        // A catalog that failed in part is listed again, before the run, when it doesn't cover what the run
        // names (an id, library or group with no row in it), so a row that lists now is not left out.
        Some(c) => select(&cfg, rows_of(c)).is_empty() || !covers(&cfg, rows_of(c)),
        // These settings were never listed.
        None => true,
    };
    drop(cache);
    let before_run = before.clone();
    let start_no = STARTS.fetch_add(1, Ordering::SeqCst) + 1;
    // The start's number, under the status lock and before its thread exists, so it can't land after the
    // thread released the slot and a later start wrote its own; every status the thread writes carries it
    // too. An app reads it once start() returns, to tell this start's status (`run_start`, `refused_start`)
    // from an earlier one's.
    set_status(|s| s["acked_start"] = json!(start_no));
    std::thread::Builder::new()
        .name("devbench".into())
        .stack_size(64 << 20)
        .spawn(move || {
            let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let cat = if list_on_thread {
                    // Polls see this run listing, not the last run's results.
                    let rounds = cfg.rounds.unwrap_or(3).max(1);
                    set_status(|s| {
                        *s = json!({"running": true, "current": "listing tests", "done": 0, "total": 0,
                            "round": 0, "rounds": rounds, "acked_start": start_no})
                    });
                    let relisted = catalog_in(&mut catalogs(), true);
                    match cached {
                        Some(checked) => after_relist(&cfg, checked, relisted),
                        None => relisted,
                    }
                } else {
                    cached.expect("a start without a cached catalog lists on its thread")
                };
                if select(&cfg, rows_of(&cat)).is_empty() {
                    // Refused once listed: no run, the environment put back, and the reason in the status.
                    let why = match listing_failure(&cat) {
                        Some(f) => format!("no test matches the libraries and groups picked ({f})"),
                        None => "no test matches the libraries and groups picked".into(),
                    };
                    restore_env_listed(&before_run);
                    // `refused_start` numbers it, so an app reports it once, even across a recreated view.
                    // Its reason is `refused_reason`, apart from `start_error`, which a later start refused before
                    // acknowledgement (as "already running") writes without touching it.
                    // Written below, with the slot's release.
                    return Some(json!({"running": false, "error": why, "refused_reason": why, "refused_start": start_no, "acked_start": start_no}));
                }
                run(cfg, cat, start_no);
                None
            }));
            // The final status and the run slot's release in one step under the status lock, which status()
            // reads both under: a poll sees either the run going or its final status, never a mix.
            let mut st = STATUS.lock().unwrap_or_else(|e| e.into_inner());
            match r {
                Ok(Some(refusal)) => *st = Some(refusal),
                Ok(None) => {}
                // A panic once run() wrote this start's status keeps its partial results; one before then
                // replaces the status, so an earlier start's refusal can't stand in for it.
                Err(_) if st.as_ref().is_some_and(|v| v["run_start"] == start_no) => {
                    let v = st.as_mut().expect("checked above");
                    v["running"] = json!(false);
                    v["error"] = json!("runner panicked");
                }
                Err(_) => *st = Some(json!({"running": false, "error": "runner panicked", "acked_start": start_no})),
            }
            RUNNING.store(false, Ordering::SeqCst);
        })
        .map_err(|e| {
            let _listing = catalogs(); // the environment goes back with listings kept out
            refuse(e.to_string())
        })?;
    Ok(())
}

pub fn status() -> Value {
    // RUNNING under the status lock: the run's thread writes its final status, then releases the slot
    // under the same lock.
    let st = STATUS.lock().unwrap_or_else(|e| e.into_inner());
    let mut v = st.clone().unwrap_or_else(|| json!({"running": false}));
    v["running"] = json!(RUNNING.load(Ordering::SeqCst));
    v
}

/// A start refused before it was acknowledged: its reason in `start_error`, leaving an acknowledged start's
/// late refusal (`refused_start`, `refused_reason`) as it is.
fn refused_now(e: &str) {
    set_status(|st| st["start_error"] = json!(e));
}

pub fn stop() {
    let _slot = RUN_SLOT.lock().unwrap_or_else(|e| e.into_inner());
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
            refused_now(&e);
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
    let _listing = catalogs(); // not while a catalog is listed
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

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg(json: Value) -> Config {
        serde_json::from_value(json).unwrap()
    }

    fn rows() -> Vec<Value> {
        vec![
            json!({"id": "a", "file": "f", "library": "rind", "section": "ML-KEM", "extra": false}),
            json!({"id": "b", "file": "f", "library": "ring", "section": "AEADs", "extra": false}),
            json!({"id": "c", "file": "f", "library": "rind", "section": "AEADs", "extra": false}),
        ]
    }

    #[test]
    fn a_catalog_covers_a_run_only_when_it_has_a_row_for_each_name() {
        assert!(covers(&cfg(json!({"libraries": ["ring"], "sections": ["AEADs"]})), &rows()));
        assert!(covers(&cfg(json!({"ids": ["a", "b"]})), &rows()));
        // A row the listing left out, as rustls's when its keys were missing.
        assert!(!covers(&cfg(json!({"ids": ["a", "tls"]})), &rows()));
        assert!(!covers(&cfg(json!({"libraries": ["rind", "rustls"]})), &rows()));
        assert!(!covers(&cfg(json!({"sections": ["AEADs", "TLS"]})), &rows()));
        // Ids alone decide what runs, so a group with no row doesn't matter beside listed ids.
        assert!(covers(&cfg(json!({"ids": ["a"], "sections": ["TLS"]})), &rows()));
    }

    #[test]
    fn a_relist_that_selects_nothing_keeps_the_checked_catalog() {
        let checked = Arc::new(json!({"rows": rows(), "files_failed_to_list": ["rustls"]}));
        let c = cfg(json!({"ids": ["a", "tls"]}));
        // The relist failed outright, as when its thread can't spawn: the run keeps the rows it was started on.
        let failed = Arc::new(json!({"error": "listing panicked", "rows": []}));
        assert!(Arc::ptr_eq(&after_relist(&c, checked.clone(), failed), &checked));
        // The relist found more rows: the run takes them.
        let mut more = rows();
        more.push(json!({"id": "tls", "file": "rustls", "library": "rind", "section": "TLS", "extra": false}));
        let relisted = Arc::new(json!({"rows": more, "files_failed_to_list": []}));
        assert!(Arc::ptr_eq(&after_relist(&c, checked, relisted.clone()), &relisted));
    }

    #[test]
    fn a_library_and_group_valid_alone_can_select_nothing_together() {
        // ring has AEADs and ML-KEM is rind's: each is a valid pick, together they match no row.
        assert!(select(&cfg(json!({"libraries": ["ring"], "sections": ["ML-KEM"]})), &rows()).is_empty());
        assert_eq!(select(&cfg(json!({"libraries": ["ring"], "sections": ["AEADs"]})), &rows()).len(), 1);
        assert_eq!(select(&cfg(json!({"libraries": ["rind"]})), &rows()).len(), 2);
    }

    #[test]
    fn a_library_filter_naming_no_library_selects_nothing_even_with_a_more_group() {
        let mut rows = rows();
        // A More group's row whose library the report doesn't list, which its group alone selects.
        rows.push(json!({"id": "s", "file": "g", "library": "fips205", "section": "More: slhdsa", "extra": true}));
        let more = |libs: Value| select(&cfg(json!({"libraries": libs, "sections": ["More: slhdsa"]})), &rows);
        // A misspelt library beside the More group: refused, not run as fips205.
        assert!(more(json!(["rign"])).is_empty());
        // A known library keeps the More fallback, and the More row's own library selects it.
        assert_eq!(more(json!(["ring"])).len(), 1);
        assert_eq!(more(json!(["fips205"])).len(), 1);
        assert_eq!(more(json!(["rign", "ring"])).len(), 1);
    }

    #[test]
    fn a_run_reports_the_groups_and_libraries_it_takes_and_the_named_ones_it_cannot() {
        let c = cfg(json!({"libraries": ["rind"], "sections": ["AEADs", "TLS 1.3 with rustls"]}));
        let sel = select(&c, &rows());
        assert_eq!(groups_run(&c, &rows(), &sel), (vec!["AEADs".to_string()], vec!["TLS 1.3 with rustls".to_string()]));
        // A library named beside one that runs, which takes no row: reported, not dropped silently.
        let c = cfg(json!({"libraries": ["rind", "rign"], "sections": ["AEADs"]}));
        let sel = select(&c, &rows());
        assert_eq!(sel.len(), 1);
        assert_eq!(libraries_run(&c, &rows(), &sel), (vec!["rind".to_string()], vec!["rign".to_string()]));
        // By ids, groups don't select, so none is missing.
        let c = cfg(json!({"ids": ["a"], "sections": ["TLS"]}));
        assert_eq!(groups_run(&c, &rows(), &select(&c, &rows())), (vec!["ML-KEM".to_string()], vec![]));
    }

    #[test]
    fn a_start_that_would_run_nothing_is_refused() {
        if denies_missing() {
            return; // start() refuses every run of such a build first
        }
        let keys_before = std::env::var_os("RIND_BENCH_KEYS_DIR");
        let low_before = std::env::var_os("RIND_BENCH_LOW_MEMORY");
        let none = r#""libraries": ["no-such-library"], "sections": ["no-such-group"]"#;
        // A start whose settings have a complete cached catalog is refused before it is acknowledged.
        if listing_failure(&catalog()).is_none() {
            let e = start(&format!("{{{none}}}")).unwrap_err();
            assert_eq!(e, "no test matches the libraries and groups picked");
            assert!(!RUNNING.load(Ordering::SeqCst));
        }
        // A start whose settings were never listed, or listed in part, is acknowledged without listing (the
        // apps call start() on their UI thread); its thread lists, then refuses in the status.
        let refused_on_thread = |env: &str| -> String {
            start(&format!(r#"{{{none}, "env": {env}}}"#)).unwrap();
            let t = Instant::now();
            while RUNNING.load(Ordering::SeqCst) {
                assert!(t.elapsed().as_secs() < 300, "the start's thread never finished");
                std::thread::sleep(std::time::Duration::from_millis(50));
            }
            let st = status();
            assert_eq!(st["running"], false);
            assert!(st.get("run_id").is_none(), "{st}");
            assert!(st["refused_start"].as_u64().is_some_and(|n| n > 0), "{st}");
            // A start refused before acknowledgement, as a second view's would be, leaves the late refusal.
            refused_now("already running");
            let after = status();
            assert_eq!(after["refused_start"], st["refused_start"]);
            assert_eq!(after["refused_reason"], st["refused_reason"]);
            st["refused_reason"].as_str().unwrap().to_string()
        };
        // An empty keys directory, as before the app copies its certificates in: rustls can't list.
        let dir = std::env::temp_dir().join(format!("rind-devbench-test-keys-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let keys = dir.to_str().unwrap();
        let env = format!(r#"{{"RIND_BENCH_KEYS_DIR": "{keys}", "RIND_BENCH_LOW_MEMORY": "1"}}"#);
        let e = refused_on_thread(&env);
        assert!(e.contains("no test matches") && e.contains("rustls failed to list"), "{e}");
        // The refused start put the environment back as it found it.
        assert_eq!(std::env::var_os("RIND_BENCH_KEYS_DIR"), keys_before);
        assert_eq!(std::env::var_os("RIND_BENCH_LOW_MEMORY"), low_before);
        let set = |env: &ListingEnv, k: &str, v: &str| env.iter().any(|(ek, ev)| ek == k && ev == v);
        let cached = || {
            catalogs().iter().find(|(k, _)| set(k, "RIND_BENCH_KEYS_DIR", keys) && set(k, "RIND_BENCH_LOW_MEMORY", "1"))
                .map(|(_, c)| c.clone())
        };
        // Its partial listing is kept, for a start with the same settings that its rows cover.
        let partial = cached().unwrap();
        assert!(listing_failure(&partial).is_some());
        // Once the certificates are in the same directory, a start that the partial listing can't cover
        // lists again on its thread, and finds the rustls rows.
        let src = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../rind-rustls/tests/keys");
        for d in std::fs::read_dir(&src).unwrap() {
            let d = d.unwrap();
            std::fs::create_dir_all(dir.join(d.file_name())).unwrap();
            for f in std::fs::read_dir(d.path()).unwrap() {
                let f = f.unwrap();
                std::fs::copy(f.path(), dir.join(d.file_name()).join(f.file_name())).unwrap();
            }
        }
        assert_eq!(refused_on_thread(&env), "no test matches the libraries and groups picked");
        let relisted = cached().unwrap();
        assert!(!Arc::ptr_eq(&partial, &relisted));
        assert_eq!(listing_failure(&relisted), None);
        let _ = std::fs::remove_dir_all(&dir);
        for bad in [r#"{"": "1"}"#, r#"{"A=B": "1"}"#, r#"{"A": "x\u0000"}"#] {
            let e = start(&format!(r#"{{"env": {bad}}}"#)).unwrap_err();
            assert!(e.contains("environment entry"), "{e}");
            assert!(!RUNNING.load(Ordering::SeqCst));
        }
    }
}
