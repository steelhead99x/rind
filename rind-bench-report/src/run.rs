//! `run`: the host side of `collect`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

use crate::error::{Error, Result};
use crate::format::py_float;
use crate::idle::{
    busy_cpus_since, busy_limit, check_idle, children_cpu_seconds, cpu_count, cpu_times,
};
use crate::paths::Paths;
use crate::tables::{
    CRITERION_ARGS, crates_for, library_of, operation_of, operation_regex, operations,
    required_features,
};

pub fn run(
    paths: &Paths,
    host: &str,
    commit: &str,
    jobs: u32,
    target_dir: &Path,
    out: &Path,
) -> Result<()> {
    let started = utc_now();
    let mut doc = vec![
        ("schema".to_string(), J::Int(1)),
        ("host".to_string(), J::Str(host.to_string())),
        ("commit".to_string(), J::Str(commit.to_string())),
        ("started".to_string(), J::Str(started.clone())),
    ];
    let cpu = cpu_model()?;
    doc.push((
        "cpu".to_string(),
        J::obj([
            ("model", J::Str(cpu)),
            ("arch", J::Str(std::env::consts::ARCH.to_string())),
            ("logical_cpus", J::Int(cpu_count() as i64)),
        ]),
    ));
    doc.push(("os".to_string(), J::Str(os_name()?)));
    let idle_before_build = match check_idle("before the build") {
        Ok(value) => value,
        Err(busy) => {
            finish(
                out,
                &doc,
                "busy",
                vec![("reason".to_string(), J::Str(busy.message))],
            )?;
            return Err(Error::new(format!("{host}: {}", "busy")));
        }
    };
    let mut env = std::env::vars().collect::<std::collections::HashMap<_, _>>();
    env.insert("CARGO_BUILD_JOBS".to_string(), jobs.to_string());
    env.insert("CARGO_TERM_COLOR".to_string(), "never".to_string());
    env.insert(
        "CARGO_TARGET_DIR".to_string(),
        target_dir
            .canonicalize()
            .unwrap_or_else(|_| target_dir.to_path_buf())
            .display()
            .to_string(),
    );
    let versions = toolchain(&env)?;
    doc.push(("toolchain".to_string(), versions));
    doc.push(("libraries".to_string(), locked_libraries(paths, &env)?));
    let cargo = "cargo";
    let bench = BENCH;
    run_cmd(&build_only(&bench), &env, false)?;
    let cpuid_raw = output(&[cargo, "run", "-q", "--release", "-p", "rind-cpuid"], &env)?;
    let rind_cpu: Value =
        serde_json::from_str(&cpuid_raw).map_err(|err| Error::new(err.to_string()))?;
    doc.push(("rind_cpu".to_string(), J::from_value(&rind_cpu)));
    let refused = refused_libraries(&rind_cpu);
    doc.push(("refused".to_string(), refused.0.clone()));
    let idle_before_run = match check_idle("before the benchmarks") {
        Ok(value) => value,
        Err(busy) => {
            finish(
                out,
                &doc,
                "busy",
                vec![("reason".to_string(), J::Str(busy.message))],
            )?;
            return Err(Error::new(format!("{host}: busy")));
        }
    };
    let criterion_dir = PathBuf::from(env["CARGO_TARGET_DIR"].clone()).join("criterion");
    let _ = fs::remove_dir_all(&criterion_dir);
    let mut args: Vec<String> = CRITERION_ARGS.iter().map(|s| (*s).to_string()).collect();
    args.push(operation_regex(
        &refused.1.iter().map(String::as_str).collect(),
    ));
    let wall0 = std::time::Instant::now();
    let ticks0 = cpu_times()?;
    let ours0 = children_cpu_seconds();
    let mut timed = bench.to_vec();
    timed.push("--");
    let arg_refs: Vec<&str> = args.iter().map(String::as_str).collect();
    timed.extend(arg_refs.iter().copied());
    run_cmd(&timed, &env, false)?;
    let ours1 = children_cpu_seconds();
    let wall = wall0.elapsed().as_secs_f64();
    let ours = ours1 - ours0;
    let other =
        ((busy_cpus_since(ticks0) - ours / wall.max(1e-9)).max(0.0) * 100.0).round() / 100.0;
    let load = J::obj([
        (
            "limit_cpus",
            J::Float(((busy_limit() * 100.0).round()) / 100.0),
        ),
        ("busy_cpus_before_build", J::Float(idle_before_build)),
        ("busy_cpus_before_run", J::Float(idle_before_run)),
        ("other_busy_cpus_during_run", J::Float(other)),
        ("noisy", J::Bool(other > busy_limit())),
    ]);
    let mut results = read_criterion(&criterion_dir)?;
    let order: std::collections::HashMap<&str, usize> = operations()
        .iter()
        .enumerate()
        .map(|(i, op)| (op.as_str(), i))
        .collect();
    results.sort_by(|a, b| {
        let ao = order.get(a.0.as_str()).copied().unwrap_or(usize::MAX);
        let bo = order.get(b.0.as_str()).copied().unwrap_or(usize::MAX);
        ao.cmp(&bo).then(a.1.cmp(&b.1))
    });
    let rows = J::Array(results.into_iter().map(|(_, _, row)| row).collect());
    let build = build_cost(&env, jobs, &refused.1)?;
    finish(
        out,
        &doc,
        "ok",
        vec![
            ("finished".to_string(), J::Str(utc_now())),
            (
                "criterion_args".to_string(),
                J::Array(args.into_iter().map(J::Str).collect()),
            ),
            ("load".to_string(), load),
            ("results".to_string(), rows),
            ("build_cost".to_string(), build),
        ],
    )
}

pub(crate) fn read_criterion(dir: &Path) -> Result<Vec<(String, String, J)>> {
    let mut out = Vec::new();
    if !dir.exists() {
        return Ok(out);
    }
    let mut files = Vec::new();
    walk(dir, &mut files);
    files.sort();
    for path in files {
        if path.file_name().and_then(|n| n.to_str()) != Some("benchmark.json") {
            continue;
        }
        if path
            .parent()
            .and_then(|p| p.file_name())
            .and_then(|n| n.to_str())
            != Some("new")
        {
            continue;
        }
        let meta: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap_or_default())
            .unwrap_or(Value::Null);
        let Some(full_id) = meta.get("full_id").and_then(Value::as_str) else {
            continue;
        };
        let Some((op, lib)) = operation_of(full_id) else {
            continue;
        };
        let estimates_path = path.parent().unwrap_or(dir).join("estimates.json");
        let estimates: Value =
            serde_json::from_str(&fs::read_to_string(&estimates_path).unwrap_or_default())
                .unwrap_or(Value::Null);
        let estimate = if estimates.get("slope").is_some() {
            &estimates["slope"]
        } else {
            &estimates["mean"]
        };
        let ns = estimate
            .get("point_estimate")
            .and_then(Value::as_f64)
            .unwrap_or(0.0);
        let low = estimate["confidence_interval"]
            .get("lower_bound")
            .and_then(Value::as_f64)
            .unwrap_or(ns);
        let high = estimate["confidence_interval"]
            .get("upper_bound")
            .and_then(Value::as_f64)
            .unwrap_or(ns);
        let library = library_of(&lib).to_string();
        let mut row = vec![
            ("operation".to_string(), J::Str(op.clone())),
            ("library".to_string(), J::Str(library.clone())),
            ("id".to_string(), J::Str(full_id.to_string())),
            ("ns".to_string(), J::Float(ns)),
            ("ns_low".to_string(), J::Float(low)),
            ("ns_high".to_string(), J::Float(high)),
        ];
        if let Some(throughput) = meta.get("throughput")
            && !throughput.is_null()
        {
            row.push(("throughput".to_string(), J::from_value(throughput)));
        }
        out.push((op, library, J::Object(row)));
    }
    Ok(out)
}

fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
    let Ok(read) = fs::read_dir(dir) else { return };
    for entry in read.filter_map(|e| e.ok()) {
        let path = entry.path();
        if path.is_dir() {
            walk(&path, files);
        } else {
            files.push(path);
        }
    }
}

/// The benchmarks, as Python's `run` runs them.
const BENCH: [&str; 6] = [
    "cargo",
    "bench",
    "-p",
    "rind-bench",
    "--features",
    "__bench_openssl",
];

/// `bench` with `--no-run`, which builds the benchmarks without running them,
/// as Python does before it reads the CPU and checks the host is idle. Run
/// there, they would take the whole suite's time before that check, and their
/// results would be deleted with the criterion directory before the timed
/// run.
fn build_only<'a>(bench: &[&'a str]) -> Vec<&'a str> {
    let mut build = bench.to_vec();
    build.push("--no-run");
    build
}

fn finish(out: &Path, base: &[(String, J)], status: &str, extra: Vec<(String, J)>) -> Result<()> {
    let mut pairs = base.to_vec();
    pairs.push(("status".to_string(), J::Str(status.to_string())));
    pairs.extend(extra);
    let text = J::Object(pairs).dump(0);
    fs::write(out, format!("{text}\n")).map_err(|err| Error::new(err.to_string()))
}

fn toolchain(env: &std::collections::HashMap<String, String>) -> Result<J> {
    if std::env::var("IN_RIND_DEV_SHELL").ok().as_deref() != Some("1") {
        return Err(Error::new(
            "run inside the dev shell: nix develop --command admin/bench-report run ...",
        ));
    }
    let version = output(&["rustc", "-vV"], env)?;
    let release = version
        .lines()
        .find_map(|line| line.strip_prefix("release: "))
        .unwrap_or("")
        .to_string();
    let pinned = pinned_toolchain()?;
    if release != pinned {
        return Err(Error::new(format!(
            "rustc {release} is not the pinned {pinned}"
        )));
    }
    let rustc = version.lines().next().unwrap_or("").to_string();
    let cargo = output(&["cargo", "-V"], env)?;
    Ok(J::obj([("rustc", J::Str(rustc)), ("cargo", J::Str(cargo))]))
}

fn pinned_toolchain() -> Result<String> {
    let text = fs::read_to_string("flake.nix")
        .or_else(|_| fs::read_to_string(crate::paths::workspace_root().join("flake.nix")))
        .map_err(|err| Error::new(err.to_string()))?;
    let marker = "rust-bin.stable.\"";
    let Some(start) = text.find(marker) else {
        return Err(Error::new("flake.nix names no pinned stable toolchain"));
    };
    let rest = &text[start + marker.len()..];
    let end = rest.find('"').unwrap_or(0);
    Ok(rest[..end].to_string())
}

fn locked_libraries(paths: &Paths, env: &std::collections::HashMap<String, String>) -> Result<J> {
    let text = fs::read_to_string(paths.lockfile()).map_err(|err| Error::new(err.to_string()))?;
    let mut versions: std::collections::HashMap<String, Vec<String>> =
        std::collections::HashMap::new();
    let mut name = None;
    for line in text.lines() {
        if let Some(rest) = line.strip_prefix("name = \"") {
            name = rest.strip_suffix('"').map(str::to_string);
        } else if let Some(rest) = line.strip_prefix("version = \"")
            && let (Some(pkg), Some(version)) = (name.take(), rest.strip_suffix('"'))
        {
            versions.entry(pkg).or_default().push(version.to_string());
        }
    }
    let mut libs = Vec::new();
    for spec in crates_for() {
        let mut crates = Vec::new();
        for name in spec.crates {
            let found = versions
                .get(*name)
                .map(|v| v.join(", "))
                .unwrap_or_else(|| "?".to_string());
            crates.push(((*name).to_string(), J::Str(found)));
        }
        libs.push((spec.library.to_string(), J::Object(crates)));
    }
    if let Some(openssl) = libs.iter_mut().find(|(name, _)| name == "openssl")
        && let J::Object(crates) = &mut openssl.1
    {
        let linked = output(&["openssl", "version"], env).unwrap_or_else(|_| "?".to_string());
        crates.push(("linked".to_string(), J::Str(linked)));
    }
    Ok(J::Object(libs))
}

fn refused_libraries(rind_cpu: &Value) -> (J, std::collections::HashSet<String>) {
    let cpuid = rind_cpu.get("cpuid").cloned().unwrap_or(Value::Null);
    let arch = std::env::consts::ARCH;
    let mut pairs = Vec::new();
    let mut names = std::collections::HashSet::new();
    let features = required_features("graviola", arch);
    if !features.is_empty() {
        let missing: Vec<String> = features
            .iter()
            .filter(|feature| cpuid.get(*feature).and_then(Value::as_i64) != Some(1))
            .map(|feature| (*feature).to_string())
            .collect();
        if !missing.is_empty() {
            names.insert("graviola".to_string());
            pairs.push((
                "graviola".to_string(),
                J::Array(missing.into_iter().map(J::Str).collect()),
            ));
        }
    }
    (J::Object(pairs), names)
}

fn build_cost(
    env: &std::collections::HashMap<String, String>,
    jobs: u32,
    refused: &std::collections::HashSet<String>,
) -> Result<J> {
    let started = utc_now();
    let python = "python3";
    let script = crate::paths::workspace_root().join("admin/build-cost");
    let mut args = vec![python.to_string(), script.display().to_string()];
    if !refused.is_empty() {
        for name in [
            "rind",
            "aws-lc-rs",
            "ring",
            "rustcrypto",
            "graviola",
            "libcrux",
            "openssl",
            "openssl-vendored",
            "rustls-rind",
            "rustls-aws-lc-rs",
            "rustls-ring",
        ] {
            if !refused.contains(name) {
                args.push(name.to_string());
            }
        }
    }
    let mut command = Command::new(python);
    command.args(&args[1..]);
    for (key, value) in env {
        command.env(key, value);
    }
    command.env("CARGO_BUILD_JOBS", jobs.to_string());
    let output = command
        .output()
        .map_err(|err| Error::new(err.to_string()))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprintln!("{stderr}");
        let reason = stderr
            .trim()
            .lines()
            .last()
            .unwrap_or("no output")
            .to_string();
        return Ok(J::obj([
            ("status", J::Str("failed".to_string())),
            ("started", J::Str(started)),
            ("reason", J::Str(reason)),
        ]));
    }
    let parsed: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
    let mut pairs = vec![
        ("status".to_string(), J::Str("ok".to_string())),
        ("started".to_string(), J::Str(started)),
    ];
    if let Some(object) = parsed.as_object() {
        for (key, value) in object {
            pairs.push((key.clone(), J::from_value(value)));
        }
    }
    Ok(J::Object(pairs))
}

fn run_cmd(
    args: &[&str],
    env: &std::collections::HashMap<String, String>,
    _quiet: bool,
) -> Result<()> {
    let mut command = Command::new(args[0]);
    command.args(&args[1..]);
    for (key, value) in env {
        command.env(key, value);
    }
    let status = command
        .status()
        .map_err(|err| Error::new(err.to_string()))?;
    if status.success() {
        Ok(())
    } else {
        Err(Error::new(format!("{} exited {status}", args.join(" "))))
    }
}

fn output(args: &[&str], env: &std::collections::HashMap<String, String>) -> Result<String> {
    let mut command = Command::new(args[0]);
    command.args(&args[1..]);
    for (key, value) in env {
        command.env(key, value);
    }
    let output = command
        .output()
        .map_err(|err| Error::new(err.to_string()))?;
    if !output.status.success() {
        return Err(Error::new(
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn cpu_model() -> Result<String> {
    #[cfg(target_os = "macos")]
    {
        return output(
            &["sysctl", "-n", "machdep.cpu.brand_string"],
            &std::env::vars().collect(),
        );
    }
    #[cfg(not(target_os = "macos"))]
    {
        let text = fs::read_to_string("/proc/cpuinfo").unwrap_or_default();
        for line in text.lines() {
            if line.starts_with("model name") || line.starts_with("Model") {
                return Ok(line
                    .split_once(':')
                    .map(|(_, rest)| rest.trim().to_string())
                    .unwrap_or_default());
            }
        }
        Ok(std::env::consts::ARCH.to_string())
    }
}

fn os_name() -> Result<String> {
    #[cfg(target_os = "macos")]
    {
        let ver = output(&["sw_vers", "-productVersion"], &std::env::vars().collect())
            .unwrap_or_default();
        let release = output(&["uname", "-r"], &std::env::vars().collect()).unwrap_or_default();
        return Ok(format!("macOS {ver} ({release})"));
    }
    #[cfg(not(target_os = "macos"))]
    {
        let mut pretty = "Linux".to_string();
        if let Ok(text) = fs::read_to_string("/etc/os-release") {
            for line in text.lines() {
                if let Some(rest) = line.strip_prefix("PRETTY_NAME=") {
                    pretty = rest.trim().trim_matches('"').to_string();
                }
            }
        }
        let release =
            output(&["uname", "-r"], &std::collections::HashMap::new()).unwrap_or_default();
        Ok(format!("{pretty} (Linux {release})"))
    }
}

fn utc_now() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    // ISO-8601 with seconds, matching datetime.isoformat(timespec="seconds").
    let days = secs / 86400;
    let time = secs % 86400;
    let (year, month, day) = civil_from_days(days as i64);
    format!(
        "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}+00:00",
        time / 3600,
        (time % 3600) / 60,
        time % 60
    )
}

fn civil_from_days(days: i64) -> (i64, u32, u32) {
    let z = days + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y, m as u32, d as u32)
}

#[derive(Clone)]
pub(crate) enum J {
    Str(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Array(Vec<J>),
    Object(Vec<(String, J)>),
    Null,
}

impl J {
    fn obj<const N: usize>(pairs: [(&str, J); N]) -> Self {
        J::Object(pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect())
    }

    fn from_value(value: &Value) -> Self {
        match value {
            Value::Null => J::Null,
            Value::Bool(v) => J::Bool(*v),
            Value::Number(n) => {
                if let Some(i) = n.as_i64()
                    && n.as_f64().is_some_and(|f| f == i as f64)
                    && !n.to_string().contains('.')
                {
                    return J::Int(i);
                }
                J::Float(n.as_f64().unwrap_or(0.0))
            }
            Value::String(s) => J::Str(s.clone()),
            Value::Array(items) => J::Array(items.iter().map(J::from_value).collect()),
            Value::Object(map) => J::Object(
                map.iter()
                    .map(|(k, v)| (k.clone(), J::from_value(v)))
                    .collect(),
            ),
        }
    }

    pub(crate) fn dump(&self, level: usize) -> String {
        match self {
            J::Null => "null".to_string(),
            J::Bool(v) => v.to_string(),
            J::Int(v) => v.to_string(),
            J::Float(v) => py_float(*v),
            J::Str(v) => crate::format::py_string(v),
            J::Array(items) if items.is_empty() => "[]".to_string(),
            J::Object(pairs) if pairs.is_empty() => "{}".to_string(),
            J::Array(items) => {
                let mut out = String::from("[\n");
                for (i, item) in items.iter().enumerate() {
                    out.push_str(&" ".repeat(level + 1));
                    out.push_str(&item.dump(level + 1));
                    if i + 1 != items.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                out.push_str(&" ".repeat(level));
                out.push(']');
                out
            }
            J::Object(pairs) => {
                let mut out = String::from("{\n");
                for (i, (key, value)) in pairs.iter().enumerate() {
                    out.push_str(&" ".repeat(level + 1));
                    out.push_str(&crate::format::py_string(key));
                    out.push_str(": ");
                    out.push_str(&value.dump(level + 1));
                    if i + 1 != pairs.len() {
                        out.push(',');
                    }
                    out.push('\n');
                }
                out.push_str(&" ".repeat(level));
                out.push('}');
                out
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The build step builds the benchmarks without running them, and the
    // timed step runs them, as Python's `run` does.
    #[test]
    fn builds_before_it_times() {
        let build = build_only(&BENCH);
        assert_eq!(build.last(), Some(&"--no-run"));
        assert_eq!(build[..BENCH.len()], BENCH);
        assert!(!BENCH.contains(&"--no-run"));
    }
}
