//! Schema 1 host files, tier documents, and nightly `bench-results.json` artifacts.
//!
//! Unknown object keys land in an [`indexmap::IndexMap`], which keeps the file's
//! key order. That avoids enabling `serde_json`'s `preserve_order` feature, which
//! would change map order for every other crate in the workspace.

use std::fs;
use std::path::Path;

use indexmap::IndexMap;
use serde::Deserialize;
use serde::Serialize;
use serde_json::{Map, Value};

use crate::error::{Error, Result};
use crate::tables::hosts;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Loaded<T> {
    pub value: T,
    #[serde(skip)]
    pub raw: Value,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HostResult {
    pub schema: u64,
    pub host: String,
    pub commit: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub started: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cpu: Option<CpuInfo>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub os: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub toolchain: Option<Toolchain>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub libraries: Option<IndexMap<String, IndexMap<String, String>>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rind_cpu: Option<RindCpu>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub refused: Option<IndexMap<String, Vec<String>>>,
    pub status: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub finished: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub criterion_args: Option<Vec<String>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load: Option<Load>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub results: Option<Vec<TimingRow>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub build_cost: Option<BuildCost>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub upstream_commit: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fork_commit: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub patches: Option<Vec<Patch>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hardware_commit: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub harness_commit: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub firmware_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub runs: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub warmup: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub iterations: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub metric_units: Option<String>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CpuInfo {
    pub model: String,
    pub arch: String,
    pub logical_cpus: u32,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Toolchain {
    pub rustc: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cargo: Option<String>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RindCpu {
    #[serde(default)]
    pub cpuid: IndexMap<String, i64>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Load {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub limit_cpus: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub busy_cpus_before_build: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub busy_cpus_before_run: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub other_busy_cpus_during_run: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub noisy: Option<bool>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingRow {
    pub operation: String,
    pub library: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<String>,
    pub ns: f64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ns_low: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ns_high: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub throughput: Option<Value>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cycles: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cycles_per_byte: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub run_spread_pct: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub runs_ns: Option<Vec<f64>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub spread_is: Option<String>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Patch {
    pub name: String,
    pub sha256: String,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildCost {
    pub status: String,
    pub started: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub host: Option<BuildHost>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub runs: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub builds: Option<Vec<BuildMeasurement>>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildHost {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hostname: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub os: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arch: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cpu: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cpus: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub jobs: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub rustc: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub cc: Option<String>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildMeasurement {
    pub name: String,
    pub seconds: Vec<f64>,
    pub median_seconds: f64,
    pub cpu_seconds: Vec<f64>,
    pub median_cpu_seconds: f64,
    pub stripped_bytes: u64,
    pub tools: Vec<String>,
    pub packages: Vec<String>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TierDocument {
    pub schema: u64,
    pub run: u64,
    pub url: String,
    pub commit: String,
    pub date: String,
    pub tiers: Vec<Tier>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Tier {
    pub target: String,
    pub portable: bool,
    pub tier: String,
    pub cpu: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub avx512: Option<bool>,
    pub benchmarks: IndexMap<String, IndexMap<String, f64>>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

/// One `bench-*/bench-results.json` from the nightly workflow.
/// The workflow writes `schema: 1`; the report's own tests omit it.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchArtifact {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub schema: Option<u64>,
    pub target: String,
    pub portable: bool,
    pub tier: String,
    pub cpu: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub avx512: Option<bool>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub commit: Option<String>,
    pub results: Vec<BenchPoint>,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchPoint {
    pub id: String,
    pub ns: f64,
    #[serde(default, flatten)]
    pub extra: IndexMap<String, Value>,
}

const STATUSES: &[&str] = &["ok", "busy", "failed", "unreachable"];

pub fn load_host_file(path: &Path) -> Result<Loaded<HostResult>> {
    let text =
        fs::read_to_string(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    parse_host(&text, &path.display().to_string())
}

pub fn parse_host(text: &str, path: &str) -> Result<Loaded<HostResult>> {
    let raw: Value = serde_json::from_str(text).map_err(|e| Error::new(format!("{path}: {e}")))?;
    let obj = raw
        .as_object()
        .ok_or_else(|| Error::new(format!("{path}: expected an object")))?;
    match obj.get("schema") {
        Some(v) if is_one(v) => {}
        _ => return Err(Error::new(format!("{path}: schema must be 1"))),
    }
    require_string(obj, "host", path)?;
    require_string(obj, "commit", path)?;
    let status = require_string(obj, "status", path)?;
    if !STATUSES.contains(&status) {
        return Err(Error::new(format!("{path}: unknown status {status}")));
    }
    let value: HostResult =
        serde_json::from_value(raw.clone()).map_err(|e| Error::new(format!("{path}: {e}")))?;
    if value.schema != 1 {
        return Err(Error::new(format!("{path}: schema must be 1")));
    }
    if status == "ok" {
        require_some(&value.started, path, "started")?;
        require_some(&value.finished, path, "finished")?;
        require_some(&value.cpu, path, "cpu")?;
        require_some(&value.os, path, "os")?;
        require_some(&value.toolchain, path, "toolchain")?;
        require_some(&value.libraries, path, "libraries")?;
        require_some(&value.rind_cpu, path, "rind_cpu")?;
        if value.results.is_none() {
            return Err(Error::new(format!("{path}: missing results")));
        }
    } else {
        require_some(&value.reason, path, "reason")?;
    }
    if let Some(cost) = &value.build_cost {
        if cost.status == "ok" {
            require_some(&cost.host, path, "build_cost.host")?;
            require_some(&cost.builds, path, "build_cost.builds")?;
        } else if cost.status == "failed" {
            require_some(&cost.reason, path, "build_cost.reason")?;
        } else {
            return Err(Error::new(format!(
                "{path}: unknown build_cost status {}",
                cost.status
            )));
        }
    }
    Ok(Loaded { value, raw })
}

pub fn load_tier_file(path: &Path) -> Result<Loaded<TierDocument>> {
    let text =
        fs::read_to_string(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    parse_tier(&text, &path.display().to_string())
}

pub fn parse_tier(text: &str, path: &str) -> Result<Loaded<TierDocument>> {
    let raw: Value = serde_json::from_str(text).map_err(|e| Error::new(format!("{path}: {e}")))?;
    let obj = raw
        .as_object()
        .ok_or_else(|| Error::new(format!("{path}: expected an object")))?;
    match obj.get("schema") {
        Some(v) if is_one(v) => {}
        _ => return Err(Error::new(format!("{path}: schema must be 1"))),
    }
    for key in ["run", "url", "commit", "date", "tiers"] {
        if !obj.contains_key(key) {
            return Err(Error::new(format!("{path}: missing {key}")));
        }
    }
    let value: TierDocument =
        serde_json::from_value(raw.clone()).map_err(|e| Error::new(format!("{path}: {e}")))?;
    if value.schema != 1 {
        return Err(Error::new(format!("{path}: schema must be 1")));
    }
    if value.tiers.is_empty() {
        return Err(Error::new(format!("{path}: tiers are empty")));
    }
    Ok(Loaded { value, raw })
}

pub fn load_bench_artifact(path: &Path) -> Result<BenchArtifact> {
    let text =
        fs::read_to_string(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    let value: BenchArtifact =
        serde_json::from_str(&text).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    if let Some(schema) = value.schema
        && schema != 1
    {
        return Err(Error::new(format!("{}: schema must be 1", path.display())));
    }
    Ok(value)
}

/// Host files in `directory` whose names are in [`hosts`], in that order.
pub fn load_hosts(directory: &Path) -> Result<Vec<HostResult>> {
    let mut out = Vec::new();
    for spec in hosts() {
        let path = directory.join(format!("{}.json", spec.name));
        if path.is_file() {
            out.push(load_host_file(&path)?.value);
        }
    }
    Ok(out)
}

fn is_one(value: &Value) -> bool {
    match value {
        Value::Number(n) => n.as_u64() == Some(1) || n.as_f64() == Some(1.0),
        _ => false,
    }
}

fn require_string<'a>(obj: &'a Map<String, Value>, key: &str, path: &str) -> Result<&'a str> {
    match obj.get(key) {
        Some(Value::String(s)) if !s.is_empty() => Ok(s),
        Some(Value::String(_)) => Err(Error::new(format!("{path}: {key} is empty"))),
        Some(_) => Err(Error::new(format!("{path}: {key} must be a string"))),
        None => Err(Error::new(format!("{path}: missing {key}"))),
    }
}

fn require_some<T>(value: &Option<T>, path: &str, key: &str) -> Result<()> {
    if value.is_some() {
        Ok(())
    } else {
        Err(Error::new(format!("{path}: missing {key}")))
    }
}
