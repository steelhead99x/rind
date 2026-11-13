//! `benchmarks/verified.toml`, checked the way `load_verified` checks it.

use std::fs;
use std::path::Path;

use crate::error::{Error, Result};
use crate::format::{fnmatchcase, sorted_comma};
use crate::paths::relpath;
use crate::schema::HostResult;
use crate::tables::{COLUMNS, cpu_features, known_arch, operations, row_name};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedEntry {
    pub library: String,
    pub operations: Vec<String>,
    pub arch: Option<String>,
    pub cpu: Option<Vec<String>>,
    pub os: Option<String>,
    pub proof: String,
    pub link: String,
}

const REQUIRED: &[&str] = &["library", "operations", "proof", "link"];
const OPTIONAL: &[&str] = &["arch", "cpu", "os"];

pub fn load_verified(path: &Path, root: &Path) -> Result<Vec<VerifiedEntry>> {
    let text =
        fs::read_to_string(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    parse_verified(&text, path, root)
}

pub fn parse_verified(text: &str, path: &Path, root: &Path) -> Result<Vec<VerifiedEntry>> {
    let doc: toml::Value =
        toml::from_str(text).map_err(|e| Error::new(format!("{}: {e}", relpath(path, root))))?;
    let table = doc
        .as_table()
        .ok_or_else(|| Error::new(format!("{}: expected a table", relpath(path, root))))?;
    let entries = match table.get("verified") {
        None => return Ok(Vec::new()),
        Some(value) => value.as_array().ok_or_else(|| {
            Error::new(format!(
                "{}: verified must be an array",
                relpath(path, root)
            ))
        })?,
    };
    let rows: Vec<String> = operations().iter().map(|op| row_name(op)).collect();
    let mut out = Vec::new();
    for (i, entry) in entries.iter().enumerate() {
        let where_ = format!("{}: entry {}", relpath(path, root), i + 1);
        let table = entry
            .as_table()
            .ok_or_else(|| Error::new(format!("{where_}: expected a table")))?;
        let keys: Vec<&str> = table.keys().map(String::as_str).collect();
        let unknown: Vec<String> = keys
            .iter()
            .filter(|k| !REQUIRED.contains(k) && !OPTIONAL.contains(k))
            .map(|k| (*k).to_string())
            .collect();
        if !unknown.is_empty() {
            return Err(Error::new(format!(
                "{where_}: unknown keys {}",
                sorted_comma(unknown)
            )));
        }
        let missing: Vec<String> = REQUIRED
            .iter()
            .filter(|k| !table.contains_key(**k))
            .map(|k| (*k).to_string())
            .collect();
        if !missing.is_empty() {
            return Err(Error::new(format!(
                "{where_}: missing {}",
                sorted_comma(missing)
            )));
        }
        let library = toml_str(table, "library", &where_)?;
        if !COLUMNS.iter().any(|(name, _)| *name == library) {
            return Err(Error::new(format!("{where_}: unknown library {library}")));
        }
        let arch = optional_str(table, "arch", &where_)?;
        let arch_for_features = arch.as_deref().unwrap_or("x86_64");
        if !known_arch(arch_for_features) {
            return Err(Error::new(format!(
                "{where_}: unknown arch {}",
                arch.as_deref().unwrap_or("x86_64")
            )));
        }
        let cpu = match table.get("cpu") {
            None => None,
            Some(value) => Some(toml_str_array(value, &where_, "cpu")?),
        };
        if cpu.is_some() && arch.is_none() {
            return Err(Error::new(format!("{where_}: CPU features need an arch")));
        }
        if let Some(features) = &cpu {
            let known = cpu_features(arch.as_deref().expect("arch checked"));
            for feature in features {
                let bare = feature.strip_prefix('!').unwrap_or(feature);
                if !known.contains(&bare) {
                    return Err(Error::new(format!(
                        "{where_}: unknown {} CPU feature {feature}",
                        arch.as_deref().unwrap_or("")
                    )));
                }
            }
        }
        let os = optional_str(table, "os", &where_)?;
        let os_for_check = os.as_deref().unwrap_or("linux");
        if os_for_check != "linux" && os_for_check != "macos" {
            return Err(Error::new(format!(
                "{where_}: unknown os {}",
                os.as_deref().unwrap_or("linux")
            )));
        }
        let patterns = toml_str_array(
            table.get("operations").expect("checked"),
            &where_,
            "operations",
        )?;
        for pattern in &patterns {
            if !rows.iter().any(|row| fnmatchcase(row, pattern)) {
                return Err(Error::new(format!(
                    "{where_}: {pattern} names no operation"
                )));
            }
        }
        let proof = toml_str(table, "proof", &where_)?;
        let link = toml_str(table, "link", &where_)?;
        if !link.starts_with("https://") {
            return Err(Error::new(format!("{where_}: the link is not https")));
        }
        out.push(VerifiedEntry {
            library,
            operations: patterns,
            arch,
            cpu,
            os,
            proof,
            link,
        });
    }
    Ok(out)
}

pub fn proof_for<'a>(
    verified: &'a [VerifiedEntry],
    library: &str,
    row: &str,
    host: &HostResult,
) -> Option<&'a VerifiedEntry> {
    let arch = host
        .cpu
        .as_ref()
        .map(|cpu| host_arch(&cpu.arch))
        .unwrap_or("");
    let os = host.os.as_deref().map(host_os).unwrap_or("linux");
    let cpuid = host.rind_cpu.as_ref().map(|cpu| &cpu.cpuid);
    for entry in verified {
        if entry.library != library {
            continue;
        }
        if entry.arch.as_deref().unwrap_or(arch) != arch {
            continue;
        }
        if entry.os.as_deref().unwrap_or(os) != os {
            continue;
        }
        if let Some(features) = &entry.cpu {
            let ok = features.iter().all(|feature| {
                let (neg, name) = match feature.strip_prefix('!') {
                    Some(rest) => (true, rest),
                    None => (false, feature.as_str()),
                };
                let value = cpuid.and_then(|map| map.get(name)).copied();
                value == Some(if neg { 0 } else { 1 })
            });
            if !ok {
                continue;
            }
        }
        if entry
            .operations
            .iter()
            .any(|pattern| fnmatchcase(row, pattern))
        {
            return Some(entry);
        }
    }
    None
}

pub fn host_arch(arch: &str) -> &str {
    match arch {
        "arm64" => "aarch64",
        "amd64" => "x86_64",
        other => other,
    }
}

pub fn host_os(os: &str) -> &'static str {
    if os.starts_with("macOS") {
        "macos"
    } else {
        "linux"
    }
}

fn toml_str(
    table: &toml::map::Map<String, toml::Value>,
    key: &str,
    where_: &str,
) -> Result<String> {
    match table.get(key).and_then(toml::Value::as_str) {
        Some(value) => Ok(value.to_string()),
        None => Err(Error::new(format!("{where_}: {key} must be a string"))),
    }
}

fn optional_str(
    table: &toml::map::Map<String, toml::Value>,
    key: &str,
    where_: &str,
) -> Result<Option<String>> {
    match table.get(key) {
        None => Ok(None),
        Some(value) => value
            .as_str()
            .map(|s| Some(s.to_string()))
            .ok_or_else(|| Error::new(format!("{where_}: {key} must be a string"))),
    }
}

fn toml_str_array(value: &toml::Value, where_: &str, key: &str) -> Result<Vec<String>> {
    let array = value
        .as_array()
        .ok_or_else(|| Error::new(format!("{where_}: {key} must be an array")))?;
    let mut out = Vec::new();
    for item in array {
        let text = item
            .as_str()
            .ok_or_else(|| Error::new(format!("{where_}: {key} must be an array of strings")))?;
        out.push(text.to_string());
    }
    Ok(out)
}
