//! `benchmarks/gaps.toml` and the gaps a host or a nightly tier measures.

use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use indexmap::IndexMap;
use regex::Regex;

use crate::error::{Error, Result};
use crate::format::{fnmatchcase, sorted_comma};
use crate::paths::relpath;
use crate::schema::{HostResult, Tier, TierDocument};
use crate::tables::{
    BASELINES, SLOWER, TIER_ROWS, UNRANKED, host, is_variant, row_name, tier_name_of, tier_names,
};

#[derive(Debug, Clone, PartialEq)]
pub struct GapHit {
    pub operation: String,
    pub place: String,
    pub ratio: f64,
    pub library: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DecidedGap {
    pub operations: Vec<String>,
    pub on: Vec<String>,
    pub quest: Option<String>,
    pub reason: Option<String>,
    pub covered: Vec<GapHit>,
}

const GAP_KEYS: &[&str] = &["operations", "on", "quest", "reason"];

pub fn load_gaps(
    hosts: &[HostResult],
    tiers: Option<&TierDocument>,
    path: &Path,
    root: &Path,
) -> Result<Vec<DecidedGap>> {
    let text =
        fs::read_to_string(path).map_err(|e| Error::new(format!("{}: {e}", path.display())))?;
    parse_gaps(&text, hosts, tiers, path, root)
}

pub fn parse_gaps(
    text: &str,
    hosts: &[HostResult],
    tiers: Option<&TierDocument>,
    path: &Path,
    root: &Path,
) -> Result<Vec<DecidedGap>> {
    let doc: toml::Value =
        toml::from_str(text).map_err(|e| Error::new(format!("{}: {e}", relpath(path, root))))?;
    let table = doc
        .as_table()
        .ok_or_else(|| Error::new(format!("{}: expected a table", relpath(path, root))))?;
    let entries = match table.get("gap") {
        None => Vec::new(),
        Some(value) => value
            .as_array()
            .ok_or_else(|| Error::new(format!("{}: gap must be an array", relpath(path, root))))?
            .clone(),
    };
    let mut found = gaps_of(hosts, tiers)?;
    let mut measured: Vec<&str> = hosts.iter().map(|host| host.host.as_str()).collect();
    if let Some(doc) = tiers {
        for tier in &doc.tiers {
            measured.push(tier_name(tier)?);
        }
    }
    let mut out = Vec::new();
    for (i, entry) in entries.iter().enumerate() {
        let where_ = format!("{}: entry {}", relpath(path, root), i + 1);
        let table = entry
            .as_table()
            .ok_or_else(|| Error::new(format!("{where_}: expected a table")))?;
        let unknown: Vec<String> = table
            .keys()
            .filter(|key| !GAP_KEYS.contains(&key.as_str()))
            .cloned()
            .collect();
        if !unknown.is_empty() {
            return Err(Error::new(format!(
                "{where_}: unknown keys {}",
                sorted_comma(unknown)
            )));
        }
        if !table.contains_key("operations") || !table.contains_key("on") {
            return Err(Error::new(format!("{where_}: needs operations and on")));
        }
        let has_quest = table.contains_key("quest");
        let has_reason = table.contains_key("reason");
        if has_quest == has_reason {
            return Err(Error::new(format!(
                "{where_}: needs a quest or a reason, not both"
            )));
        }
        let quest = match table.get("quest") {
            Some(value) => Some(
                value
                    .as_str()
                    .ok_or_else(|| Error::new(format!("{where_}: quest must be a string")))?
                    .to_string(),
            ),
            None => None,
        };
        if let Some(quest) = &quest
            && !(quest.starts_with("/quest/") && root.join(quest.trim_start_matches('/')).is_file())
        {
            return Err(Error::new(format!("{where_}: no quest at {quest}")));
        }
        let reason = match table.get("reason") {
            Some(value) => Some(
                value
                    .as_str()
                    .ok_or_else(|| Error::new(format!("{where_}: reason must be a string")))?
                    .to_string(),
            ),
            None => None,
        };
        let operations = str_array(
            table.get("operations").expect("checked"),
            &where_,
            "operations",
        )?;
        let on = str_array(table.get("on").expect("checked"), &where_, "on")?;
        for place in &on {
            let known_host = host(place).is_some();
            let known_tier = tier_names().any(|name| name == place);
            if !known_host && !known_tier {
                return Err(Error::new(format!("{where_}: no host or tier {place}")));
            }
            if known_host && !hosts.iter().any(|host| host.host == *place) {
                return Err(Error::new(format!(
                    "{where_}: {place} is not measured; update or remove the entry"
                )));
            }
        }
        let mut covered = Vec::new();
        found.retain(|hit| {
            if covers(&operations, &on, &hit.operation, &hit.place) {
                covered.push(hit.clone());
                false
            } else {
                true
            }
        });
        if covered.is_empty() && on.iter().any(|place| measured.contains(&place.as_str())) {
            return Err(Error::new(format!(
                "{where_}: names no gap over 10%; update or remove the entry"
            )));
        }
        if !covered.is_empty() {
            out.push(DecidedGap {
                operations,
                on,
                quest,
                reason,
                covered,
            });
        }
    }
    if !found.is_empty() {
        found.sort_by(|a, b| (&a.operation, &a.place).cmp(&(&b.operation, &b.place)));
        let listed = found
            .iter()
            .map(|hit| {
                format!(
                    "{} on {} ({:.2}× {})",
                    hit.operation, hit.place, hit.ratio, hit.library
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        return Err(Error::new(format!(
            "gaps over 10% without a decision in {}: {listed}",
            relpath(path, root)
        )));
    }
    Ok(out)
}

pub fn covers(operations: &[String], on: &[String], operation: &str, place: &str) -> bool {
    on.iter().any(|item| item == place)
        && operations
            .iter()
            .any(|pattern| fnmatchcase(operation, pattern))
}

pub fn gaps_of(hosts: &[HostResult], tiers: Option<&TierDocument>) -> Result<Vec<GapHit>> {
    let mut out = Vec::new();
    for host in hosts {
        let Some(results) = &host.results else {
            continue;
        };
        for (row, libs) in times(results) {
            let Some((ratio, best)) = rival_ratio(&libs) else {
                continue;
            };
            if ratio > SLOWER {
                out.push(GapHit {
                    operation: row,
                    place: host.host.clone(),
                    ratio,
                    library: best,
                });
            }
        }
    }
    if let Some(doc) = tiers {
        for tier in &doc.tiers {
            let column = tier_name(tier)?;
            for (key, libs) in &tier.benchmarks {
                let Some((ratio, best)) = baseline_ratio(libs) else {
                    continue;
                };
                if ratio > SLOWER && tier_row(key)?.is_some() {
                    out.push(GapHit {
                        operation: key.clone(),
                        place: column.to_string(),
                        ratio,
                        library: best,
                    });
                }
            }
        }
    }
    Ok(out)
}

pub fn tier_name(tier: &Tier) -> Result<&'static str> {
    tier_name_of(&tier.target, tier.portable, &tier.tier).ok_or_else(|| {
        Error::new(format!(
            "nightly results name an unknown tier: {} {}",
            tier.target, tier.tier
        ))
    })
}

pub fn tier_column(tier: &Tier) -> Result<String> {
    let mut column = tier_name(tier)?.to_string();
    if column == "x86_64"
        && let Some(avx512) = tier.avx512
    {
        column.push_str(if avx512 { " AVX-512" } else { " VAES AVX2" });
    }
    Ok(column)
}

/// The CPU-tier row a nightly id belongs to. `Ok(None)` is an [`UNRANKED`] id.
pub fn tier_row(key: &str) -> Result<Option<&'static str>> {
    for pair in tier_regexes() {
        if pair.0.is_match(key) {
            return Ok(Some(pair.1));
        }
    }
    if unranked_regexes().iter().any(|re| re.is_match(key)) {
        return Ok(None);
    }
    Err(Error::new(format!(
        "nightly benchmark {key} matches neither a TIER_ROWS row nor UNRANKED"
    )))
}

fn tier_regexes() -> &'static [(Regex, &'static str)] {
    static ROWS: OnceLock<Vec<(Regex, &'static str)>> = OnceLock::new();
    ROWS.get_or_init(|| {
        TIER_ROWS
            .iter()
            .map(|(name, pattern)| {
                (
                    Regex::new(&format!("^(?:{pattern})")).expect(pattern),
                    *name,
                )
            })
            .collect()
    })
    .as_slice()
}

fn unranked_regexes() -> &'static [Regex] {
    static ROWS: OnceLock<Vec<Regex>> = OnceLock::new();
    ROWS.get_or_init(|| {
        UNRANKED
            .iter()
            .map(|(pattern, _)| Regex::new(&format!("^(?:{pattern})")).expect(pattern))
            .collect()
    })
    .as_slice()
}

fn times(results: &[crate::schema::TimingRow]) -> Vec<(String, IndexMap<String, f64>)> {
    let mut rows: Vec<(String, IndexMap<String, f64>)> = Vec::new();
    for result in results {
        let row = row_name(&result.operation);
        if let Some((_, libs)) = rows.iter_mut().find(|(name, _)| *name == row) {
            libs.insert(result.library.clone(), result.ns);
        } else {
            let mut libs = IndexMap::new();
            libs.insert(result.library.clone(), result.ns);
            rows.push((row, libs));
        }
    }
    rows
}

fn rival_ratio(libs: &IndexMap<String, f64>) -> Option<(f64, String)> {
    let rind = *libs.get("rind")?;
    let mut best_lib = None;
    let mut best_ns = f64::INFINITY;
    for (lib, ns) in libs {
        if lib == "rind" || is_variant(lib) {
            continue;
        }
        if *ns < best_ns {
            best_ns = *ns;
            best_lib = Some(lib.clone());
        }
    }
    let best_lib = best_lib?;
    Some((rind / best_ns, best_lib))
}

fn baseline_ratio(libs: &IndexMap<String, f64>) -> Option<(f64, String)> {
    let rind = *libs.get("rind")?;
    let mut best_lib = None;
    let mut best_ns = f64::INFINITY;
    for (lib, ns) in libs {
        if BASELINES.contains(&lib.as_str()) && *ns < best_ns {
            best_ns = *ns;
            best_lib = Some(lib.clone());
        }
    }
    let best_lib = best_lib?;
    Some((rind / best_ns, best_lib))
}

fn str_array(value: &toml::Value, where_: &str, key: &str) -> Result<Vec<String>> {
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
