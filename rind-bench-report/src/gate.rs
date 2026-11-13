//! `gate`: fail only on a gap the previous scheduled run showed too.

use std::path::Path;

use indexmap::IndexMap;

use crate::error::{Error, Result};
use crate::format::significant;
use crate::gaps::{GapHit, gaps_of, tier_column, tier_row};
use crate::paths::Paths;
use crate::schema::{BenchArtifact, Tier, TierDocument, load_bench_artifact};
use crate::tables::{BASELINES, SLOWER, baselines};

pub struct GateReport {
    pub stdout: String,
    pub error: Option<String>,
}

pub fn gate(dir: &Path, previous: Option<&Path>, paths: &Paths) -> Result<GateReport> {
    let tiers = run_tiers(dir)?;
    let previous_gaps = match previous {
        Some(dir) => Some(gaps_of(&[], Some(&run_tiers(dir)?))?),
        None => None,
    };
    let entries = crate::gaps::load_gap_patterns(&paths.gaps())?;
    let mut unbaselined = Vec::new();
    for tier in &tiers.tiers {
        let column = tier_column(tier)?;
        for (key, libs) in &tier.benchmarks {
            if tier_row(key)?.is_some()
                && !libs.keys().any(|lib| baselines().contains(&lib.as_str()))
            {
                unbaselined.push(format!("{key} on {column}"));
            }
        }
    }
    unbaselined.sort();
    unbaselined.dedup();
    let mut found = gaps_of(&[], Some(&tiers))?;
    found.sort_by(|a, b| (&a.operation, &a.place).cmp(&(&b.operation, &b.place)));
    let mut undecided = Vec::new();
    let mut once = Vec::new();
    for hit in found {
        if entries.iter().any(|entry| entry.covers(&hit)) {
            continue;
        }
        let cell = format!(
            "{} on {} ({:.2}× {})",
            hit.operation, hit.place, hit.ratio, hit.library
        );
        if previous_gaps.as_ref().is_none_or(|gaps| {
            gaps.iter()
                .any(|old| old.operation == hit.operation && old.place == hit.place)
        }) {
            undecided.push(cell);
        } else {
            once.push(cell);
        }
    }
    let mut stdout = String::new();
    if !unbaselined.is_empty() {
        stdout.push_str(&format!(
            "No baseline, so no ratio: {}.\n\n",
            unbaselined.join(", ")
        ));
    }
    if !once.is_empty() {
        stdout.push_str(&format!(
            "Over {SLOWER}× without a decision, but not in the previous run: {}.\n\n",
            once.join(", ")
        ));
    }
    let error = if !undecided.is_empty() {
        stdout.push_str(&format!(
            "Over {SLOWER}× without a decision in benchmarks/gaps.toml: {}.\n",
            undecided.join(", ")
        ));
        Some(format!(
            "{count} gaps over {SLOWER}× without a decision in benchmarks/gaps.toml",
            count = undecided.len()
        ))
    } else {
        stdout.push_str(&format!(
            "Every gap over {SLOWER}× has a decision in benchmarks/gaps.toml.\n"
        ));
        None
    };
    Ok(GateReport { stdout, error })
}

pub fn run_tiers(directory: &Path) -> Result<TierDocument> {
    let mut paths = Vec::new();
    let read = std::fs::read_dir(directory).map_err(|err| {
        Error::new(format!(
            "no bench-*/bench-results.json in {}: {err}",
            directory.display()
        ))
    })?;
    for entry in read.filter_map(|entry| entry.ok()) {
        let nested = entry.path().join("bench-results.json");
        if nested.is_file() {
            paths.push(nested);
        }
    }
    paths.sort();
    if paths.is_empty() {
        return Err(Error::new(format!(
            "no bench-*/bench-results.json in {}",
            directory.display()
        )));
    }
    let mut tiers = Vec::new();
    for path in paths {
        tiers.push(tier_from_artifact(&load_bench_artifact(&path)?)?);
    }
    Ok(TierDocument {
        schema: 1,
        run: 0,
        url: String::new(),
        commit: String::new(),
        date: String::new(),
        tiers,
        extra: IndexMap::new(),
    })
}

fn tier_from_artifact(saved: &BenchArtifact) -> Result<Tier> {
    let mut benchmarks: IndexMap<String, IndexMap<String, f64>> = IndexMap::new();
    for point in &saved.results {
        let parts: Vec<&str> = point.id.split('/').collect();
        let Some(lib) = parts
            .iter()
            .copied()
            .find(|part| *part == "rind" || BASELINES.contains(part))
        else {
            continue;
        };
        let key = parts
            .iter()
            .map(|part| if *part == lib { "*" } else { *part })
            .collect::<Vec<_>>()
            .join("/");
        benchmarks
            .entry(key)
            .or_default()
            .insert(lib.to_string(), significant(point.ns));
    }
    Ok(Tier {
        target: saved.target.clone(),
        portable: saved.portable,
        tier: saved.tier.clone(),
        cpu: saved.cpu.clone(),
        avx512: saved.avx512,
        benchmarks,
        extra: IndexMap::new(),
    })
}

trait Covers {
    fn covers(&self, hit: &GapHit) -> bool;
}

impl Covers for crate::gaps::GapPattern {
    fn covers(&self, hit: &GapHit) -> bool {
        crate::gaps::covers(&self.operations, &self.on, &hit.operation, &hit.place)
    }
}
