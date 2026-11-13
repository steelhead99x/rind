//! `nightly`: save the latest scheduled bench run as `benchmarks/data/tiers.json`.

use std::fs;
use std::process::Command;

use serde_json::Value;

use crate::error::{Error, Result};
use crate::gate::run_tiers;
use crate::paths::Paths;
use crate::run::J;
use crate::tables::{REPO, tiers};

pub fn nightly(paths: &Paths) -> Result<()> {
    let list = output(&[
        "gh",
        "run",
        "list",
        "--repo",
        REPO,
        "--workflow",
        "bench.yml",
        "--branch",
        "main",
        "--event",
        "schedule",
        "--limit",
        "20",
        "--json",
        "databaseId,headSha,createdAt,url,status",
    ])?;
    let runs: Vec<Value> =
        serde_json::from_str(&list).map_err(|err| Error::new(err.to_string()))?;
    let scratch = paths.root.join(".tmp/bench-report/nightly");
    let mut incomplete = Vec::new();
    for run in runs {
        if run.get("status").and_then(Value::as_str) != Some("completed") {
            continue;
        }
        let _ = fs::remove_dir_all(&scratch);
        let id = run.get("databaseId").and_then(Value::as_u64).unwrap_or(0);
        let status = Command::new("gh")
            .args([
                "run",
                "download",
                &id.to_string(),
                "--repo",
                REPO,
                "--pattern",
                "bench-*",
                "--dir",
            ])
            .arg(&scratch)
            .status()
            .map_err(|err| Error::new(err.to_string()))?;
        if !status.success() {
            continue;
        }
        let saved = match run_tiers(&scratch) {
            Ok(doc) => doc.tiers,
            Err(_) => continue,
        };
        let have: std::collections::HashSet<_> = saved
            .iter()
            .map(|tier| (tier.target.as_str(), tier.portable, tier.tier.as_str()))
            .collect();
        let missing: Vec<_> = tiers()
            .iter()
            .filter(|spec| !have.contains(&(spec.target, spec.portable, spec.tier)))
            .map(|spec| spec.name)
            .collect();
        if !missing.is_empty() {
            incomplete.push(format!("{id} lacks {}", missing.join(", ")));
            continue;
        }
        let mut ordered = saved;
        ordered.sort_by_key(|tier| {
            tiers()
                .iter()
                .position(|spec| {
                    spec.target == tier.target
                        && spec.portable == tier.portable
                        && spec.tier == tier.tier
                })
                .unwrap_or(usize::MAX)
        });
        let mut tier_values = Vec::new();
        for tier in &ordered {
            let mut pairs = vec![
                ("target".to_string(), J::Str(tier.target.clone())),
                ("portable".to_string(), J::Bool(tier.portable)),
                ("tier".to_string(), J::Str(tier.tier.clone())),
                ("cpu".to_string(), J::Str(tier.cpu.clone())),
            ];
            if let Some(avx512) = tier.avx512 {
                pairs.push(("avx512".to_string(), J::Bool(avx512)));
            }
            let benches = tier
                .benchmarks
                .iter()
                .map(|(key, libs)| {
                    let libs = libs
                        .iter()
                        .map(|(lib, ns)| (lib.clone(), J::Float(*ns)))
                        .collect();
                    (key.clone(), J::Object(libs))
                })
                .collect();
            pairs.push(("benchmarks".to_string(), J::Object(benches)));
            tier_values.push(J::Object(pairs));
        }
        let body = J::Object(vec![
            ("schema".to_string(), J::Int(1)),
            (
                "run".to_string(),
                J::Int(i64::try_from(id).unwrap_or(i64::MAX)),
            ),
            (
                "url".to_string(),
                J::Str(
                    run.get("url")
                        .and_then(Value::as_str)
                        .unwrap_or("")
                        .to_string(),
                ),
            ),
            (
                "commit".to_string(),
                J::Str(
                    run.get("headSha")
                        .and_then(Value::as_str)
                        .unwrap_or("")
                        .to_string(),
                ),
            ),
            (
                "date".to_string(),
                J::Str(
                    run.get("createdAt")
                        .and_then(Value::as_str)
                        .unwrap_or("")
                        .to_string(),
                ),
            ),
            ("tiers".to_string(), J::Array(tier_values)),
        ])
        .dump(0);
        fs::create_dir_all(paths.data()).map_err(|err| Error::new(err.to_string()))?;
        fs::write(paths.data().join("tiers.json"), format!("{body}\n"))
            .map_err(|err| Error::new(err.to_string()))?;
        let _ = fs::remove_dir_all(&scratch);
        eprintln!("bench-report: tiers from run {id}");
        return Ok(());
    }
    let mut message = "no completed nightly bench run on main timed every tier".to_string();
    for item in incomplete {
        message.push_str(&format!("; run {item}"));
    }
    Err(Error::new(message))
}

fn output(args: &[&str]) -> Result<String> {
    let output = Command::new(args[0])
        .args(&args[1..])
        .output()
        .map_err(|err| Error::new(err.to_string()))?;
    if !output.status.success() {
        return Err(Error::new(
            String::from_utf8_lossy(&output.stderr).trim().to_string(),
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}
