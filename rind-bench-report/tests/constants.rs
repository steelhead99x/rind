//! The Python script is the source of the tables. This fails when they drift.

use std::collections::HashSet;
use std::process::Command;

use rind_bench_report::*;
use serde_json::{Map, Value, json};

fn python_tables() -> Value {
    let root = workspace_root();
    let script = r#"
import importlib.machinery, importlib.util, json, os, sys
root = sys.argv[1]
path = os.path.join(root, "admin", "bench-report")
loader = importlib.machinery.SourceFileLoader("bench_report", path)
spec = importlib.util.spec_from_loader("bench_report", loader)
br = importlib.util.module_from_spec(spec)
loader.exec_module(br)
rows = [op.replace("/{lib}", "") for op in br.OPERATIONS]
patterns = [
    "x25519-ecdh", "aes256-gcm/*", "sha256/*/64B", "p[0-9]*", "rsa*",
    "aes*-gcm*", "p521-ecdsa-verify*", "aes256-gcm/8B", "aes256-gcm/16KB",
    "chacha20poly1305/*/16KB", "*",
]
samples = [0.0, 1.0, 1.5, 2.5, 9.9996, 9999.5, 233731.1471129501, 1e-7, 1e20, 0.00012345, 99.995, 100.0, 80.0, 30000.0, 1.105, 10.0/12.0]
payload = {
    "operations": br.OPERATIONS,
    "libraries": list(br.LIBRARIES.items()),
    "columns": list(br.COLUMNS.items()),
    "variants": list(br.VARIANTS.items()),
    "crates": [[name, crates] for name, crates in br.CRATES.items()],
    "builds": list(br.BUILDS.items()),
    "criterion_args": br.CRITERION_ARGS,
    "slower": br.SLOWER,
    "busy_share": br.BUSY_SHARE,
    "repo": br.REPO,
    "remote_dir": br.REMOTE_DIR,
    "lease_held": br.LEASE_HELD,
    "copy_failed": br.COPY_FAILED,
    "baselines": br.BASELINES,
    "hosts": [
        {"name": name, "jobs": spec["jobs"], "ssh": spec.get("ssh"), "lease": spec.get("lease"), "note": spec.get("note")}
        for name, spec in br.HOSTS.items()
    ],
    "required": [[lib, arch, feats] for lib, arches in br.REQUIRED.items() for arch, feats in arches.items()],
    "cpu_features": {arch: sorted(feats) for arch, feats in br.CPU_FEATURES.items()},
    "tiers": [[target, portable, tier, name] for (target, portable, tier), name in br.TIERS],
    "tier_rows": [[name, pat] for name, pat in br.TIER_ROWS],
    "unranked": [[pat, why] for pat, why in br.UNRANKED],
    "speed_bins": br.SPEED_BINS,
    "speed_labels": br.SPEED_LABELS,
    "tier_bins": br.TIER_BINS,
    "tier_labels": br.TIER_LABELS,
    "speed_colors": br.SPEED,
    "font": br.FONT,
    "themes": br.THEMES,
    "regex": br.operation_regex(),
    "regex_graviola": br.operation_regex({"graviola": ["adx"]}),
    "labels": {row: br.label(row) for row in rows},
    "fnmatch": {pat: [row for row in rows if __import__("fnmatch").fnmatchcase(row, pat)] for pat in patterns},
    "human": [[n, br.human(n)] for n in samples],
    "significant": [[n, br.significant(n)] for n in samples],
    "operation_of": {
        "x25519-ecdh/rind": br.operation_of("x25519-ecdh/rind"),
        "aes128-gcm/openssl/32B": br.operation_of("aes128-gcm/openssl/32B"),
        "not-a-benchmark": br.operation_of("not-a-benchmark"),
    },
}
json.dump(payload, sys.stdout)
"#;
    let output = Command::new("python3")
        .arg("-c")
        .arg(script)
        .arg(root)
        .output()
        .expect("python3");
    assert!(
        output.status.success(),
        "python: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).expect("python json")
}

fn rust_tables() -> Value {
    let mut refused = HashSet::new();
    refused.insert("graviola");
    let rows: Vec<String> = operations().iter().map(|op| row_name(op)).collect();
    let patterns = [
        "x25519-ecdh",
        "aes256-gcm/*",
        "sha256/*/64B",
        "p[0-9]*",
        "rsa*",
        "aes*-gcm*",
        "p521-ecdsa-verify*",
        "aes256-gcm/8B",
        "aes256-gcm/16KB",
        "chacha20poly1305/*/16KB",
        "*",
    ];
    let mut fnmatch = Map::new();
    for pattern in patterns {
        let matched: Vec<_> = rows
            .iter()
            .filter(|row| fnmatchcase(row, pattern))
            .cloned()
            .collect();
        fnmatch.insert(pattern.to_string(), json!(matched));
    }
    let samples = [
        0.0,
        1.0,
        1.5,
        2.5,
        9.9996,
        9999.5,
        233731.1471129501,
        1e-7,
        1e20,
        0.00012345,
        99.995,
        100.0,
        80.0,
        30000.0,
        1.105,
        10.0 / 12.0,
    ];
    let themes = Map::from_iter(THEMES.iter().map(|theme| {
        (
            theme.name.to_string(),
            json!({
                "ink": theme.ink,
                "muted": theme.muted,
                "rule": theme.rule,
                "speed": theme.speed,
                "tier": theme.tier,
            }),
        )
    }));
    json!({
        "operations": operations(),
        "libraries": libraries(),
        "columns": columns(),
        "variants": variants(),
        "crates": crates_for().iter().map(|c| json!([c.library, c.crates])).collect::<Vec<_>>(),
        "builds": builds(),
        "criterion_args": criterion_args(),
        "slower": SLOWER,
        "busy_share": BUSY_SHARE,
        "repo": REPO,
        "remote_dir": REMOTE_DIR,
        "lease_held": LEASE_HELD,
        "copy_failed": COPY_FAILED,
        "baselines": baselines(),
        "hosts": hosts().iter().map(|h| json!({
            "name": h.name,
            "jobs": h.jobs,
            "ssh": h.ssh,
            "lease": h.lease,
            "note": h.note,
        })).collect::<Vec<_>>(),
        "required": [
            ["graviola", "x86_64", required_features("graviola", "x86_64")],
            ["graviola", "aarch64", required_features("graviola", "aarch64")],
        ],
        "cpu_features": {
            "x86_64": sorted(cpu_feature_list("x86_64")),
            "aarch64": sorted(cpu_feature_list("aarch64")),
        },
        "tiers": tiers().iter().map(|t| json!([t.target, t.portable, t.tier, t.name])).collect::<Vec<_>>(),
        "tier_rows": TIER_ROWS.iter().map(|(n, p)| json!([n, p])).collect::<Vec<_>>(),
        "unranked": UNRANKED.iter().map(|(p, w)| json!([p, w])).collect::<Vec<_>>(),
        "speed_bins": SPEED_BINS,
        "speed_labels": SPEED_LABELS,
        "tier_bins": TIER_BINS,
        "tier_labels": TIER_LABELS,
        "speed_colors": SPEED_COLORS,
        "font": FONT,
        "themes": themes,
        "regex": operation_regex(&HashSet::new()),
        "regex_graviola": operation_regex(&refused),
        "labels": Map::from_iter(rows.iter().map(|row| (row.clone(), json!(label(row))))),
        "fnmatch": fnmatch,
        "human": samples.iter().map(|n| json!([n, human(*n)])).collect::<Vec<_>>(),
        "significant": samples.iter().map(|n| json!([n, significant(*n)])).collect::<Vec<_>>(),
        "operation_of": {
            "x25519-ecdh/rind": operation_of("x25519-ecdh/rind").map(|(op, lib)| json!([op, lib])),
            "aes128-gcm/openssl/32B": operation_of("aes128-gcm/openssl/32B").map(|(op, lib)| json!([op, lib])),
            "not-a-benchmark": Value::Null,
        },
    })
}

fn cpu_feature_list(arch: &str) -> Vec<String> {
    // Re-list through the public checker by probing is not available; the
    // snapshot compares the sorted features the validator accepts.
    let mut names = Vec::new();
    let probes = [
        "adx",
        "aes",
        "avx",
        "avx2",
        "avx512bw",
        "avx512dq",
        "avx512f",
        "avx512ifma",
        "avx512vbmi",
        "avx512vbmi2",
        "avx512vl",
        "bmi1",
        "bmi2",
        "dit",
        "intel",
        "movbe",
        "neon",
        "pclmulqdq",
        "pmull",
        "popcnt",
        "sha",
        "sha2",
        "sha3",
        "sse4.1",
        "ssse3",
        "vaes",
        "vpclmulqdq",
    ];
    for name in probes {
        if rind_bench_report::cpu_features(arch).contains(&name) {
            names.push(name.to_string());
        }
    }
    names
}

fn sorted(mut names: Vec<String>) -> Vec<String> {
    names.sort();
    names
}

fn same(expect: &Value, got: &Value, path: &str) -> std::result::Result<(), String> {
    match (expect, got) {
        (Value::Number(a), Value::Number(b)) => {
            let (Some(x), Some(y)) = (a.as_f64(), b.as_f64()) else {
                return Err(format!("{path}: {a} != {b}"));
            };
            if x == y {
                Ok(())
            } else {
                Err(format!("{path}: python {x:?} rust {y:?}"))
            }
        }
        (Value::Array(a), Value::Array(b)) => {
            if a.len() != b.len() {
                return Err(format!("{path}: len {} != {}", a.len(), b.len()));
            }
            for (i, (x, y)) in a.iter().zip(b).enumerate() {
                same(x, y, &format!("{path}[{i}]"))?;
            }
            Ok(())
        }
        (Value::Object(a), Value::Object(b)) => {
            let mut keys: Vec<_> = a.keys().chain(b.keys()).cloned().collect();
            keys.sort();
            keys.dedup();
            for key in keys {
                match (a.get(&key), b.get(&key)) {
                    (Some(x), Some(y)) => same(x, y, &format!("{path}.{key}"))?,
                    (Some(_), None) => return Err(format!("{path}.{key}: missing from rust")),
                    (None, Some(_)) => return Err(format!("{path}.{key}: missing from python")),
                    (None, None) => {}
                }
            }
            Ok(())
        }
        (x, y) if x == y => Ok(()),
        (x, y) => Err(format!("{path}:\n python: {x}\n rust:   {y}")),
    }
}

// It runs `admin/bench-report` under python3 (3.11 or later, for
// `tomllib`), which a workspace `cargo test` cannot count on, as on Windows,
// so `just check`'s bench check runs it after checking for python3.
#[test]
#[ignore = "needs python3 and admin/bench-report; just check's bench check runs it"]
fn tables_match_the_python_script() {
    if let Err(diff) = same(&python_tables(), &rust_tables(), "$") {
        panic!("table drift at {diff}");
    }
}
