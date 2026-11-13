//! Schema 1 files, verified.toml, and gaps.toml.

use std::fs;
use std::path::Path;

use rind_bench_report::*;
use serde_json::{Value, json};

struct Temp(std::path::PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
impl Temp {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "rind-bench-report-{}-{}.toml",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::write(&path, text).unwrap();
        Self(path)
    }
    fn path(&self) -> &Path {
        &self.0
    }
}

fn entry(fields: &[(&str, Option<&str>)]) -> String {
    let mut base = vec![
        ("library", Some(r#""rind""#)),
        ("operations", Some(r#"["x25519-ecdh"]"#)),
        ("arch", Some(r#""x86_64""#)),
        ("proof", Some(r#""p""#)),
        ("link", Some(r#""https://example.com""#)),
    ];
    for (key, value) in fields {
        if let Some(slot) = base.iter_mut().find(|(k, _)| k == key) {
            slot.1 = *value;
        } else {
            base.push((key, *value));
        }
    }
    let mut text = String::from("[[verified]]\n");
    for (key, value) in base {
        if let Some(value) = value {
            text.push_str(key);
            text.push_str(" = ");
            text.push_str(value);
            text.push('\n');
        }
    }
    text
}

fn host(
    name: &str,
    arch: &str,
    os: &str,
    cpuid: Value,
    results: &[(&str, &str, f64)],
) -> HostResult {
    let rows: Vec<_> = results
        .iter()
        .map(|(op, lib, ns)| json!({"operation": op, "library": lib, "ns": ns}))
        .collect();
    serde_json::from_value(json!({
        "schema": 1,
        "host": name,
        "commit": "0123456789abcdef0123456789abcdef01234567",
        "started": "2026-11-03T02:00:00+00:00",
        "status": "ok",
        "cpu": {"model": format!("{name} CPU"), "arch": arch, "logical_cpus": 8},
        "os": os,
        "toolchain": {"rustc": "rustc 1.98.1"},
        "rind_cpu": {"cpuid": cpuid},
        "load": {"noisy": false},
        "results": rows,
    }))
    .unwrap()
}

fn zen3() -> Value {
    json!({"intel": 0, "adx": 1, "aes": 1, "vaes": 1, "avx2": 1, "sha": 1})
}

fn coffee() -> Value {
    json!({"intel": 1, "adx": 1, "aes": 1, "vaes": 0, "avx2": 1, "sha": 0})
}

fn sample_hosts() -> Vec<HostResult> {
    vec![
        host(
            "nixos",
            "x86_64",
            "NixOS (Linux 6.18)",
            zen3(),
            &[
                ("x25519-ecdh/{lib}", "rind", 30000.0),
                ("x25519-ecdh/{lib}", "ring", 33000.0),
                ("x25519-ecdh/{lib}", "openssl", 300000.0),
                ("aes256-gcm/{lib}/16KB", "rind", 1000.0),
                ("aes256-gcm/{lib}/16KB", "aws-lc-rs", 1500.0),
            ],
        ),
        host(
            "nixos2",
            "x86_64",
            "NixOS (Linux 6.18)",
            coffee(),
            &[
                ("aes256-gcm/{lib}/16KB", "rind", 2000.0),
                ("aes256-gcm/{lib}/16KB", "aws-lc-rs", 2100.0),
            ],
        ),
        host(
            "kixtop",
            "arm64",
            "macOS 15.1 (24.1.0)",
            json!({"aes": 1, "pmull": 1, "sha2": 1, "sha3": 1}),
            &[
                ("x25519-ecdh/{lib}", "rind", 20000.0),
                ("x25519-ecdh/{lib}", "ring", 40000.0),
            ],
        ),
    ]
}

fn gap_hosts() -> (Vec<HostResult>, TierDocument) {
    let mut hosts = sample_hosts();
    hosts[0].results.as_mut().unwrap()[1].ns = 20000.0;
    let tiers: TierDocument = serde_json::from_value(json!({
        "schema": 1,
        "run": 1,
        "url": "https://github.com/moq-dev/rind/actions/runs/1",
        "commit": "fedcba9876543210fedcba9876543210fedcba98",
        "date": "2026-11-02T18:00:00Z",
        "tiers": [{
            "target": "x86_64-unknown-linux-gnu",
            "portable": false,
            "tier": "",
            "cpu": "AMD EPYC 7763",
            "benchmarks": {"sha256/*/64B": {"rind": 100.0, "ring": 80.0}}
        }]
    }))
    .unwrap();
    (hosts, tiers)
}

const X25519: &[(&str, &str)] = &[
    ("operations", r#"["x25519-ecdh"]"#),
    ("on", r#"["nixos"]"#),
    ("quest", r#""/quest/m3/README.md""#),
];
const SHA256: &[(&str, &str)] = &[
    ("operations", r#"["sha256/*/64B"]"#),
    ("on", r#"["x86_64"]"#),
    ("reason", r#""r""#),
];

fn gap_text(entries: &[&[(&str, &str)]]) -> String {
    let mut text = String::new();
    for entry in entries {
        text.push_str("[[gap]]\n");
        for (key, value) in *entry {
            text.push_str(key);
            text.push_str(" = ");
            text.push_str(value);
            text.push('\n');
        }
    }
    text
}

#[test]
fn committed_host_and_tier_files_parse() {
    let paths = Paths::discover();
    let hosts = load_hosts(&paths.data()).unwrap();
    assert_eq!(hosts.len(), 6);
    assert!(
        hosts
            .iter()
            .all(|host| host.status == "ok" && host.schema == 1)
    );
    let tiers = load_tier_file(&paths.data().join("tiers.json")).unwrap();
    assert_eq!(tiers.value.schema, 1);
    assert!(!tiers.value.tiers.is_empty());
}

#[test]
fn reader_keeps_side_host_fields_and_rejects_a_bad_schema() {
    let ok = r#"{
        "schema": 1,
        "host": "orin",
        "commit": "0123456789abcdef0123456789abcdef01234567",
        "started": "2026-11-13T00:00:00+00:00",
        "finished": "2026-11-13T00:01:00+00:00",
        "cpu": {"model": "m", "arch": "aarch64", "logical_cpus": 8},
        "os": "Linux",
        "toolchain": {"rustc": "rustc"},
        "libraries": {},
        "rind_cpu": {"cpuid": {}},
        "status": "ok",
        "upstream_commit": "abc",
        "patches": [{"name": "0001", "sha256": "deadbeef"}],
        "results": [{
            "operation": "x25519-ecdh/{lib}",
            "library": "rind",
            "ns": 1.5,
            "cycles": 10.0,
            "spread_is": "runs",
            "board_note": "quiet"
        }],
        "firmware_note": "kept"
    }"#;
    let loaded = parse_host(ok, "mem.json").unwrap();
    assert_eq!(loaded.value.upstream_commit.as_deref(), Some("abc"));
    assert_eq!(loaded.value.patches.as_ref().unwrap()[0].name, "0001");
    assert_eq!(loaded.value.results.as_ref().unwrap()[0].cycles, Some(10.0));
    assert_eq!(
        loaded.value.results.as_ref().unwrap()[0]
            .extra
            .get("board_note")
            .and_then(Value::as_str),
        Some("quiet")
    );
    assert_eq!(
        loaded
            .value
            .extra
            .get("firmware_note")
            .and_then(Value::as_str),
        Some("kept")
    );
    assert!(loaded.raw.get("firmware_note").is_some());

    let busy = r#"{"schema":1,"host":"orin","commit":"c","status":"busy","reason":"held"}"#;
    let busy = parse_host(busy, "busy.json").unwrap();
    assert_eq!(busy.value.reason.as_deref(), Some("held"));

    assert!(
        parse_host(
            r#"{"schema":2,"host":"h","commit":"c","status":"busy","reason":"r"}"#,
            "s"
        )
        .is_err()
    );
    assert!(
        parse_host(
            r#"{"schema":1,"commit":"c","status":"busy","reason":"r"}"#,
            "s"
        )
        .is_err()
    );
    assert!(
        parse_host(
            r#"{"schema":1,"host":"h","commit":"c","status":"nope","reason":"r"}"#,
            "s"
        )
        .is_err()
    );
    let bad_ns = r#"{
        "schema": 1, "host": "h", "commit": "c", "status": "ok",
        "started": "t", "finished": "t",
        "cpu": {"model": "m", "arch": "x86_64", "logical_cpus": 1},
        "os": "Linux", "toolchain": {"rustc": "r"}, "libraries": {}, "rind_cpu": {"cpuid": {}},
        "results": [{"operation": "x25519-ecdh/{lib}", "library": "rind", "ns": "fast"}]
    }"#;
    assert!(parse_host(bad_ns, "bad.json").is_err());
}

#[test]
fn verified_accepts_and_refuses_like_the_script() {
    let root = workspace_root();
    let good = entry(&[("cpu", Some(r#"["adx", "!vaes"]"#))]);
    let path = Temp::new(&good);
    assert_eq!(
        parse_verified(
            &fs::read_to_string(path.path()).unwrap(),
            path.path(),
            &root
        )
        .unwrap()
        .len(),
        1
    );
    let no_arch = entry(&[("arch", None)]);
    let path = Temp::new(&no_arch);
    assert_eq!(
        parse_verified(
            &fs::read_to_string(path.path()).unwrap(),
            path.path(),
            &root
        )
        .unwrap()
        .len(),
        1
    );

    let bad = [
        entry(&[("library", Some(r#""rustls""#))]),
        entry(&[("operations", Some(r#"["x25519"]"#))]),
        entry(&[("operations", Some(r#"["aes256-gcm/8B"]"#))]),
        entry(&[("arch", Some(r#""armv7""#))]),
        entry(&[("arch", None), ("cpu", Some(r#"["adx"]"#))]),
        entry(&[("cpu", Some(r#"["sha2"]"#))]),
        entry(&[("os", Some(r#""windows""#))]),
        entry(&[("link", Some(r#""http://example.com""#))]),
        entry(&[("proof", None)]),
        entry(&[("platform", Some(r#""x86_64""#))]),
    ];
    for text in bad {
        let path = Temp::new(&text);
        assert!(
            parse_verified(
                &fs::read_to_string(path.path()).unwrap(),
                path.path(),
                &root
            )
            .is_err(),
            "{text}"
        );
    }
    load_verified(&Paths::discover().verified(), &root).unwrap();
}

#[test]
fn gaps_match_the_script_on_synthetic_and_committed_data() {
    let root = workspace_root();
    let (hosts, tiers) = gap_hosts();
    let text = gap_text(&[X25519, SHA256]);
    let path = Temp::new(&text);
    let gaps = parse_gaps(
        &fs::read_to_string(path.path()).unwrap(),
        &hosts,
        Some(&tiers),
        path.path(),
        &root,
    )
    .unwrap();
    let ratios: Vec<f64> = gaps
        .iter()
        .flat_map(|gap| gap.covered.iter().map(|hit| hit.ratio))
        .collect();
    assert_eq!(ratios.len(), 2);
    assert!((ratios[0] - 1.5).abs() < 1e-9);
    assert!((ratios[1] - 1.25).abs() < 1e-9);

    for entries in [
        gap_text(&[X25519]).as_str(),
        gap_text(&[SHA256]).as_str(),
        "",
    ] {
        let path = Temp::new(entries);
        assert!(
            parse_gaps(
                &fs::read_to_string(path.path()).unwrap(),
                &hosts,
                Some(&tiers),
                path.path(),
                &root
            )
            .is_err(),
            "{entries}"
        );
    }

    let stale = [
        gap_text(&[
            X25519,
            SHA256,
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("on", r#"["kixtop"]"#),
                ("reason", r#""r""#),
            ],
        ]),
        gap_text(&[
            X25519,
            SHA256,
            &[
                ("operations", r#"["aes256-gcm/16KB"]"#),
                ("on", r#"["nixos"]"#),
                ("reason", r#""r""#),
            ],
        ]),
        gap_text(&[
            X25519,
            SHA256,
            &[
                ("operations", r#"["sha256/*/16KB"]"#),
                ("on", r#"["x86_64"]"#),
                ("reason", r#""r""#),
            ],
        ]),
        gap_text(&[
            X25519,
            SHA256,
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("on", r#"["desktop"]"#),
                ("reason", r#""r""#),
            ],
        ]),
    ];
    for text in stale {
        let path = Temp::new(&text);
        assert!(
            parse_gaps(
                &fs::read_to_string(path.path()).unwrap(),
                &hosts,
                Some(&tiers),
                path.path(),
                &root
            )
            .is_err()
        );
    }

    let malformed = [
        // Both a quest and a reason.
        gap_text(&[
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("on", r#"["nixos"]"#),
                ("quest", r#""/quest/m3/README.md""#),
                ("reason", r#""r""#),
            ],
            SHA256,
        ]),
        gap_text(&[
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("on", r#"["nixos"]"#),
                ("quest", r#""/quest/m3/missing.md""#),
            ],
            SHA256,
        ]),
        gap_text(&[
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("on", r#"["nixos"]"#),
                ("quest", r#""/README.md""#),
            ],
            SHA256,
        ]),
        gap_text(&[
            &[("operations", r#"["x25519-ecdh"]"#), ("on", r#"["nixos"]"#)],
            SHA256,
        ]),
        gap_text(&[
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("quest", r#""/quest/m3/README.md""#),
            ],
            SHA256,
        ]),
        gap_text(&[
            &[
                ("operations", r#"["x25519-ecdh"]"#),
                ("on", r#"["nixos"]"#),
                ("quest", r#""/quest/m3/README.md""#),
                ("host", r#""nixos""#),
            ],
            SHA256,
        ]),
    ];
    for text in malformed {
        let path = Temp::new(&text);
        assert!(
            parse_gaps(
                &fs::read_to_string(path.path()).unwrap(),
                &hosts,
                Some(&tiers),
                path.path(),
                &root
            )
            .is_err(),
            "{text}"
        );
    }

    let paths = Paths::discover();
    let committed = load_hosts(&paths.data()).unwrap();
    let tier_file = load_tier_file(&paths.data().join("tiers.json")).unwrap();
    load_gaps(
        &committed,
        Some(&tier_file.value),
        &paths.gaps(),
        &paths.root,
    )
    .unwrap();
}

#[test]
fn tier_rows_rank_aead_open_and_refuse_an_unknown_id() {
    assert!(tier_row("aes256-gcm-open/*/16KB").unwrap().is_some());
    assert!(tier_row("chacha20poly1305-open/*/16KB").unwrap().is_some());
    assert!(tier_row("rsa2048-key-generation/*").unwrap().is_none());
    assert!(tier_row("md6/*/32B").is_err());
}
