//! The cases in `admin/bench-report-test`, against this crate.

use std::collections::HashSet;
use std::path::PathBuf;
use std::process::Command;

use serde_json::json;

use crate::gaps::gaps_of;
use crate::gate::gate;
use crate::schema::{HostResult, TierDocument};
use crate::svg::{bin_of, header_lines, overview_svg, tier_cells};
use crate::tables::{SPEED_BINS, THEMES, operation_regex};
use crate::{Paths, VerifiedEntry};

fn host(
    name: &str,
    arch: &str,
    os: &str,
    cpuid: serde_json::Value,
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

fn hosts() -> Vec<HostResult> {
    vec![
        host(
            "nixos",
            "x86_64",
            "NixOS (Linux 6.18)",
            json!({"intel": 0, "adx": 1, "aes": 1, "vaes": 1, "avx2": 1, "sha": 1}),
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
            json!({"intel": 1, "adx": 1, "aes": 1, "vaes": 0, "avx2": 1, "sha": 0}),
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

fn entry(
    library: &str,
    operations: &[&str],
    arch: Option<&str>,
    cpu: Option<&[&str]>,
    os: Option<&str>,
    proof: &str,
) -> VerifiedEntry {
    VerifiedEntry {
        library: library.to_string(),
        operations: operations.iter().map(|item| (*item).to_string()).collect(),
        arch: arch.map(str::to_string),
        cpu: cpu.map(|items| items.iter().map(|item| (*item).to_string()).collect()),
        os: os.map(str::to_string),
        proof: proof.to_string(),
        link: "https://example.com".to_string(),
    }
}

fn verified() -> Vec<VerifiedEntry> {
    vec![
        entry(
            "rind",
            &["x25519-ecdh"],
            Some("x86_64"),
            Some(&["adx"]),
            None,
            "x86 proof",
        ),
        entry(
            "rind",
            &["aes256-gcm/*"],
            Some("x86_64"),
            Some(&["!vaes"]),
            None,
            "aes proof",
        ),
        entry("ring", &["x25519-ecdh"], None, None, None, "any-arch proof"),
        entry(
            "rind",
            &["x25519-ecdh"],
            Some("aarch64"),
            None,
            Some("linux"),
            "linux-only proof",
        ),
    ]
}

fn squares(svg: &str) -> Vec<String> {
    let mut out = Vec::new();
    for chunk in svg.split("<rect ").skip(1) {
        let Some((body, _)) = chunk.split_once("</rect>") else {
            continue;
        };
        let Some((_, after)) = body.split_once("<title>") else {
            continue;
        };
        let Some((title, _)) = after.split_once("</title>") else {
            continue;
        };
        out.push(title.to_string());
    }
    out
}

#[test]
fn overview_marks_each_measured_square() {
    let theme = THEMES.iter().find(|theme| theme.name == "light").unwrap();
    let svg = overview_svg(&hosts(), &verified(), theme);
    let titles = squares(&svg);
    assert_eq!(titles.len(), 9);
    assert!(svg.contains("left to right: nixos, nixos2, kixtop."));
    assert!(svg.contains(">OpenSSL<"));
    assert!(!svg.contains(">graviola<"));
    assert!(
        titles
            .iter()
            .any(|title| title == "X25519, OpenSSL on nixos: 300.00 µs, 10.00× the fastest")
    );
    assert!(titles.iter().any(|title| title
        == "X25519, ring on nixos: 33.00 µs, 1.10× the fastest; verified: any-arch proof"));
}

#[test]
fn verified_follows_cpu_and_os() {
    let theme = THEMES.iter().find(|theme| theme.name == "dark").unwrap();
    let mut titles: Vec<_> = squares(&overview_svg(&hosts(), &verified(), theme))
        .into_iter()
        .filter(|title| title.contains("verified"))
        .collect();
    titles.sort();
    assert_eq!(
        titles,
        vec![
            "AES-256-GCM seal, 16 KB, rind on nixos2: 2.00 µs, 1.00× the fastest; verified: aes proof".to_string(),
            "X25519, rind on nixos: 30.00 µs, 1.00× the fastest; verified: x86 proof".to_string(),
            "X25519, ring on kixtop: 40.00 µs, 2.00× the fastest; verified: any-arch proof".to_string(),
            "X25519, ring on nixos: 33.00 µs, 1.10× the fastest; verified: any-arch proof".to_string(),
        ]
    );
}

#[test]
fn dit_held_never_sets_the_fastest() {
    let mut everyone = hosts();
    everyone[2].results.as_mut().unwrap().push(
        serde_json::from_value(json!({
            "operation": "x25519-ecdh/{lib}",
            "library": "rind-dit-held",
            "ns": 10000.0
        }))
        .unwrap(),
    );
    everyone[2].results.as_mut().unwrap()[1].ns = 15000.0;
    let theme = THEMES.iter().find(|theme| theme.name == "light").unwrap();
    let svg = overview_svg(&everyone, &verified(), theme);
    assert!(svg.contains("rind is the fastest, or within 10% of it, in 3 of its 4 times"));
    let titles = squares(&svg);
    assert!(
        titles
            .iter()
            .any(|title| title == "X25519, rind (DIT held) on kixtop: 10.00 µs, 0.67× the fastest")
    );
    assert!(
        titles
            .iter()
            .any(|title| title == "X25519, rind on kixtop: 20.00 µs, 1.33× the fastest")
    );
    let gaps = gaps_of(&everyone, None).unwrap();
    assert_eq!(gaps.len(), 1);
    assert_eq!(
        (
            gaps[0].operation.as_str(),
            gaps[0].place.as_str(),
            gaps[0].library.as_str()
        ),
        ("x25519-ecdh", "kixtop", "ring")
    );
    assert!((gaps[0].ratio - 20000.0 / 15000.0).abs() < 1e-12);
    let on_macos = vec![entry("rind", &["x25519-ecdh"], None, None, None, "p")];
    let text = crate::report::host_table(&everyone[2], &on_macos).join("\n");
    assert!(text.contains("| Operation | rind | rind (DIT held) | ring |"));
    assert!(text.contains("| X25519 | 20.00 µs ✓ | 10.00 µs ✓ | 15.00 µs |"));
    assert_eq!(
        header_lines("rind (DIT held)"),
        ["rind".to_string(), "(DIT held)".to_string()]
    );
}

#[test]
fn report_states_what_is_not_measured() {
    let files =
        crate::report::generate(std::path::Path::new("."), &hosts(), None, &verified(), &[])
            .unwrap();
    let md = files
        .iter()
        .find(|(path, _)| path.ends_with("BENCHMARKS.md"))
        .unwrap()
        .1
        .as_str();
    assert!(md.contains("on three machines"));
    assert!(md.contains("Not timed on `kixtop`: full handshake, X25519MLKEM768, "));
    assert!(md.contains("Not measured yet: `desktop`, `ovh-iad`, `ovh-sea`."));
    assert!(!md.contains("`desktop` |"));
    assert!(md.contains("No nightly results yet."));
    let svgs: Vec<_> = files
        .iter()
        .filter(|(path, _)| path.extension().is_some_and(|ext| ext == "svg"))
        .map(|(path, _)| path.file_name().unwrap().to_str().unwrap().to_string())
        .collect();
    let mut expected = Vec::new();
    for name in ["overview", "nixos", "nixos2", "kixtop"] {
        expected.push(format!("{name}.svg"));
        expected.push(format!("{name}-dark.svg"));
    }
    let mut got = svgs;
    got.sort();
    expected.sort();
    assert_eq!(got, expected);
    assert!(md.contains("| Operation | rind | aws-lc-rs | ring | OpenSSL |"));
    assert!(md.contains("| X25519 | 30.00 µs ✓ | - | 33.00 µs ✓ | 300.00 µs |"));
}

// It runs `admin/bench-report` under python3, which a workspace `cargo test`
// cannot count on, as on Windows, so `sh/bench-parity.sh` runs it.
#[test]
#[ignore = "needs python3 and admin/bench-report; sh/bench-parity.sh runs it"]
fn host_script_matches_python() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..");
    let py = Command::new("python3")
        .current_dir(&root)
        .arg("-c")
        .arg(
            "import importlib.machinery,importlib.util\n\
             loader=importlib.machinery.SourceFileLoader('b','admin/bench-report')\n\
             spec=importlib.util.spec_from_loader('b',loader)\n\
             m=importlib.util.module_from_spec(spec); loader.exec_module(m)\n\
             print(m.host_script('nixos','/tmp/work','echo hi'), end='')\n\
             print('---')\n\
             print(m.host_script('ovh-iad','/tmp/work dir','echo hi'), end='')\n",
        )
        .output()
        .unwrap();
    assert!(
        py.status.success(),
        "{}",
        String::from_utf8_lossy(&py.stderr)
    );
    let text = String::from_utf8(py.stdout).unwrap();
    let mut parts = text.split("---\n");
    let nixos = crate::host_script("nixos", "/tmp/work", "echo hi").unwrap();
    let leased = crate::host_script("ovh-iad", "/tmp/work dir", "echo hi").unwrap();
    assert_eq!(parts.next().unwrap(), nixos);
    assert_eq!(parts.next().unwrap(), leased);
}

#[test]
fn fastest_bin_holds_within_ten_percent() {
    assert_eq!(bin_of(1.0, SPEED_BINS), 0);
    assert_eq!(bin_of(1.1, SPEED_BINS), 0);
    assert_eq!(bin_of(1.11, SPEED_BINS), 1);
    assert_eq!(bin_of(10.0, SPEED_BINS), SPEED_BINS.len());
}

#[test]
fn tier_cell_is_the_worst_ranked_benchmark() {
    let tiers: TierDocument = serde_json::from_value(json!({
        "schema": 1,
        "run": 1,
        "url": "https://github.com/moq-dev/rind/actions/runs/1",
        "commit": "fedcba9876543210fedcba9876543210fedcba98",
        "date": "2026-11-02T18:00:00Z",
        "tiers": [
            {
                "target": "x86_64-unknown-linux-gnu",
                "portable": false,
                "tier": "",
                "cpu": "AMD EPYC 7763",
                "benchmarks": {
                    "sha256/*/64B": {"rind": 100.0, "aws-lc-rs": 105.0, "ring": 95.0},
                    "sha256/*/16KB": {"rind": 1000.0, "aws-lc-rs": 990.0, "ring": 1200.0},
                    "rsa2048-key-generation/*": {"rind": 9e7, "aws-lc-rs": 1e7},
                    "jwt-es256-sign/*/load": {"rind": 9e3, "aws-lc-rs": 1e3}
                }
            },
            {
                "target": "x86_64-unknown-linux-gnu",
                "portable": true,
                "tier": "no-aes",
                "cpu": "AMD EPYC 9V74",
                "benchmarks": {"aes128-gcm/*/1350B": {"rind": 500.0, "aws-lc-rs": 1000.0}}
            }
        ]
    }))
    .unwrap();
    let cells = tier_cells(&tiers).unwrap();
    let (key, point) = cells
        .get(&("SHA-256".to_string(), "x86_64".to_string()))
        .unwrap();
    assert_eq!(key, "sha256/*/64B");
    assert!((point.ratio - 100.0 / 95.0).abs() < 1e-12);
    let aes = cells
        .get(&("AES-GCM".to_string(), "no AES-NI".to_string()))
        .unwrap();
    assert!((aes.1.ratio - 0.5).abs() < 1e-12);
    assert!(!cells.contains_key(&("RSA signatures".to_string(), "x86_64".to_string())));
    assert_eq!(cells.len(), 2);
}

#[test]
fn operation_regex_drops_a_refused_library() {
    let mut refused = HashSet::new();
    refused.insert("graviola");
    let re = regex::Regex::new(&operation_regex(&refused)).unwrap();
    for row in [
        "x25519-ecdh/rind",
        "p256-ecdh/p256-rustcrypto",
        "aes128-gcm/openssl/32B",
    ] {
        assert!(re.is_match(row), "{row}");
    }
    for row in [
        "x25519-ecdh/graviola",
        "aes128-gcm/graviola/32B",
        "x25519-ecdh/rind/extra",
    ] {
        assert!(!re.is_match(row), "{row}");
    }
}

#[test]
fn gate_stdout_matches_python_on_the_script_fixture() {
    let dir = std::env::temp_dir().join(format!("rind-gate-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    write_run(&dir.join("now/bench-x"), 100.0, 100.0, true);
    write_run(&dir.join("then/bench-x"), 100.0, 80.0, false);
    std::fs::create_dir_all(dir.join("benchmarks")).unwrap();
    std::fs::create_dir_all(dir.join("admin")).unwrap();
    std::fs::write(
        dir.join("benchmarks/gaps.toml"),
        "[[gap]]\noperations = [\"sha256/*\"]\non = [\"x86_64\"]\nreason = \"r\"\n",
    )
    .unwrap();
    let script = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../admin/bench-report");
    std::fs::copy(script, dir.join("admin/bench-report")).unwrap();
    let report = gate(&dir.join("now"), Some(&dir.join("then")), &Paths::new(&dir)).unwrap();
    assert!(report.error.is_none(), "{:?}", report.error);
    let py = Command::new("python3")
        .arg("-c")
        .arg(include_str!("behavior_gate.py"))
        .arg(&dir)
        .output()
        .unwrap();
    assert!(
        py.status.success(),
        "{}",
        String::from_utf8_lossy(&py.stderr)
    );
    assert_eq!(report.stdout, String::from_utf8(py.stdout).unwrap());
    let _ = std::fs::remove_dir_all(&dir);
}

fn write_run(dir: &std::path::Path, sha256: f64, chacha: f64, avx512: bool) {
    std::fs::create_dir_all(dir).unwrap();
    let saved = json!({
        "target": "x86_64-unknown-linux-gnu",
        "portable": false,
        "tier": "",
        "cpu": "c",
        "avx512": avx512,
        "results": [
            {"id": "sha256/rind/64B", "ns": sha256},
            {"id": "sha256/ring/64B", "ns": 80.0},
            {"id": "chacha20poly1305/rind/32B", "ns": chacha},
            {"id": "chacha20poly1305/aws-lc-rs/32B", "ns": 80.0},
            {"id": "x25519-ecdh/rind", "ns": 1.0}
        ]
    });
    std::fs::write(
        dir.join("bench-results.json"),
        serde_json::to_vec(&saved).unwrap(),
    )
    .unwrap();
}

const NON_ASCII_MODEL: &str = "Apple M4 — café";
const NON_ASCII_NOTE: &str = "DIT ~30 µs; shield ✓; snowman ☃; emoji 😀; line\nbreak; quote\"; back\\slash; bell\u{0007}; del\u{007f}";

/// A run record holding the characters `json.dumps` escapes, as `run`
/// writes it.
fn non_ascii_dump() -> String {
    let (model, note) = (NON_ASCII_MODEL, NON_ASCII_NOTE);
    crate::run::J::Object(vec![
        ("schema".into(), crate::run::J::Int(1)),
        ("host".into(), crate::run::J::Str("kixtop".into())),
        (
            "cpu".into(),
            crate::run::J::Object(vec![
                ("model".into(), crate::run::J::Str(model.into())),
                ("arch".into(), crate::run::J::Str("aarch64".into())),
            ]),
        ),
        ("note".into(), crate::run::J::Str(note.into())),
        ("ns".into(), crate::run::J::Float(1.5)),
        ("ok".into(), crate::run::J::Bool(true)),
        (
            "tags".into(),
            crate::run::J::Array(vec![
                crate::run::J::Str("µ".into()),
                crate::run::J::Str("×".into()),
            ]),
        ),
    ])
    .dump(0)
}

#[test]
fn json_ensure_ascii_matches_the_fixture() {
    // A checkout that converts line endings, as Git on Windows does by
    // default, has CRLF in the fixture where the encoder writes LF.
    let fixture = include_str!("../tests/fixtures/non-ascii.json").replace("\r\n", "\n");
    assert_eq!(non_ascii_dump(), fixture, "committed fixture");
}

// The fixture above is a `json.dumps` of the same values; this re-runs it
// under python3, which a workspace `cargo test` cannot count on, so
// `sh/bench-parity.sh` runs it.
#[test]
#[ignore = "needs python3; sh/bench-parity.sh runs it"]
fn json_ensure_ascii_matches_python() {
    let (model, note) = (NON_ASCII_MODEL, NON_ASCII_NOTE);
    let dumped = non_ascii_dump();
    let spec =
        serde_json::to_vec(&json!({"model": model, "note": note, "tags": ["µ", "×"]})).unwrap();
    let py = Command::new("python3")
        .arg("-c")
        .arg(
            "import json,sys\n\
             spec=json.load(sys.stdin)\n\
             obj={'schema':1,'host':'kixtop','cpu':{'model':spec['model'],'arch':'aarch64'},\n\
             'note':spec['note'],'ns':1.5,'ok':True,'tags':spec['tags']}\n\
             sys.stdout.write(json.dumps(obj, indent=1))",
        )
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let output = {
        use std::io::Write;
        let mut child = py;
        child.stdin.take().unwrap().write_all(&spec).unwrap();
        child.wait_with_output().unwrap()
    };
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(dumped, String::from_utf8(output.stdout).unwrap());
}
