//! `fnmatchcase` stays case-sensitive, matching Linux CPython.
//!
//! On macOS, `fnmatch.fnmatch` (and therefore `fnmatch.filter`) casefolds.
//! `admin/bench-report` uses that for "does this pattern name an operation"
//! and `fnmatch.fnmatchcase` for gap and proof rows. This crate uses the
//! case-sensitive rule for both, which is what Linux CPython does for both.

use std::process::Command;

use rind_bench_report::fnmatchcase;

#[test]
fn case_differs_from_macos_fnmatch_and_matches_fnmatchcase() {
    let pairs = [
        ("sha256", "sha256", true),
        ("sha256/64B", "sha256/*", true),
        ("SHA256", "sha256", false),
        ("Sha256/64B", "sha256/*", false),
        ("x25519-ecdh", "X25519-ecdh", false),
        ("AES256-gcm/16KB", "aes256-gcm/*", false),
        ("p256-ecdh", "p[0-9]*", true),
        ("P256-ecdh", "p[0-9]*", false),
    ];
    for (name, pattern, expect) in pairs {
        assert_eq!(
            fnmatchcase(name, pattern),
            expect,
            "{name:?} against {pattern:?}"
        );
    }

    let script = r#"
import fnmatch, json, sys
pairs = json.loads(sys.argv[1])
# fnmatchcase is the Linux rule. fnmatch.fnmatch casefolds only on macOS.
print(json.dumps([[n, p, fnmatch.fnmatchcase(n, p)] for n, p, _ in pairs]))
"#;
    let payload = serde_json::to_string(
        &pairs
            .iter()
            .map(|(n, p, e)| (*n, *p, *e))
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let output = Command::new("python3")
        .arg("-c")
        .arg(script)
        .arg(payload)
        .output()
        .expect("python3");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let python: Vec<(String, String, bool)> = serde_json::from_slice(&output.stdout).unwrap();
    for (name, pattern, expect) in python {
        assert_eq!(
            fnmatchcase(&name, &pattern),
            expect,
            "fnmatchcase {name:?} {pattern:?}"
        );
    }
}
