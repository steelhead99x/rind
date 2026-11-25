// Records the rind commit, target, rustc and the compared crates' versions.
include!("src/ops.rs");
include!("src/deny.rs");
use std::process::Command;
fn main() {
    // RIND_DEVBENCH_DENY: refuse a list that would leave a feature enabled that
    // the report calls denied, and hand the library the checked ids.
    println!("cargo:rerun-if-env-changed=RIND_DEVBENCH_DENY");
    let deny = std::env::var("RIND_DEVBENCH_DENY").unwrap_or_default();
    let ids = if deny.is_empty() {
        vec![]
    } else {
        let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
        let ids = parse_denies(&deny, &arch).unwrap_or_else(|e| panic!("{e}"));
        let flags = std::env::var("CARGO_ENCODED_RUSTFLAGS").unwrap_or_default();
        if !denies_take_effect(&flags) {
            panic!("RIND_DEVBENCH_DENY is set but rind is built without --cfg rind_cpu_disable, so it may deny nothing (build-ios.sh adds the flag)");
        }
        ids
    };
    println!("cargo:rustc-env=DEVBENCH_DENY_IDS={}", ids.join(","));
    let out = |c: &mut Command| c.output().ok().filter(|o| o.status.success()).map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string());
    let mut commit = out(Command::new("git").args(["-C", "..", "rev-parse", "HEAD"])).unwrap_or_else(|| "unknown".into());
    // rind or the bench files changed from the commit: say so.
    if Command::new("git").args(["-C", "..", "diff", "--quiet", "HEAD", "--", "rind", "rind-bench", "rind-rustls", "rind-jsonwebtoken"]).status().map(|s| !s.success()).unwrap_or(true) {
        commit.push_str("-dirty");
    }
    println!("cargo:rustc-env=DEVBENCH_RIND_COMMIT={commit}");
    println!("cargo:rustc-env=DEVBENCH_TARGET={}", std::env::var("TARGET").unwrap());
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    println!("cargo:rustc-env=DEVBENCH_RUSTC={}", out(Command::new(rustc).arg("-V")).unwrap_or_default());
    let lock = std::fs::read_to_string("Cargo.lock").unwrap_or_default();
    let mut vers: Vec<(String, String)> = vec![];
    let mut name = String::new();
    for line in lock.lines() {
        if let Some(n) = line.strip_prefix("name = ") { name = n.trim_matches('"').to_string(); }
        if let Some(v) = line.strip_prefix("version = ") { vers.push((name.clone(), v.trim_matches('"').to_string())); }
    }
    let mut j = String::from("{");
    for (i, (lib, crates)) in CRATES.iter().enumerate() {
        if i > 0 { j.push(','); }
        j.push_str(&format!("\"{lib}\":{{\"crates\":{{"));
        let mut first = true;
        for c in *crates {
            let vs: Vec<&str> = vers.iter().filter(|(n, _)| n == c).map(|(_, v)| v.as_str()).collect();
            if vs.is_empty() { continue; }
            if !first { j.push(','); }
            first = false;
            j.push_str(&format!("\"{c}\":\"{}\"", vs.join(" ")));
        }
        j.push_str("}}");
    }
    j.push('}');
    println!("cargo:rustc-env=DEVBENCH_CRATE_VERSIONS={j}");
    println!("cargo:rerun-if-changed=Cargo.lock");
    println!("cargo:rerun-if-changed=../.git/HEAD");
    let _ = (OPERATIONS, LIBRARIES, REQUIRED, deny_ids);
}
