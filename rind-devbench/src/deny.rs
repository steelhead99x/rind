// Checks `RIND_DEVBENCH_DENY`, included by build.rs, which refuses a build
// whose list is wrong, and by the library, whose tests check it. Plain `//`
// comments, since `include!` takes no inner doc comments.

/// The ids whose `RIND_CPU_DISABLE_<id>` rind reads on `arch`, as its CPU
/// detection names them (`rind/src/low/*/cpu.rs`, `rind/src/low/mcdt.rs`),
/// without the dots rind drops from the variable's name (`sse4.1` is
/// `sse41`). Empty for an arch where rind reads none.
pub fn deny_ids(arch: &str) -> &'static [&'static str] {
    match arch {
        "aarch64" => &["aes", "pmull", "sha2", "sha3", "sve2", "dit", "sb", "wide_mul"],
        "arm" => &["neon", "aes", "pmull", "sha1", "sha2"],
        "x86_64" => &[
            "aes", "vaes", "pclmulqdq", "vpclmulqdq", "bmi1", "bmi2", "adx", "popcnt", "ssse3",
            "sse41", "avx", "avx2", "avx512f", "avx512dq", "avx512ifma", "avx512bw", "avx512vl",
            "avx512vbmi", "avx512vbmi2", "avx512fp16", "sha", "movbe", "intel", "mcdt_no",
        ],
        _ => &[],
    }
}

/// `spec`, a comma-separated `RIND_DEVBENCH_DENY` list, as the ids rind reads
/// on `arch`, dots dropped, each once, in the order given; or why it is
/// refused: an empty entry, a character outside `[A-Za-z0-9_.]`, or an id
/// rind does not read there, any of which would leave a feature enabled that
/// the report calls denied.
pub fn parse_denies(spec: &str, arch: &str) -> Result<Vec<String>, String> {
    let known = deny_ids(arch);
    let mut ids: Vec<String> = Vec::new();
    for entry in spec.split(',') {
        let entry = entry.trim();
        if entry.is_empty() {
            return Err(format!("RIND_DEVBENCH_DENY={spec:?} has an empty entry"));
        }
        if !entry.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'.') {
            return Err(format!("RIND_DEVBENCH_DENY entry {entry:?} is not a CPU feature id"));
        }
        let id = entry.replace('.', "");
        if !known.contains(&id.as_str()) {
            return Err(format!(
                "RIND_DEVBENCH_DENY entry {entry:?} is not a feature rind can deny on {arch} (it can deny: {})",
                if known.is_empty() { "none".to_string() } else { known.join(", ") }
            ));
        }
        if !ids.contains(&id) {
            ids.push(id);
        }
    }
    Ok(ids)
}

/// Whether these encoded rustflags (`CARGO_ENCODED_RUSTFLAGS`, flags split by
/// 0x1f) give rind `--cfg rind_cpu_disable`, so it reads `RIND_CPU_DISABLE_*`.
/// rind also reads them with debug assertions on, but a profile can turn those
/// off for rind alone, so a deny build always asks for the cfg.
pub fn denies_take_effect(encoded_rustflags: &str) -> bool {
    let flags: Vec<&str> = encoded_rustflags.split('\x1f').collect();
    flags.windows(2).any(|w| w[0] == "--cfg" && w[1] == "rind_cpu_disable")
        || flags.contains(&"--cfg=rind_cpu_disable")
}

#[cfg(test)]
mod tests {
    use super::*;

    // A list is taken as the ids rind reads, dots dropped, each once.
    #[test]
    fn takes_known_ids() {
        assert_eq!(parse_denies("sha3,dit", "aarch64").unwrap(), ["sha3", "dit"]);
        assert_eq!(parse_denies("sha3, sha3", "aarch64").unwrap(), ["sha3"]);
        assert_eq!(parse_denies("sse4.1,avx2", "x86_64").unwrap(), ["sse41", "avx2"]);
        assert_eq!(parse_denies("neon", "arm").unwrap(), ["neon"]);
    }

    // Anything that would deny nothing while the report says it denied is
    // refused: empty entries, malformed ids, ids rind does not read there.
    #[test]
    fn refuses_what_denies_nothing() {
        for (spec, arch, why) in [
            ("sha3,", "aarch64", "empty entry"),
            (",", "aarch64", "empty entry"),
            ("sha-3", "aarch64", "not a CPU feature id"),
            ("sha3;dit", "aarch64", "not a CPU feature id"),
            ("sha4", "aarch64", "not a feature rind can deny"),
            ("avx2", "aarch64", "not a feature rind can deny"),
            ("sha3", "x86_64", "not a feature rind can deny"),
            ("neon", "riscv64", "can deny: none"),
        ] {
            let e = parse_denies(spec, arch).unwrap_err();
            assert!(e.contains(why), "{spec} on {arch}: {e}");
        }
    }

    // Only `--cfg rind_cpu_disable` counts, in either spelling.
    #[test]
    fn effect_needs_the_cfg() {
        assert!(!denies_take_effect(""));
        assert!(denies_take_effect("-Cfoo\x1f--cfg\x1frind_cpu_disable"));
        assert!(denies_take_effect("--cfg=rind_cpu_disable"));
        assert!(!denies_take_effect("--cfg\x1frind_portable"));
        assert!(!denies_take_effect("--cfg\x1frind_cpu_disable_x"));
    }
}
