// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Picks the one backend `rind::low` compiles, as `rind_backend`.
//!
//! The assembly backends assume a little-endian target, so a big-endian
//! aarch64 or 32-bit ARM target gets the portable backend, as does every
//! other architecture. A backend requires only what its target enables at
//! compile time, so no CPU that runs the binary lacks a feature it needs:
//! the aarch64 backend needs NEON, which only the `no_std`
//! `*-none-softfloat` targets disable, and the x86_64 backend SSE2, so a
//! build without it, such as one for the kernel and firmware targets
//! `x86_64-unknown-none` and `x86_64-unknown-uefi`, gets the portable backend.
//! The 32-bit ARM assembly is cut for ARMv7, so a target
//! for an earlier core, such as ARMv6's `arm-unknown-linux-gnueabihf` or
//! ARMv5TE's `arm-linux-androideabi`, gets the portable backend too, and so
//! does a microcontroller (M-profile) target such as `thumbv7em-none-eabihf`,
//! which has no ARM state or NEON for that assembly to run in.
//! `--cfg rind_portable` forces it anywhere, so CI tests it on x86_64 without
//! emulation; it is for testing, not for shipping.
//!
//! Cargo.toml's portable dependencies repeat this choice, since a manifest
//! cannot read a build script's cfgs.
//!
//! It also picks `rind_limb`, the width in bits of the limbs the portable
//! backend's public-key arithmetic runs on: 64 where a 64-bit product is
//! one or two instructions, on 64-bit targets and on wasm32 with the
//! `wide-arithmetic` feature, and 32 elsewhere, where it would be a library
//! call. `--cfg rind_limb="32"` forces 32-bit limbs on a 64-bit target, so
//! CI checks both widths on x86_64; like `rind_portable`, it is for testing.
//!
//! And it sets `rind_std` where the target has an operating system and
//! `std`, the only places rind may use `std`: every target but those for
//! bare metal (`target_os = "none"`), UEFI, and Linux without a libc, such
//! as `x86_64-unknown-linux-none`, all of which run `no_std` code.
//!
//! And it sets `rind_reg_asm` on the architectures whose `asm!` with a `reg`
//! operand is stable Rust, which the portable MD5 uses as an optimisation
//! barrier. Elsewhere, such as Xtensa or MIPS, it uses `black_box`.
//!
//! And it sets `rind_mul16` where Poly1305 must not use a 32x32->64-bit multiply (`low::generic::mul16`).
//! On `thumbv7m` the Cortex-M3's `umull` ends early, and on `thumbv6m` and
//! `thumbv8m.base` there is no `umull`; each half is one 32-bit `mul`, which
//! those cores do in fixed time. On ARMv4T and ARMv5TE that `mul` ends early
//! too, including on a 16-bit half, so `rind_mul16_top` sets bit 31 of each
//! half and the early-out takes its long path. That includes a custom target
//! whose triple, `llvm-target`, or features name `v4t` or `v5te`, not only
//! Android's `armv5te` triple. A custom target whose specification the script
//! cannot find (it looks in `RUST_TARGET_PATH` and the package directory and
//! its parents) takes the top-bit path, as the safe choice. On 32-bit RISC-V with no multiply instruction,
//! `rind_mul16_soft` builds each half with a shift and an add. Zmmul has
//! `mul` and `mulhu`, so it does not. A 64-bit RISC-V target with neither
//! keeps 64-bit limbs; those products call `__multi3`, and the build warns.
//! `--cfg rind_mul16` forces the halves,
//! so CI checks them on other targets; it is for testing. The top and soft
//! cfgs follow the target even then. Only Poly1305's limb products use this.
//! X25519, the NIST curves, and RSA on these cores still use a multiply whose
//! time depends on its operands.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        r#"cargo::rustc-check-cfg=cfg(rind_backend, values("x86_64", "aarch64", "arm", "portable"))"#
    );

    println!(r#"cargo::rustc-check-cfg=cfg(rind_limb, values("32", "64"))"#);
    println!("cargo::rustc-check-cfg=cfg(rind_std)");
    println!("cargo::rustc-check-cfg=cfg(rind_mul16)");
    println!("cargo::rustc-check-cfg=cfg(rind_mul16_top)");
    println!("cargo::rustc-check-cfg=cfg(rind_mul16_soft)");
    println!("cargo::rustc-check-cfg=cfg(rind_reg_asm)");
    println!("cargo::rerun-if-env-changed=RUST_TARGET_PATH");

    let os = env::var("CARGO_CFG_TARGET_OS").expect("cargo sets the target os");
    let libc = env::var("CARGO_CFG_TARGET_ENV").is_ok_and(|e| !e.is_empty());
    if !(os == "none" || os == "uefi" || (os == "linux" && !libc)) {
        println!("cargo::rustc-cfg=rind_std");
    }

    let arch = env::var("CARGO_CFG_TARGET_ARCH").expect("cargo sets the target arch");
    let little = env::var("CARGO_CFG_TARGET_ENDIAN").is_ok_and(|e| e == "little");
    let forced = env::var_os("CARGO_CFG_RIND_PORTABLE").is_some();
    let enabled = |feature: &str| {
        env::var("CARGO_CFG_TARGET_FEATURE").is_ok_and(|f| f.split(',').any(|f| f == feature))
    };
    let backend = match arch.as_str() {
        "x86_64" if little && !forced && enabled("sse2") => "x86_64",
        "aarch64" if little && !forced && enabled("neon") => "aarch64",
        // M-profile is Thumb-only and has no NEON, so the arm assembly
        // cannot run there.
        "arm" if little && !forced && armv7_or_later() && !m_profile() => "arm",
        _ => "portable",
    };
    println!(r#"cargo::rustc-cfg=rind_backend="{backend}""#);

    // Stable Rust's `asm!` with a `reg` operand, allow-listed so an
    // architecture whose inline assembly is unstable, such as Xtensa or MIPS,
    // falls back to `black_box` in the portable MD5 instead of failing to
    // build. Arm64EC's `reg` class has been stable since Rust 1.84.
    let reg_asm = matches!(
        arch.as_str(),
        "x86"
            | "x86_64"
            | "arm"
            | "aarch64"
            | "arm64ec"
            | "riscv32"
            | "riscv64"
            | "loongarch64"
            | "s390x"
            | "powerpc"
            | "powerpc64"
    );
    if reg_asm {
        println!("cargo::rustc-cfg=rind_reg_asm");
    }

    let wide = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").is_ok_and(|w| w == "64")
        || (arch == "wasm32"
            && env::var("CARGO_CFG_TARGET_FEATURE")
                .is_ok_and(|f| f.split(',').any(|f| f == "wide-arithmetic")));
    if env::var_os("CARGO_CFG_RIND_LIMB").is_none() {
        let limb = if wide { 64 } else { 32 };
        println!(r#"cargo::rustc-cfg=rind_limb="{limb}""#);
    }

    // A cfg the build already passed, including CI's `--cfg rind_mul16`,
    // stays. The top and soft cfgs still follow the target, so forcing the
    // halves on ARMv5TE does not drop the bit that keeps the early-out long.
    let mode = poly1305_half_mul();
    if env::var_os("CARGO_CFG_RIND_MUL16").is_none() && mode.is_some() {
        println!("cargo::rustc-cfg=rind_mul16");
    }
    if mode == Some(Half::Top) && env::var_os("CARGO_CFG_RIND_MUL16_TOP").is_none() {
        println!("cargo::rustc-cfg=rind_mul16_top");
    }
    if mode == Some(Half::Soft) && env::var_os("CARGO_CFG_RIND_MUL16_SOFT").is_none() {
        println!("cargo::rustc-cfg=rind_mul16_soft");
    }

    // `rind_mul16` is the 32-bit half product. A 64-bit target keeps
    // `generic::poly1305`, so the cfg would not cover these calls.
    if riscv64_without_multiply() {
        println!(
            "cargo::warning=riscv64 without the M extension or Zmmul keeps 64-bit \
             Poly1305 limbs, so each 64x64->128 product calls __multi3 on the secret. \
             rind_mul16 does not cover that width (PLATFORMS.md)"
        );
    }
}

/// How Poly1305 multiplies one 16-bit half, where it must not use a
/// 32x32->64-bit product.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Half {
    /// One 32-bit `mul`. Constant time on the Cortex-M0 and the Cortex-M3.
    Halves,
    /// That `mul` with bit 31 set, so ARMv4T and XScale take the long path.
    Top,
    /// Sixteen shifts and adds. The target has no multiply instruction.
    Soft,
}

/// Which half Poly1305 uses on this target, or none when a 32x32->64-bit
/// product is one instruction that takes the same time for every operand.
///
/// `thumbv7m` is the Cortex-M3, whose `umull` takes 3 to 5 cycles by the
/// size of its operands (Arm DDI 0337, "Cortex-M3 instructions"). `thumbv6m`
/// and `thumbv8m.base` have no `umull`. Each one's 32-bit `mul` takes the
/// same time for every operand. ARMv7E-M, as in `thumbv7em-none-eabihf`,
/// takes one cycle for `umull`, so it is not here. ARMv4T and ARMv5TE end a
/// `mul` early on a 16-bit half too, so the top bit stays set.
/// `arm-linux-androideabi` is ARMv5TE; `armv7-linux-androideabi` is not.
/// Rust's unversioned `arm-unknown-linux-*` triples are ARMv6, which does
/// not end early. 32-bit RISC-V without M and without Zmmul has no multiply
/// instruction. 64-bit RISC-V in that state is not a half product: Poly1305
/// stays on 64-bit limbs.
fn poly1305_half_mul() -> Option<Half> {
    if riscv32_without_multiply() {
        return Some(Half::Soft);
    }
    if arm_early_mul() {
        return Some(Half::Top);
    }
    if thumb_halves() {
        return Some(Half::Halves);
    }
    None
}

/// Whether this 32-bit RISC-V target has no multiply instruction.
fn riscv32_without_multiply() -> bool {
    env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default() == "riscv32" && !riscv_has_multiply()
}

/// Whether this 64-bit RISC-V target has no multiply instruction. Poly1305
/// then calls `__multi3`. `rind_mul16` does not run on 64-bit limbs.
fn riscv64_without_multiply() -> bool {
    env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default() == "riscv64" && !riscv_has_multiply()
}

/// Whether the RISC-V target has `mul` and `mulhu`: the M extension, or
/// Zmmul without the divide instructions.
///
/// Stable `cfg(target_feature)` lists `m` and omits `zmmul`.
/// See UPSTREAM.md, "Build scripts cannot see Zmmul or ARMv4T and ARMv5TE".
fn riscv_has_multiply() -> bool {
    feature_on("m") || feature_on("zmmul")
}

/// Whether Poly1305 must set bit 31 before a 32-bit `mul`.
fn arm_early_mul() -> bool {
    if env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default() != "arm" {
        return false;
    }
    // Those Linux triples are ARMv6. Stable cfg hides `v6`, and `+v5te` on
    // top of one does not retarget it. A custom JSON is not in this list,
    // even one whose file takes such a name: its `llvm-target` decides.
    if let Ok(target) = env::var("TARGET")
        && target_json_text().is_none()
        && matches!(
            target.as_str(),
            "arm-unknown-linux-gnueabi"
                | "arm-unknown-linux-gnueabihf"
                | "arm-unknown-linux-musleabi"
                | "arm-unknown-linux-musleabihf"
                | "armeb-unknown-linux-gnueabi"
        )
    {
        return false;
    }
    let names = arch_names();
    if names
        .iter()
        .any(|name| classify_arm_arch(name) == ArmKind::Later)
    {
        return false;
    }
    if names
        .iter()
        .any(|name| classify_arm_arch(name) == ArmKind::Early)
    {
        return true;
    }
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    if os == "android" && names.iter().any(|name| name == "arm") {
        return true;
    }
    // A custom `arm-none-eabi` with `+v5te` or `+v4t`, and no later arch.
    let early = ["v4t", "armv4t", "v5te", "armv5te"]
        .iter()
        .any(|name| feature_on(name));
    let later = ["v6", "v6k", "v6t2", "v7", "v8", "thumb2"]
        .iter()
        .any(|name| feature_on(name));
    if later {
        return false;
    }
    // A custom 32-bit ARM specification the script could not find, or found
    // without an `llvm-target`: the early core is possible and the top bit
    // costs the others only a little time, so take it.
    early || custom_target_unlocated() || custom_target_unclassified()
}

/// `thumbv6m`, `thumbv7m`, and `thumbv8m.base`: one fixed-time 32-bit `mul`
/// per half. The triple or a custom target's `llvm-target` names them.
fn thumb_halves() -> bool {
    arch_names()
        .iter()
        .any(|name| matches!(name.as_str(), "thumbv6m" | "thumbv7m" | "thumbv8m.base"))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ArmKind {
    /// ARMv4T or ARMv5TE. The 32-bit `mul` ends early.
    Early,
    /// ARMv6 or later. Not this early-out, including M-profile.
    Later,
    /// `arm` or `thumb` with no version.
    Unversioned,
    /// Not a 32-bit ARM arch name.
    Other,
}

fn classify_arm_arch(name: &str) -> ArmKind {
    let rest = if let Some(rest) = name.strip_prefix("thumb") {
        rest
    } else if let Some(rest) = name.strip_prefix("arm") {
        rest
    } else {
        return ArmKind::Other;
    };
    let Some(rest) = rest.strip_prefix('v') else {
        return if rest.is_empty() {
            ArmKind::Unversioned
        } else {
            ArmKind::Other
        };
    };
    let digits = rest.chars().take_while(char::is_ascii_digit).count();
    let Ok(major) = rest[..digits].parse::<u32>() else {
        return ArmKind::Other;
    };
    if major >= 6 {
        return ArmKind::Later;
    }
    if (major == 4 && rest.starts_with("4t")) || (major == 5 && rest.starts_with("5te")) {
        return ArmKind::Early;
    }
    ArmKind::Other
}

/// The arch that names the core: a custom target's `llvm-target` arch, which
/// is what LLVM compiles for whatever the specification's file is called, or
/// else the built-in triple's. A file name is a label anyone can choose, so it
/// never overrides the specification it names: `armv7-board.json` holding an
/// ARMv5TE `llvm-target` is ARMv5TE. Empty for a specification without an
/// `llvm-target`, which `custom_target_unclassified` makes fail closed.
fn arch_names() -> Vec<String> {
    target_arch_label().into_iter().collect()
}

/// See [`arch_names`].
fn target_arch_label() -> Option<String> {
    if let Some(text) = target_json_text() {
        return json_string_field(&text, "llvm-target")
            .map(|llvm| arch_component(&llvm).to_string());
    }
    let target = env::var("TARGET").ok()?;
    Some(arch_component(target_file_stem(&target)).to_string())
}

/// Whether `TARGET` is a custom specification this script read but whose
/// `llvm-target` it could not find, so its core is unknown.
fn custom_target_unclassified() -> bool {
    target_json_text().is_some() && target_arch_label().is_none()
}

fn target_file_stem(target: &str) -> &str {
    let file = target.rsplit(['/', '\\']).next().unwrap_or(target);
    file.strip_suffix(".json").unwrap_or(file)
}

fn arch_component(name: &str) -> &str {
    name.split('-').next().unwrap_or(name)
}

/// Whether `name` is enabled. An explicit `+` or `-` in a custom target's
/// `features` or in `-C target-feature` wins. Otherwise the cfg does, which
/// is where stable Rust reports `m` and where nightly reports `v5te`.
///
/// `zmmul` and stable `v5te` are not in that cfg.
/// See UPSTREAM.md, "Build scripts cannot see Zmmul or ARMv4T and ARMv5TE".
fn feature_on(name: &str) -> bool {
    if let Some(enabled) = explicit_feature(name) {
        return enabled;
    }
    env::var("CARGO_CFG_TARGET_FEATURE")
        .unwrap_or_default()
        .split(',')
        .any(|feature| feature == name)
}

fn explicit_feature(name: &str) -> Option<bool> {
    let mut found = None;
    if let Some(text) = target_json_text()
        && let Some(features) = json_string_field(&text, "features")
        && let Some(enabled) = last_sign(&features, name)
    {
        found = Some(enabled);
    }
    if let Ok(encoded) = env::var("CARGO_ENCODED_RUSTFLAGS") {
        for list in rustflag_feature_lists(&encoded) {
            if let Some(enabled) = last_sign(list, name) {
                found = Some(enabled);
            }
        }
    }
    found
}

fn last_sign(list: &str, name: &str) -> Option<bool> {
    let mut found = None;
    for token in list.split(',') {
        let token = token.trim();
        if let Some(feature) = token.strip_prefix('+')
            && feature == name
        {
            found = Some(true);
        } else if let Some(feature) = token.strip_prefix('-')
            && feature == name
        {
            found = Some(false);
        }
    }
    found
}

/// `-C target-feature` lists from `CARGO_ENCODED_RUSTFLAGS`. Cargo joins
/// arguments with U+001F. `RUSTFLAGS='-C target-feature=+zmmul'` arrives as
/// one argument, `-Ctarget-feature=+zmmul`.
fn rustflag_feature_lists(encoded: &str) -> Vec<&str> {
    let args: Vec<&str> = encoded.split('\u{1f}').collect();
    let mut lists = Vec::new();
    for (i, arg) in args.iter().enumerate() {
        if let Some(list) = arg.strip_prefix("-Ctarget-feature=") {
            lists.push(list);
        } else if let Some(list) = arg.strip_prefix("target-feature=") {
            lists.push(list);
        } else if *arg == "-C"
            && let Some(list) = args
                .get(i + 1)
                .and_then(|next| next.strip_prefix("target-feature="))
        {
            lists.push(list);
        }
    }
    lists
}

fn target_json_text() -> Option<String> {
    let target = env::var("TARGET").ok()?;
    let path = Path::new(&target);
    if path.is_file() {
        return fs::read_to_string(path).ok();
    }
    let json = Path::new(&target).with_extension("json");
    if json.is_file() {
        return fs::read_to_string(json).ok();
    }
    // Cargo sets `TARGET` to the file stem of `--target /path/board.json`
    // and runs this script in the package directory, so look where a
    // specification is usually kept: `RUST_TARGET_PATH`, which rustc also
    // searches, and the package directory and each parent up to the
    // workspace root. A specification kept anywhere else stays unseen, and
    // `custom_target_unlocated` makes that case fail closed.
    let name = format!("{}.json", target_file_stem(&target));
    let mut dirs: Vec<PathBuf> = Vec::new();
    if let Some(list) = env::var_os("RUST_TARGET_PATH") {
        dirs.extend(env::split_paths(&list));
    }
    if let Some(manifest) = env::var_os("CARGO_MANIFEST_DIR") {
        dirs.extend(Path::new(&manifest).ancestors().map(Path::to_path_buf));
    }
    dirs.into_iter()
        .map(|dir| dir.join(&name))
        .find(|candidate| candidate.is_file())
        .and_then(|candidate| fs::read_to_string(candidate).ok())
}

/// Whether `TARGET` names a custom target specification this script could
/// not read. The arch, `llvm-target`, and features it would have named are
/// unknown, so an ARMv4T or ARMv5TE core, or a Cortex-M3, may be behind it.
fn custom_target_unlocated() -> bool {
    let Ok(target) = env::var("TARGET") else {
        return false;
    };
    if target_json_text().is_some() {
        return false;
    }
    // A built-in triple is in rustc's list. If rustc cannot be asked, a name
    // with no hyphen is not a triple.
    let rustc = env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    match std::process::Command::new(rustc)
        .args(["--print", "target-list"])
        .output()
    {
        Ok(out) if out.status.success() => !String::from_utf8_lossy(&out.stdout)
            .lines()
            .any(|line| line == target),
        _ => !target.contains('-'),
    }
}

/// The string value of one top-level JSON field, if it is a string.
fn json_string_field(text: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\"");
    let mut rest = text;
    while let Some(at) = rest.find(&needle) {
        let after = rest[at + needle.len()..].trim_start();
        rest = &rest[at + needle.len()..];
        let Some(after) = after.strip_prefix(':') else {
            continue;
        };
        let after = after.trim_start();
        let Some(after) = after.strip_prefix('"') else {
            continue;
        };
        let mut out = String::new();
        let mut chars = after.chars();
        while let Some(c) = chars.next() {
            match c {
                '\\' => {
                    if let Some(escaped) = chars.next() {
                        out.push(escaped);
                    }
                }
                '"' => return Some(out),
                _ => out.push(c),
            }
        }
    }
    None
}

/// Whether the 32-bit ARM target's triple names ARMv7 or later, as in
/// `armv7-unknown-linux-gnueabihf` or `thumbv7neon-linux-androideabi`.
/// Stable Rust hides the `v7` target feature from build scripts, so the
/// triple is all there is. A triple naming no version, such as
/// `arm-unknown-linux-gnueabi`, is for an earlier core.
/// See UPSTREAM.md, "Build scripts cannot see ARM's `v7` target feature".
fn armv7_or_later() -> bool {
    // A custom target's `llvm-target`, not its file name (`arch_names`).
    let arch = target_arch_label().unwrap_or_default();
    let arch = arch.as_str();
    let version = arch
        .strip_prefix("arm")
        .or_else(|| arch.strip_prefix("thumb"))
        .and_then(|rest| rest.strip_prefix('v'))
        .unwrap_or_default();
    let digits = version.bytes().take_while(u8::is_ascii_digit).count();
    version[..digits].parse::<u32>().is_ok_and(|v| v >= 7)
}

/// Whether the 32-bit ARM target is for a microcontroller (M-profile) core,
/// as in `thumbv7m-none-eabi`, `thumbv7em-none-eabihf`,
/// `thumbv8m.main-none-eabihf` or `thumbv8.1m.main-none-eabihf`: Thumb only,
/// without NEON.
fn m_profile() -> bool {
    let arch = target_arch_label().unwrap_or_default();
    let arch = arch.as_str();
    let Some(version) = arch.strip_prefix("thumbv") else {
        return false;
    };
    fn skip_digits(s: &str) -> &str {
        s.trim_start_matches(|c: char| c.is_ascii_digit())
    }
    // The major version, then an optional minor one, as in v8.1m.
    let rest = skip_digits(version);
    let rest = rest.strip_prefix('.').map_or(rest, skip_digits);
    rest.starts_with('m') || rest.starts_with("em")
}
