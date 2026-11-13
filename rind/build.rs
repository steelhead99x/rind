// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Picks the one backend `rind::low` compiles, as `rind_backend`.
//!
//! The assembly backends assume a little-endian target, so a big-endian
//! aarch64 or 32-bit ARM target gets the portable backend, as does every
//! other architecture. The 32-bit ARM assembly is cut for ARMv7, so a target
//! for an earlier core, such as ARMv6's `arm-unknown-linux-gnueabihf` or
//! ARMv5TE's `arm-linux-androideabi`, gets the portable backend too, and so
//! does a microcontroller (M-profile) target such as `thumbv7em-none-eabihf`,
//! which has no ARM state or NEON for that assembly to run in. A bare-metal
//! x86_64 or aarch64 target (`target_os = "none"`, such as
//! `x86_64-unknown-none`) gets the portable backend as well: those backends
//! detect CPU features through std, which such a target lacks.
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
//! And it sets `rind_reg_asm` on the architectures whose `asm!` with a `reg`
//! operand is stable Rust, which the portable MD5 uses as an optimisation
//! barrier.

use std::env;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        r#"cargo::rustc-check-cfg=cfg(rind_backend, values("x86_64", "aarch64", "arm", "portable"))"#
    );

    println!(r#"cargo::rustc-check-cfg=cfg(rind_limb, values("32", "64"))"#);
    println!("cargo::rustc-check-cfg=cfg(rind_reg_asm)");

    let arch = env::var("CARGO_CFG_TARGET_ARCH").expect("cargo sets the target arch");
    let little = env::var("CARGO_CFG_TARGET_ENDIAN").is_ok_and(|e| e == "little");
    let forced = env::var_os("CARGO_CFG_RIND_PORTABLE").is_some();
    let bare_metal = env::var("CARGO_CFG_TARGET_OS").is_ok_and(|os| os == "none");
    let backend = match arch.as_str() {
        "x86_64" | "aarch64" if little && !forced && !bare_metal => arch.as_str(),
        "arm" if little && !forced && armv7_or_later() && !m_profile() => "arm",
        _ => "portable",
    };
    println!(r#"cargo::rustc-cfg=rind_backend="{backend}""#);

    // Stable Rust's `asm!` with a `reg` operand, allow-listed so an
    // architecture whose inline assembly is unstable, such as Xtensa or MIPS,
    // falls back to `black_box` instead of failing to build.
    let reg_asm = matches!(
        arch.as_str(),
        "x86"
            | "x86_64"
            | "arm"
            | "aarch64"
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
}

/// Whether the 32-bit ARM target's triple names ARMv7 or later, as in
/// `armv7-unknown-linux-gnueabihf` or `thumbv7neon-linux-androideabi`.
/// Stable Rust hides the `v7` target feature from build scripts, so the
/// triple is all there is. A triple naming no version, such as
/// `arm-unknown-linux-gnueabi`, is for an earlier core.
/// See UPSTREAM.md, "Build scripts cannot see ARM's `v7` target feature".
fn armv7_or_later() -> bool {
    let target = env::var("TARGET").expect("cargo sets the target");
    let arch = target.split('-').next().unwrap_or_default();
    let version = arch
        .strip_prefix("arm")
        .or_else(|| arch.strip_prefix("thumb"))
        .and_then(|rest| rest.strip_prefix('v'))
        .unwrap_or_default();
    let digits = version.bytes().take_while(u8::is_ascii_digit).count();
    version[..digits].parse::<u32>().is_ok_and(|v| v >= 7)
}

/// Whether the 32-bit ARM target is for a microcontroller (M-profile) core,
/// as in `thumbv7m-none-eabi`, `thumbv7em-none-eabihf` or
/// `thumbv8m.main-none-eabihf`: Thumb only, without NEON.
fn m_profile() -> bool {
    let target = env::var("TARGET").expect("cargo sets the target");
    let arch = target.split('-').next().unwrap_or_default();
    let Some(version) = arch.strip_prefix("thumbv") else {
        return false;
    };
    let rest = version.trim_start_matches(|c: char| c.is_ascii_digit());
    rest.starts_with('m') || rest.starts_with("em")
}
