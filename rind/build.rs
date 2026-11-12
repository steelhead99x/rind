// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Picks the one backend `rind::low` compiles, as `rind_backend`.
//!
//! The assembly backends assume a little-endian target, so a big-endian
//! aarch64 or 32-bit ARM target gets the portable backend, as does every
//! other architecture. The 32-bit ARM assembly is cut for ARMv7, so a target
//! for an earlier core, such as ARMv6's `arm-unknown-linux-gnueabihf` or
//! ARMv5TE's `arm-linux-androideabi`, gets the portable backend too.
//! `--cfg rind_portable` forces it anywhere, so CI tests it on x86_64 without
//! emulation; it is for testing, not for shipping.
//!
//! Cargo.toml's portable dependencies repeat this choice, since a manifest
//! cannot read a build script's cfgs.

use std::env;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        r#"cargo::rustc-check-cfg=cfg(rind_backend, values("x86_64", "aarch64", "arm", "portable"))"#
    );

    let arch = env::var("CARGO_CFG_TARGET_ARCH").expect("cargo sets the target arch");
    let little = env::var("CARGO_CFG_TARGET_ENDIAN").is_ok_and(|e| e == "little");
    let forced = env::var_os("CARGO_CFG_RIND_PORTABLE").is_some();
    let backend = match arch.as_str() {
        "x86_64" | "aarch64" if little && !forced => arch.as_str(),
        "arm" if little && !forced && armv7_or_later() => "arm",
        _ => "portable",
    };
    println!(r#"cargo::rustc-cfg=rind_backend="{backend}""#);

    // See UPSTREAM.md, "Thumb targets omit `thumb-mode`".
    println!("cargo::rustc-check-cfg=cfg(rind_arm_thumb)");
    if arm_thumb_codegen() {
        println!("cargo::rustc-cfg=rind_arm_thumb");
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

/// Thumb codegen that does not advertise `target_feature = "thumb-mode"`.
///
/// rustc 1.99.1 sets that feature in no `arch = "arm"` target's
/// `--print cfg`. Thumb is every triple whose name starts with `thumb`,
/// plus the two whose LLVM triples are Thumb anyway:
/// `armv7-linux-androideabi` (`armv7-none-linux-android` with `+thumb-mode`)
/// and `armv7-sony-vita-newlibeabihf` (`thumbv7a-sony-vita-eabihf`).
/// `arm-linux-androideabi` and `armv7-unknown-linux-gnueabihf` stay ARM, so
/// their `add r12, pc` reads the instruction address plus 8.
fn arm_thumb_codegen() -> bool {
    let target = env::var("TARGET").expect("cargo sets the target");
    let arch = target.split('-').next().unwrap_or_default();
    arch.starts_with("thumb")
        || target == "armv7-linux-androideabi"
        || target == "armv7-sony-vita-newlibeabihf"
}
