// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Picks the one backend `rind::low` compiles, as `rind_backend`.
//!
//! The assembly backends assume a little-endian target, so a big-endian
//! aarch64 or 32-bit ARM target gets the portable backend, as does every
//! other architecture. The aarch64 backend needs NEON, so a target without
//! it, such as `aarch64-unknown-none-softfloat`, gets the portable backend.
//! Bare-metal x86_64 keeps the x86_64 backend when the target enables SSE2.
//! `x86_64-unknown-none` does not: it is soft-float, so that assembly's
//! `xmm` operands are refused until the build passes
//! `-C target-feature=+sse,+sse2,-soft-float`. Leaving soft-float set beside
//! SSE makes LLVM abort while splitting vector results. The backend then
//! reads CPUID through `core::arch`. AVX, AVX2, SHA512, and AVX-512 run
//! only when those target features are enabled: XCR0 does not mean an
//! interrupt saves YMM or ZMM. Bare-metal aarch64
//! with NEON keeps the aarch64 backend,
//! and its crypto tier is the compile-time target features, because there
//! is no OS to ask. The 32-bit ARM assembly is cut for ARMv7,
//! so a target for an earlier core, such as ARMv6's
//! `arm-unknown-linux-gnueabihf` or ARMv5TE's `arm-linux-androideabi`, gets
//! the portable backend too, and so does a microcontroller (M-profile)
//! target such as `thumbv7em-none-eabihf`, which has no ARM state or NEON
//! for that assembly to run in.
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
//! barrier. Arm64EC is one of them: its `reg` class has been stable since
//! Rust 1.84, and it is a subset of AArch64's.
//!
//! On bare-metal x86_64, curve25519-dalek's default does not use AVX:
//! cpufeatures reports a SIMD feature there only when it is a compile-time
//! target feature. An explicit `simd` or `avx512` backend is refused when
//! those features are enabled, because that build would then use them.

use std::env;

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        r#"cargo::rustc-check-cfg=cfg(rind_backend, values("x86_64", "aarch64", "arm", "portable"))"#
    );

    println!(r#"cargo::rustc-check-cfg=cfg(rind_limb, values("32", "64"))"#);
    println!("cargo::rustc-check-cfg=cfg(rind_reg_asm)");
    println!("cargo::rustc-check-cfg=cfg(rind_x86_64_none_dalek_wide)");

    let arch = env::var("CARGO_CFG_TARGET_ARCH").expect("cargo sets the target arch");
    let little = env::var("CARGO_CFG_TARGET_ENDIAN").is_ok_and(|e| e == "little");
    let forced = env::var_os("CARGO_CFG_RIND_PORTABLE").is_some();
    let bare_metal = env::var("CARGO_CFG_TARGET_OS").is_ok_and(|os| os == "none");
    let target_feature = env::var("CARGO_CFG_TARGET_FEATURE").unwrap_or_default();
    let enabled = |name: &str| target_feature.split(',').any(|feature| feature == name);
    let neon = enabled("neon");
    // The x86_64 assembly names `xmm` registers, which need SSE2. A hosted
    // x86_64 target enables it. `x86_64-unknown-none` does not, until the
    // build asks for it. That target is also soft-float, which has to be
    // cleared in the same flag or LLVM cannot legalize the vectors.
    let sse2 = enabled("sse2");
    let backend = match arch.as_str() {
        "x86_64" if little && !forced && (!bare_metal || sse2) => "x86_64",
        "aarch64" if little && !forced && neon => "aarch64",
        // M-profile is Thumb-only and has no NEON, so the arm assembly
        // cannot run there.
        "arm" if little && !forced && armv7_or_later() && !m_profile() => "arm",
        _ => "portable",
    };
    println!(r#"cargo::rustc-cfg=rind_backend="{backend}""#);

    // cpufeatures reports AVX on this os only when the target feature is
    // on, so dalek's default stays on its serial code. An explicit `simd`
    // or `avx512` cfg together with those features would use the registers.
    if arch == "x86_64" && bare_metal && dalek_forces_wide_vectors(&enabled) {
        println!("cargo::rustc-cfg=rind_x86_64_none_dalek_wide");
    }

    // Stable Rust's `asm!` with a `reg` operand, allow-listed so an
    // architecture whose inline assembly is unstable, such as Xtensa or MIPS,
    // falls back to `black_box` instead of failing to build.
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
/// as in `thumbv7m-none-eabi`, `thumbv7em-none-eabihf`,
/// `thumbv8m.main-none-eabihf` or `thumbv8.1m.main-none-eabihf`: Thumb only,
/// without NEON.
fn m_profile() -> bool {
    let target = env::var("TARGET").expect("cargo sets the target");
    let arch = target.split('-').next().unwrap_or_default();
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

/// Whether this build forces curve25519-dalek onto AVX while the target
/// features would let cpufeatures report that those registers exist.
///
/// Cargo passes a `RUSTFLAGS` `--cfg` to the build script as
/// `CARGO_CFG_<NAME>`, one value or several separated by commas. The unset
/// default, `serial`, and `fiat` do not take this path.
fn dalek_forces_wide_vectors(enabled: &dyn Fn(&str) -> bool) -> bool {
    let Ok(value) = env::var("CARGO_CFG_CURVE25519_DALEK_BACKEND") else {
        return false;
    };
    value.split(',').any(|value| match value {
        "simd" => enabled("avx") || enabled("avx2"),
        "avx512" => enabled("avx512f") || enabled("avx512ifma") || enabled("avx512vl"),
        _ => false,
    })
}
