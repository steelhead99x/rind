// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Picks the one backend `rind::low` compiles, as `rind_backend`.
//!
//! The assembly backends assume a little-endian target, so a big-endian
//! aarch64 or 32-bit ARM target gets the portable backend, as does every
//! other architecture. The 32-bit ARM assembly is cut for ARMv7, so a target
//! for an earlier core, such as ARMv6's `arm-unknown-linux-gnueabihf` or
//! ARMv5TE's `arm-linux-androideabi`, gets the portable backend too.
//! `--cfg rind_portable` forces it anywhere, so CI tests it on x86_64 without
//! emulation; it is for testing, not for shipping. On
//! `xtensa-esp32s3-espidf` it also raises the alignment of libcrux-sha2's
//! SHA-256 text to the instruction-cache set stride. See
//! `esp32s3-sha256-align.py`.
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

use std::env;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::thread;
use std::time::{Duration, Instant};

fn main() {
    println!("cargo::rerun-if-changed=build.rs");
    println!(
        r#"cargo::rustc-check-cfg=cfg(rind_backend, values("x86_64", "aarch64", "arm", "portable"))"#
    );

    println!(r#"cargo::rustc-check-cfg=cfg(rind_limb, values("32", "64"))"#);

    let arch = env::var("CARGO_CFG_TARGET_ARCH").expect("cargo sets the target arch");
    let little = env::var("CARGO_CFG_TARGET_ENDIAN").is_ok_and(|e| e == "little");
    let forced = env::var_os("CARGO_CFG_RIND_PORTABLE").is_some();
    let backend = match arch.as_str() {
        "x86_64" | "aarch64" if little && !forced => arch.as_str(),
        "arm" if little && !forced && armv7_or_later() => "arm",
        _ => "portable",
    };
    println!(r#"cargo::rustc-cfg=rind_backend="{backend}""#);

    let wide = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").is_ok_and(|w| w == "64")
        || (arch == "wasm32"
            && env::var("CARGO_CFG_TARGET_FEATURE")
                .is_ok_and(|f| f.split(',').any(|f| f == "wide-arithmetic")));
    if env::var_os("CARGO_CFG_RIND_LIMB").is_none() {
        let limb = if wide { 64 } else { 32 };
        println!(r#"cargo::rustc-cfg=rind_limb="{limb}""#);
    }

    align_esp32s3_sha256();
}

/// On `xtensa-esp32s3-espidf`, raise `sh_addralign` of libcrux-sha2's
/// `.text.*sha256_update*` sections to 8192 bytes.
///
/// Cargo may run this script while that rlib is still being linked, so wait
/// until the archive is complete. The edit is idempotent: an alignment that
/// is already a multiple of 8192 is left untouched, and the file is rewritten
/// only when a field changes. `lto` rebuilds the sections and drops it.
/// Every other target returns without looking for the rlib.
fn align_esp32s3_sha256() {
    if env::var("TARGET").ok().as_deref() != Some("xtensa-esp32s3-espidf") {
        return;
    }
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("cargo sets the manifest dir");
    let script = Path::new(&manifest).join("esp32s3-sha256-align.py");
    println!("cargo::rerun-if-changed={}", script.display());

    let out = PathBuf::from(env::var("OUT_DIR").expect("cargo sets OUT_DIR"));
    let deps = out
        .ancestors()
        .nth(3)
        .expect("OUT_DIR is target/<triple>/<profile>/build/<pkg>/out")
        .join("deps");
    let rlibs = wait_for_sha2_rlibs(&deps);
    for rlib in &rlibs {
        println!("cargo::rerun-if-changed={}", rlib.display());
        let status = Command::new("python3")
            .arg(&script)
            .arg("align")
            .arg(rlib)
            .status()
            .unwrap_or_else(|err| panic!("python3 failed to run {}: {err}", script.display()));
        if !status.success() {
            panic!(
                "ESP32-S3 SHA-256 alignment failed for {} (python3 exited {:?})",
                rlib.display(),
                status.code()
            );
        }
    }
}

fn wait_for_sha2_rlibs(deps: &Path) -> Vec<PathBuf> {
    let deadline = Instant::now() + Duration::from_secs(180);
    loop {
        let found = sha2_rlibs(deps);
        if !found.is_empty() && found.iter().all(|path| archive_ready(path)) {
            return found;
        }
        if Instant::now() >= deadline {
            panic!(
                "no complete liblibcrux_sha2-*.rlib under {} after 180s; cannot align HACL* SHA-256 to the ESP32-S3 cache stride",
                deps.display()
            );
        }
        thread::sleep(Duration::from_millis(50));
    }
}

fn sha2_rlibs(deps: &Path) -> Vec<PathBuf> {
    let Ok(entries) = fs::read_dir(deps) else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with("liblibcrux_sha2-") && name.ends_with(".rlib") {
            found.push(entry.path());
        }
    }
    found.sort();
    found
}

/// True once rustc has renamed a finished archive into place.
fn archive_ready(path: &Path) -> bool {
    let Ok(first) = fs::metadata(path) else {
        return false;
    };
    if first.len() < 8 {
        return false;
    }
    thread::sleep(Duration::from_millis(20));
    let Ok(second) = fs::metadata(path) else {
        return false;
    };
    if first.len() != second.len() || first.modified().ok() != second.modified().ok() {
        return false;
    }
    let Ok(mut file) = fs::File::open(path) else {
        return false;
    };
    let mut magic = [0_u8; 8];
    file.read_exact(&mut magic).is_ok() && magic == *b"!<arch>\n"
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
