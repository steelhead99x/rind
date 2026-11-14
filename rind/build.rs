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
//!
//! It also picks `rind_limb`, the width in bits of the limbs the portable
//! backend's public-key arithmetic runs on: 64 where a 64-bit product is
//! one or two instructions, on 64-bit targets and on wasm32 with the
//! `wide-arithmetic` feature, and 32 elsewhere, where it would be a library
//! call. `--cfg rind_limb="32"` forces 32-bit limbs on a 64-bit target, so
//! CI checks both widths on x86_64; like `rind_portable`, it is for testing.
//!
//! On 32-bit portable targets it also assembles the rolled SHA-512 block and
//! the one-block SHA-256 finish into `.text.rind_rolled_slot`, padded so the
//! section's contribution to `.text` is a multiple of 2048 bytes.

use std::env;
use std::fs;
use std::path::Path;
use std::process::Command;

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

    emit_rolled_slot(backend);
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

/// Set stride of a 16 KiB 8-way cache with 32-byte lines: 16384 / 8.
/// A `.text` growth of this many bytes leaves every set index where it was.
/// 4096 and 8192 are the same for that cache, and 4096 also for a 4-way one.
const SET_STRIDE: i64 = 2048;

/// Assembles the rolled SHA-512 block and the one-block SHA-256 finish into
/// one section, padded to a multiple of [`SET_STRIDE`]. The crate pulls the
/// assembly in with `global_asm!`.
fn emit_rolled_slot(backend: &str) {
    println!("cargo::rustc-check-cfg=cfg(sha512_asm_slot)");
    // The slot driver passes this cfg. The rind crate names it and never sets it.
    println!("cargo::rustc-check-cfg=cfg(sha_slot_driver)");
    let width = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap_or_default();
    if backend != "portable" || width != "32" {
        return;
    }
    println!("cargo::rustc-cfg=sha512_asm_slot");
    println!("cargo::rerun-if-changed=src/low/generic/sha512_block.rs");
    println!("cargo::rerun-if-changed=src/low/generic/sha256.rs");
    println!("cargo::rerun-if-changed=src/low/generic/slot_driver.rs");

    let target = env::var("TARGET").expect("cargo sets TARGET");
    let out_dir = env::var("OUT_DIR").expect("cargo sets OUT_DIR");
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR");
    let rustc = env::var("RUSTC").expect("cargo sets RUSTC");
    let out = Path::new(&out_dir);

    let raw_asm = out.join("slot_driver.s");
    compile_driver(&rustc, &target, &manifest, &raw_asm);
    let raw = fs::read_to_string(&raw_asm).unwrap_or_else(|e| panic!("reading {raw_asm:?}: {e}"));
    // `.L*` labels would collide with the CGU that includes this assembly.
    let renamed = raw.replace(".L", ".Lrslot");

    let unpadded = out.join("slot_unpadded.s");
    fs::write(&unpadded, prepare_asm(&renamed))
        .unwrap_or_else(|e| panic!("writing {unpadded:?}: {e}"));
    let body = assemble(
        &rustc,
        &target,
        out,
        &unpadded,
        &out.join("slot_unpadded.o"),
    );

    let slack = placement_slack(&target);
    let stride = stride_for(body as i64 + slack);
    let rem = (body as i64 + slack).rem_euclid(stride);
    let pad = if rem == 0 { 0 } else { (stride - rem) as u64 };

    let mut padded = renamed;
    if pad > 0 {
        let directive = section_directive(&padded);
        padded.push_str(&format!("\n{directive}\n\t.zero {pad}\n"));
    }
    let slot_asm = out.join("sha512_slot.s");
    fs::write(&slot_asm, prepare_asm(&padded))
        .unwrap_or_else(|e| panic!("writing {slot_asm:?}: {e}"));
    let got = assemble(&rustc, &target, out, &slot_asm, &out.join("sha512slot.o"));
    let linked = got as i64 + slack;
    if linked.rem_euclid(stride) != 0 {
        panic!(
            "rolled slot is {got} bytes with slack {slack}, which is {linked} mod {stride} = {}",
            linked.rem_euclid(stride)
        );
    }
}

/// Bytes of `.text` outside the slot, versus main `8dfb7942`, in a release
/// image that hashes SHA-256 and SHA-512 and still links HACL*'s SHA-512.
/// The slot shrinks by this much so the linked image grows by a multiple of
/// [`SET_STRIDE`].
///
/// Measured with rustc 1.90. A target that is not listed keeps 0: the slot
/// itself is still a multiple of the stride, and only an unmeasured
/// out-of-slot change can miss it.
fn placement_slack(target: &str) -> i64 {
    match target {
        "i686-unknown-linux-gnu" => 16,
        _ => 0,
    }
}

fn stride_for(total: i64) -> i64 {
    let mut stride = SET_STRIDE;
    let need = total.max(0);
    while need > stride {
        stride *= 2;
        if stride > 8192 {
            panic!("rolled slot contribution {total} exceeds 8192 bytes");
        }
    }
    stride
}

fn compile_driver(rustc: &str, target: &str, manifest: &str, asm: &Path) {
    let driver = Path::new(manifest).join("src/low/generic/slot_driver.rs");
    let mut cmd = rustc_cmd(rustc, target);
    cmd.args([
        "--crate-name",
        "rind_slot",
        "--emit",
        &format!("asm={}", asm.display()),
        "-C",
        // `s` keeps the block under 2048 bytes on riscv32, where `3` spills
        // into the next stride. The ESP32-S3 win is the cache hit, not the
        // scheduling of an 80-round loop.
        "opt-level=s",
        "-C",
        "debug-assertions=off",
        "-C",
        "overflow-checks=off",
        "-C",
        "debuginfo=0",
        "--cfg",
        "sha_slot_driver",
    ])
    .arg(&driver);
    run(&mut cmd, "slot driver");
}

fn assemble(rustc: &str, target: &str, out: &Path, asm: &Path, obj: &Path) -> u64 {
    let wrap = out.join(format!(
        "wrap_{}.rs",
        asm.file_stem().unwrap().to_string_lossy()
    ));
    let name = asm.file_name().unwrap().to_string_lossy();
    let options =
        if target.starts_with("i686") || target.starts_with("i586") || target.starts_with("x86") {
            ", options(att_syntax)"
        } else {
            ""
        };
    fs::write(
        &wrap,
        format!("#![no_std]\ncore::arch::global_asm!(include_str!(\"{name}\"){options});\n"),
    )
    .unwrap_or_else(|e| panic!("writing {wrap:?}: {e}"));
    let mut cmd = rustc_cmd(rustc, target);
    cmd.args(["--crate-name", "rind_slot_wrap", "--emit"])
        .arg(format!("obj={}", obj.display()))
        .arg(&wrap);
    run(&mut cmd, "assemble slot");
    let size = text_and_literal(obj);
    let names = nm_symbols(obj);
    if asm.file_name().is_some_and(|name| name == "sha512_slot.s")
        && (!names.contains("rind_sha512_compress_blocks")
            || !names.contains("rind_sha256_finish_one"))
    {
        panic!("slot object is missing an export:\n{names}");
    }
    size
}

fn rustc_cmd(rustc: &str, target: &str) -> Command {
    let mut cmd = Command::new(rustc);
    cmd.args([
        "--edition",
        "2024",
        "--crate-type",
        "rlib",
        "--cap-lints",
        "allow",
        "--target",
        target,
        "-C",
        "panic=abort",
        "-C",
        &format!("relocation-model={}", relocation_model(target)),
    ]);
    cmd
}

fn relocation_model(target: &str) -> &'static str {
    if target.contains("-none") {
        "static"
    } else {
        "pic"
    }
}

fn prepare_asm(asm: &str) -> String {
    // x86 is AT&T. `global_asm!` is given `options(att_syntax)` for that
    // architecture. A `.att_syntax` directive in the file is `bad_asm_style`.
    asm.replace('{', "{{").replace('}', "}}")
}

fn section_directive(asm: &str) -> String {
    for line in asm.lines() {
        let trimmed = line.trim();
        if trimmed.contains(".text.rind_rolled_slot")
            && (trimmed.starts_with(".section") || trimmed.starts_with(".pushsection"))
        {
            return trimmed.to_string();
        }
    }
    panic!("rolled slot asm has no .text.rind_rolled_slot section");
}

fn text_and_literal(obj: &Path) -> u64 {
    let output = Command::new("size")
        .args(["-A"])
        .arg(obj)
        .output()
        .unwrap_or_else(|e| panic!("size: {e}"));
    if !output.status.success() {
        panic!(
            "size {} failed: {}",
            obj.display(),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut total = 0u64;
    for line in text.lines().skip(1) {
        let mut cols = line.split_whitespace();
        let Some(name) = cols.next() else { continue };
        let Some(size) = cols.next() else { continue };
        if name == ".text"
            || name.starts_with(".text.")
            || name == ".literal"
            || name.starts_with(".literal.")
        {
            let Ok(size) = size.parse::<u64>() else {
                continue;
            };
            total += size;
        }
    }
    total
}

fn nm_symbols(obj: &Path) -> String {
    let output = Command::new("nm")
        .arg(obj)
        .output()
        .unwrap_or_else(|e| panic!("nm: {e}"));
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn run(cmd: &mut Command, what: &str) {
    let output = cmd.output().unwrap_or_else(|e| panic!("{what}: {e}"));
    if !output.status.success() {
        panic!(
            "{what} failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
