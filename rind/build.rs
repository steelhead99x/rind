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
//! On built-in ELF x86, RISC-V32, and Xtensa portable targets it assembles the rolled SHA-512 block and
//! the one-block SHA-256 finish into `.text.rind_rolled_slot`, padded so the
//! slot plus measured out-of-slot slack is a multiple of 2048 bytes.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
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
/// one section, padded with measured slack to a multiple of [`SET_STRIDE`].
/// The crate pulls the
/// assembly in with `global_asm!`.
fn emit_rolled_slot(backend: &str) {
    println!("cargo::rustc-check-cfg=cfg(sha512_asm_slot)");
    // The slot driver passes this cfg. The rind crate names it and never sets it.
    println!("cargo::rustc-check-cfg=cfg(sha_slot_driver)");
    let width = env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap_or_default();
    let arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    // The slot uses ELF sections and native assembly. Wasm and other object
    // formats keep the ordinary Rust compressor, with no host tool dependency.
    // ARM also keeps Rust: LLVM's emitted EABI attributes do not establish
    // the assembler architecture when the text is included in another CGU.
    let native_elf = matches!(arch.as_str(), "x86" | "riscv32" | "xtensa")
        && matches!(os.as_str(), "linux" | "android" | "none" | "espidf");
    if backend != "portable" || width != "32" || !native_elf {
        return;
    }
    let target = env::var("TARGET").expect("cargo sets TARGET");
    let rustc = env::var("RUSTC").expect("cargo sets RUSTC");
    let mut target_list = Command::new(&rustc);
    target_list.args(["--print", "target-list"]);
    let targets = checked_output(&mut target_list, "target list");
    // Cargo exposes a custom target's name here, not the path to its JSON.
    // Compile that target through the outer Cargo invocation's Rust path.
    if !String::from_utf8(targets)
        .expect("target names are UTF-8")
        .lines()
        .any(|name| name == target)
    {
        return;
    }
    println!("cargo::rustc-cfg=sha512_asm_slot");
    println!("cargo::rerun-if-changed=src/low/generic/sha512_block.rs");
    println!("cargo::rerun-if-changed=src/low/generic/sha256.rs");
    println!("cargo::rerun-if-changed=src/low/generic/slot_driver.rs");

    let out_dir = env::var("OUT_DIR").expect("cargo sets OUT_DIR");
    let manifest = env::var("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR");
    let out = Path::new(&out_dir);

    let compiler = SlotCompiler::new(rustc, target, out);
    let raw_asm = out.join("slot_driver.s");
    let driver = Path::new(&manifest).join("src/low/generic/slot_driver.rs");
    compiler.compile(
        "rind_slot",
        &driver,
        &raw_asm,
        "asm",
        &["--cfg", "sha_slot_driver"],
    );
    let raw = fs::read_to_string(&raw_asm).unwrap_or_else(|e| panic!("reading {raw_asm:?}: {e}"));
    // `.L*` labels would collide with the CGU that includes this assembly.
    let renamed = raw.replace(".L", ".Lrslot");

    let unpadded = out.join("slot_unpadded.s");
    fs::write(&unpadded, prepare_asm(&renamed))
        .unwrap_or_else(|e| panic!("writing {unpadded:?}: {e}"));
    let body = assemble(&compiler, &unpadded, &out.join("slot_unpadded.o"));

    let slack = placement_slack(&compiler.target);
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
    let got = assemble(&compiler, &slot_asm, &out.join("sha512slot.o"));
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

/// Cargo supplies the target's `core`, including for Xtensa build-std targets.
/// Each helper has its own manifest and shares only this build's target cache.
struct SlotCompiler<'a> {
    rustc: String,
    target: String,
    out: &'a Path,
    build_std: bool,
    prefix: String,
}

impl<'a> SlotCompiler<'a> {
    fn new(rustc: String, target: String, out: &'a Path) -> Self {
        let mut cmd = Command::new(&rustc);
        cmd.args(["--print", "target-libdir", "--target", &target]);
        for flag in encoded_rustflags() {
            cmd.arg(flag);
        }
        let output = checked_output(&mut cmd, "target sysroot");
        let libdir = PathBuf::from(
            String::from_utf8(output)
                .expect("rustc path is UTF-8")
                .trim(),
        );
        let has_core = libdir.is_dir()
            && fs::read_dir(&libdir)
                .expect("reading target sysroot")
                .any(|entry| {
                    entry
                        .expect("reading target library")
                        .file_name()
                        .to_string_lossy()
                        .starts_with("libcore-")
                });
        let prefix = format!(
            "rind_{}_{}_{}",
            env!("CARGO_PKG_VERSION_MAJOR"),
            env!("CARGO_PKG_VERSION_MINOR"),
            env!("CARGO_PKG_VERSION_PATCH")
        );
        Self {
            rustc,
            target,
            out,
            build_std: !has_core,
            prefix,
        }
    }

    fn compile(&self, name: &str, source: &Path, artifact: &Path, emit: &str, flags: &[&str]) {
        let helper = self.out.join(name);
        fs::create_dir_all(&helper).expect("creating slot helper");
        let manifest = helper.join("Cargo.toml");
        fs::write(&manifest, format!(
            "[package]\nname = {name:?}\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n[lib]\npath = {:?}\n[workspace]\n[profile.release]\nopt-level = \"s\"\ndebug = false\npanic = \"abort\"\n",
            source.to_str().expect("slot source path is UTF-8")
        )).expect("writing slot helper manifest");
        let mut cmd = Command::new(env::var_os("CARGO").expect("cargo sets CARGO"));
        cmd.current_dir(&helper)
            .env("RUSTC", &self.rustc)
            .env("RIND_SLOT_PREFIX", &self.prefix)
            // A recursive cargo must not wait for its parent's jobserver slot.
            .env_remove("CARGO_MAKEFLAGS")
            .env_remove("MAKEFLAGS")
            .env_remove("MFLAGS")
            .args([
                "rustc",
                "--offline",
                "--jobs",
                "1",
                "--release",
                "--lib",
                "--manifest-path",
            ])
            .arg(&manifest)
            .arg("--target-dir")
            .arg(self.out.join("slot-target"))
            .args(["--target", &self.target]);
        if self.build_std {
            cmd.arg("-Zbuild-std=core");
        }
        cmd.arg("--")
            .arg("--emit")
            .arg(format!("{emit}={}", artifact.display()))
            .args([
                "--check-cfg",
                "cfg(sha_slot_driver)",
                "-C",
                "opt-level=s",
                "-C",
                "debug-assertions=off",
                "-C",
                "overflow-checks=off",
            ])
            .args(["-C", &format!("metadata={}", self.prefix)])
            .args(flags);
        checked_output(&mut cmd, "slot helper");
    }
}

fn encoded_rustflags() -> Vec<String> {
    env::var("CARGO_ENCODED_RUSTFLAGS")
        .unwrap_or_default()
        .split('\x1f')
        .filter(|flag| !flag.is_empty())
        .map(str::to_owned)
        .collect()
}

fn assemble(compiler: &SlotCompiler<'_>, asm: &Path, obj: &Path) -> u64 {
    let stem = asm.file_stem().unwrap().to_string_lossy();
    let wrap = compiler.out.join(format!("wrap_{stem}.rs"));
    let name = asm.file_name().unwrap().to_string_lossy();
    let options = if env::var("CARGO_CFG_TARGET_ARCH").is_ok_and(|arch| arch == "x86") {
        ", options(att_syntax)"
    } else {
        ""
    };
    fs::write(&wrap, format!(
        "#![no_std]\n#![cfg_attr(target_arch = \"xtensa\", feature(asm_experimental_arch))]\ncore::arch::global_asm!(include_str!(\"{name}\"){options});\n"
    )).unwrap_or_else(|e| panic!("writing {wrap:?}: {e}"));
    compiler.compile(&format!("rind_wrap_{stem}"), &wrap, obj, "obj", &[]);
    text_and_literal(obj)
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

/// Reads the ELF32 section table directly, so cross builds need no host binutils.
fn text_and_literal(obj: &Path) -> u64 {
    let bytes = fs::read(obj).unwrap_or_else(|e| panic!("reading {obj:?}: {e}"));
    assert_eq!(&bytes[..5], b"\x7fELF\x01", "slot requires an ELF32 object");
    let little = match bytes[5] {
        1 => true,
        2 => false,
        other => panic!("unknown ELF byte order {other}"),
    };
    let word = |offset: usize| {
        let word: [u8; 4] = bytes[offset..offset + 4].try_into().unwrap();
        if little {
            u32::from_le_bytes(word)
        } else {
            u32::from_be_bytes(word)
        }
    };
    let half = |offset: usize| {
        let half: [u8; 2] = bytes[offset..offset + 2].try_into().unwrap();
        if little {
            u16::from_le_bytes(half)
        } else {
            u16::from_be_bytes(half)
        }
    };
    let sections = word(32) as usize;
    let entry_size = half(46) as usize;
    let count = half(48) as usize;
    let names_index = half(50) as usize;
    assert!(
        entry_size >= 40 && count > 0 && names_index < count,
        "unsupported ELF section table"
    );
    let names_section = sections + entry_size * names_index;
    let names_start = word(names_section + 16) as usize;
    let names = &bytes[names_start..names_start + word(names_section + 20) as usize];
    let mut total = 0;
    for i in 0..count {
        let section = sections + entry_size * i;
        let name = &names[word(section) as usize..];
        let name = &name[..name
            .iter()
            .position(|b| *b == 0)
            .expect("ELF section name terminator")];
        if name == b".text"
            || name.starts_with(b".text.")
            || name == b".literal"
            || name.starts_with(b".literal.")
        {
            total += u64::from(word(section + 20));
        }
    }
    assert!(total > 0, "slot object has no text");
    total
}

fn checked_output(cmd: &mut Command, what: &str) -> Vec<u8> {
    let output = cmd.output().unwrap_or_else(|e| panic!("{what}: {e}"));
    if !output.status.success() {
        panic!(
            "{what} failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    output.stdout
}
