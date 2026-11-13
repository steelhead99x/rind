// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Builds the FIPS module, `librind_fips_module.so`, from `module/` with
//! pinned flags, writes its integrity value into it, and links it.
//!
//! The module is a shared library because a Rust library cannot be a
//! boundary: generics and inlining would put the module's code in its
//! caller's. Its flags are pinned so the module is the same whatever builds
//! `rind-fips`: release, `panic = "abort"`, and LTO within the module only.
//!
//! After linking, this script plays aws-lc's `inject_hash.go`: it finds the
//! module's relocation tables, writes where they are into the module's
//! read-only data, hashes the module as the load-time integrity test will
//! (`module/src/image.rs`), and writes the HMAC into its writable data,
//! which the hash leaves out.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[path = "module/src/image.rs"]
#[allow(dead_code)]
mod image;

use image::{Arch, EXPECTED_PLACEHOLDER, Image, LAYOUT_MAGIC, Layout, Rela, Segment};

const MODULE: &str = "librind_fips_module.so";

fn main() {
    let manifest = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let target = env::var("TARGET").unwrap();

    // The module's tested environments are Linux on x86_64 and aarch64, and
    // its boundary is an ELF shared library.
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    let target_env = env::var("CARGO_CFG_TARGET_ENV").unwrap();
    let arch = match env::var("CARGO_CFG_TARGET_ARCH").unwrap().as_str() {
        "x86_64" => Arch::X86_64,
        "aarch64" => Arch::Aarch64,
        other => panic!("rind-fips builds only for x86_64 and aarch64 Linux, not {other}"),
    };
    assert!(
        os == "linux" && target_env == "gnu",
        "rind-fips builds only for glibc Linux, not {target}"
    );

    for path in ["build.rs", "module", "../rind/src", "../rind/build.rs", "../rind/Cargo.toml", "../Cargo.lock"] {
        println!("cargo::rerun-if-changed={}", manifest.join(path).display());
    }

    let built = build(&manifest, &out, &target);
    let mut library = fs::read(&built).unwrap();
    if let Err(error) = inject(&mut library, arch) {
        panic!("cannot write the module's integrity value into {}: {error}", built.display());
    }

    let lib = out.join("lib");
    fs::create_dir_all(&lib).unwrap();
    let module = lib.join(MODULE);
    fs::write(&module, &library).unwrap();

    println!("cargo::rustc-link-search=native={}", lib.display());
    println!("cargo::rustc-link-lib=dylib=rind_fips_module");
    // Tests find the module to tamper with a copy of it.
    println!("cargo::rustc-env=RIND_FIPS_MODULE={}", module.display());
}

/// Builds the module with a cargo of its own, returning the library's path.
fn build(manifest: &Path, out: &Path, target: &str) -> PathBuf {
    let target_dir = out.join("target");
    let mut flags = vec!["--cfg", "rind_fips", "--cfg", "rind_cpu_disable"];
    if env::var_os("CARGO_FEATURE___BREAK_TESTS").is_some() {
        flags.extend(["--cfg", "rind_fips_break"]);
    }
    flags.push(concat!("-Clink-arg=-Wl,-soname,", "librind_fips_module.so"));

    let mut command = Command::new(env::var_os("CARGO").unwrap());
    command
        .args(["build", "--release", "--locked", "--offline", "--target", target])
        .arg("--manifest-path")
        .arg(manifest.join("module/Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir)
        // Until `wipe` is rind's default, the module turns it on here: as a
        // dependency in its manifest, it would turn it on for every crate a
        // workspace build compiles with the module.
        .args(["--features", "rind/wipe"])
        // These flags replace any the caller set, which would otherwise
        // reach the module through the environment.
        .env("CARGO_ENCODED_RUSTFLAGS", flags.join("\x1f"))
        .env("CARGO_PROFILE_RELEASE_OPT_LEVEL", "3")
        .env("CARGO_PROFILE_RELEASE_PANIC", "abort")
        .env("CARGO_PROFILE_RELEASE_LTO", "fat")
        .env("CARGO_PROFILE_RELEASE_CODEGEN_UNITS", "1")
        .env("CARGO_PROFILE_RELEASE_DEBUG", "false")
        .env("CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS", "false")
        .env("CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS", "false")
        .env("CARGO_PROFILE_RELEASE_INCREMENTAL", "false")
        .env("CARGO_PROFILE_RELEASE_STRIP", "false")
        .env_remove("RUSTC_WORKSPACE_WRAPPER")
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO_BUILD_TARGET");
    let status = command.status().expect("cannot run cargo to build the module");
    assert!(status.success(), "building the FIPS module failed");
    target_dir.join(target).join("release").join(MODULE)
}

/// The library's program headers, little-endian ELF64 only.
fn segments(file: &[u8]) -> Result<Vec<(Segment, u64)>, &'static str> {
    if file.get(..6) != Some(b"\x7fELF\x02\x01") {
        return Err("not a little-endian ELF64 file");
    }
    let phoff = u64_at(file, 0x20)? as usize;
    let phentsize = u16_at(file, 0x36)? as usize;
    let phnum = u16_at(file, 0x38)? as usize;
    (0..phnum)
        .map(|i| {
            let at = phoff + i * phentsize;
            Ok((
                Segment {
                    kind: u32_at(file, at)?,
                    flags: u32_at(file, at + 4)?,
                    vaddr: u64_at(file, at + 16)?,
                    filesz: u64_at(file, at + 32)?,
                },
                u64_at(file, at + 8)?,
            ))
        })
        .collect()
}

struct File<'a> {
    bytes: &'a [u8],
    segments: &'a [(Segment, u64)],
}

impl File<'_> {
    /// The file offset of virtual address `vaddr`, within a loaded segment's
    /// file bytes.
    fn offset(&self, vaddr: u64) -> Option<usize> {
        self.segments
            .iter()
            .find(|(s, _)| s.kind == image::PT_LOAD && vaddr >= s.vaddr && vaddr - s.vaddr < s.filesz)
            .map(|(s, offset)| (offset + vaddr - s.vaddr) as usize)
    }

    /// The loaded segment holding file offset `offset`.
    fn segment_at(&self, offset: usize) -> Option<&Segment> {
        self.segments
            .iter()
            .find(|(s, o)| s.kind == image::PT_LOAD && offset as u64 >= *o && offset as u64 - o < s.filesz)
            .map(|(s, _)| s)
    }
}

impl Image for File<'_> {
    fn bytes(&self, vaddr: u64, len: u64) -> &[u8] {
        let at = self.offset(vaddr).expect("hashing outside the loaded segments");
        &self.bytes[at..at + len as usize]
    }

    fn relative(&self, rela: &Rela) -> u64 {
        rela.addend as u64
    }
}

/// Writes the layout, then the expected HMAC, into the linked `library`.
fn inject(library: &mut [u8], arch: Arch) -> Result<(), String> {
    let segments = segments(library)?;
    let file = File {
        bytes: library,
        segments: &segments,
    };

    // The dynamic section names the relocation tables.
    let (dynamic, _) = segments
        .iter()
        .find(|(s, _)| s.kind == image::PT_DYNAMIC)
        .ok_or("no dynamic section")?;
    let dynamic_at = file.offset(dynamic.vaddr).ok_or("the dynamic section is not loaded")?;
    let mut layout = Layout::default();
    let (mut rela_size, mut jmprel_size) = (0, 0);
    for entry in library[dynamic_at..dynamic_at + dynamic.filesz as usize].as_chunks::<16>().0 {
        let (tag, value) = (u64_at(entry, 0)?, u64_at(entry, 8)?);
        match tag {
            0 => break,
            // DT_RELA, DT_RELASZ, DT_JMPREL, DT_PLTRELSZ
            7 => layout.rela = value,
            8 => rela_size = value,
            23 => layout.jmprel = value,
            2 => jmprel_size = value,
            // DT_RELAENT
            9 if value != 24 => return Err("relocations are not Elf64_Rela".into()),
            // DT_PLTREL must name DT_RELA.
            20 if value != 7 => return Err("PLT relocations are not Elf64_Rela".into()),
            // DT_REL, DT_RELR: tables the hash does not read.
            17 | 36 => return Err("relocations in a table other than RELA".into()),
            // DT_TEXTREL, or DT_FLAGS with DF_TEXTREL.
            22 => return Err("text relocations".into()),
            30 if value & 4 != 0 => return Err("text relocations".into()),
            _ => {}
        }
    }
    layout.rela_count = rela_size / 24;
    layout.jmprel_count = jmprel_size / 24;

    let mut relas = Vec::new();
    for (table, count) in [(layout.rela, layout.rela_count), (layout.jmprel, layout.jmprel_count)] {
        for i in 0..count {
            let at = file.offset(table + i * 24).ok_or("a relocation table is not loaded")?;
            let rela = Rela {
                offset: u64_at(library, at)?,
                info: u64_at(library, at + 8)?,
                addend: u64_at(library, at + 16)? as i64,
            };
            if image::kind(arch, rela.kind()).is_none() {
                return Err(format!("unexpected relocation type {}", rela.kind()));
            }
            relas.push(rela);
        }
    }

    // The layout goes where the hash covers it, the expected value where it
    // does not.
    let layout_at = find_once(library, &LAYOUT_MAGIC)?;
    let expected_at = find_once(library, &EXPECTED_PLACEHOLDER)?;
    let writable = |at: usize| file.segment_at(at).map(|s| s.flags & image::PF_W != 0);
    if writable(layout_at) != Some(false) {
        return Err("the layout is not in a read-only segment".into());
    }
    if writable(expected_at) != Some(true) {
        return Err("the expected value is not in a writable segment".into());
    }
    let relro = segments
        .iter()
        .find(|(s, _)| s.kind == image::PT_GNU_RELRO)
        .ok_or("no RELRO segment")?;
    if expected_at as u64 >= relro.1 && (expected_at as u64) - relro.1 < relro.0.filesz {
        return Err("the expected value is in the RELRO segment, which is hashed".into());
    }

    let at = layout_at + LAYOUT_MAGIC.len();
    for (i, value) in [layout.rela, layout.rela_count, layout.jmprel, layout.jmprel_count]
        .into_iter()
        .enumerate()
    {
        library[at + 8 * i..at + 8 * (i + 1)].copy_from_slice(&value.to_le_bytes());
    }

    let file = File {
        bytes: library,
        segments: &segments,
    };
    let only_segments: Vec<Segment> = segments.iter().map(|(s, _)| *s).collect();
    let key = rind::hmac::Key::new(&rind::hmac::HMAC_SHA256, &image::HMAC_KEY);
    let mut context = rind::hmac::Context::with_key(&key);
    image::hash(&file, arch, &only_segments, &mut relas, |bytes| context.update(bytes))?;
    let tag = context.sign();
    library[expected_at..expected_at + 32].copy_from_slice(tag.as_ref());
    Ok(())
}

/// The offset of `needle`'s only occurrence in `haystack`.
fn find_once(haystack: &[u8], needle: &[u8]) -> Result<usize, String> {
    let mut found = haystack
        .windows(needle.len())
        .enumerate()
        .filter(|(_, w)| *w == needle)
        .map(|(i, _)| i);
    let first = found.next().ok_or_else(|| format!("{:?} is missing", String::from_utf8_lossy(needle)))?;
    if found.next().is_some() {
        return Err(format!("{:?} appears twice", String::from_utf8_lossy(needle)));
    }
    Ok(first)
}

fn u16_at(bytes: &[u8], at: usize) -> Result<u16, &'static str> {
    Ok(u16::from_le_bytes(bytes.get(at..at + 2).ok_or("truncated ELF")?.try_into().unwrap()))
}

fn u32_at(bytes: &[u8], at: usize) -> Result<u32, &'static str> {
    Ok(u32::from_le_bytes(bytes.get(at..at + 4).ok_or("truncated ELF")?.try_into().unwrap()))
}

fn u64_at(bytes: &[u8], at: usize) -> Result<u64, &'static str> {
    Ok(u64::from_le_bytes(bytes.get(at..at + 8).ok_or("truncated ELF")?.try_into().unwrap()))
}
