// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The module refuses to load once any byte its integrity test covers
//! changes: code, constants, relocation tables, or the constants beside
//! relocated pointers.
//!
//! Each case copies the built module, flips one byte, and runs this test
//! binary again with the copy first on its library path, so the dynamic
//! loader runs the copy's integrity test before anything else.
#![cfg(rind_fips_module)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const MODULE: &str = env!("RIND_FIPS_MODULE");

/// What the child runs: anything that reaches the module.
#[test]
fn loads() {
    assert!(rind_fips::version().starts_with("rind-fips "));
}

/// Runs [`loads`] in a child that loads the module from `dir`.
fn run_with(dir: &Path) -> Output {
    let path = match std::env::var_os("LD_LIBRARY_PATH") {
        Some(rest) => {
            let mut path = dir.as_os_str().to_owned();
            path.push(":");
            path.push(rest);
            path
        }
        None => dir.as_os_str().to_owned(),
    };
    Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "loads", "--test-threads=1"])
        .env("LD_LIBRARY_PATH", path)
        .output()
        .unwrap()
}

/// A directory holding the module with the byte at `offset` flipped, or
/// unchanged for `None`.
fn copy(name: &str, offset: Option<usize>) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("rind-fips-integrity-{name}"));
    std::fs::create_dir_all(&dir).unwrap();
    let mut module = std::fs::read(MODULE).unwrap();
    if let Some(offset) = offset {
        module[offset] ^= 0x01;
    }
    let file = Path::new(MODULE).file_name().unwrap();
    std::fs::write(dir.join(file), module).unwrap();
    dir
}

#[test]
fn an_unchanged_copy_loads() {
    let output = run_with(&copy("unchanged", None));
    assert!(output.status.success(), "{output:?}");
}

/// Each case flips a byte that nothing before the integrity test reads.
/// The dynamic loader applies every relocation, and the CPU check and the
/// SHA-256 and HMAC self-tests run, before the integrity test does, so a
/// byte they read could crash the load, or fail another test, before the
/// integrity test reports: a corrupted relocation of the constructor's own
/// pointer is a jump to a misaligned address, which aarch64 traps.
#[test]
fn tampering_fails_the_integrity_test() {
    let module = std::fs::read(MODULE).unwrap();
    let elf = Elf::parse(&module);
    let relocated = elf.relocated(&module);
    let (rodata, rodata_size) = elf.section(".rodata");
    let (data_rel_ro, data_rel_ro_size) = elf.section(".data.rel.ro");

    let cases = [
        // A service's code, which only a caller reaches.
        (".text", elf.symbol(&module, "rind_fips_version")),
        // The layout's marker, which only the build script reads.
        (
            ".rodata",
            module[rodata..rodata + rodata_size]
                .windows(16)
                .position(|w| w == b"rind-fips layout")
                .map(|at| rodata + at)
                .expect("no layout marker in .rodata"),
        ),
        // The addend of a finalizer's relocation: finalizers run only at
        // exit, which a failed self-test skips by aborting.
        (
            ".rela.dyn",
            elf.relocation_into(&module, ".fini_array") + 16,
        ),
        // A byte of `.data.rel.ro` that no relocation writes, such as a
        // string's length beside its pointer. Every pointer in the module
        // is relocated, so the byte is no address the load could follow.
        (
            ".data.rel.ro",
            (data_rel_ro..data_rel_ro + data_rel_ro_size)
                .find(|&at| module[at] != 0 && !relocated.iter().any(|&r| at >= r && at < r + 8))
                .expect("no unrelocated byte in .data.rel.ro"),
        ),
    ];
    for (name, offset) in cases {
        let output = run_with(&copy(name, Some(offset)));
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success() && stderr.contains("rind-fips: integrity self-test failed"),
            "flipping a byte of {name} at {offset:#x}: {output:?}"
        );
    }
}

/// Just enough of a little-endian ELF64 file to find sections, dynamic
/// symbols, and relocations.
struct Elf {
    sections: Vec<Section>,
}

struct Section {
    name: String,
    kind: u32,
    addr: u64,
    offset: usize,
    size: usize,
}

const SHT_RELA: u32 = 4;
const RELA_SIZE: usize = 24;
const SYM_SIZE: usize = 24;

fn u32_at(file: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(file[at..at + 4].try_into().unwrap())
}

fn u64_at(file: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(file[at..at + 8].try_into().unwrap())
}

/// The NUL-terminated string at `at`.
fn str_at(file: &[u8], at: usize) -> &[u8] {
    let len = file[at..].iter().position(|&b| b == 0).unwrap();
    &file[at..at + len]
}

impl Elf {
    fn parse(file: &[u8]) -> Self {
        let u16_at = |at: usize| u16::from_le_bytes(file[at..at + 2].try_into().unwrap());
        let shoff = u64_at(file, 0x28) as usize;
        let (shentsize, shnum, shstrndx) = (
            u16_at(0x3a) as usize,
            u16_at(0x3c) as usize,
            u16_at(0x3e) as usize,
        );
        let header = |i: usize| shoff + i * shentsize;
        let names = u64_at(file, header(shstrndx) + 0x18) as usize;
        let sections = (0..shnum)
            .map(|i| {
                let h = header(i);
                Section {
                    name: String::from_utf8_lossy(str_at(file, names + u32_at(file, h) as usize))
                        .into_owned(),
                    kind: u32_at(file, h + 4),
                    addr: u64_at(file, h + 0x10),
                    offset: u64_at(file, h + 0x18) as usize,
                    size: u64_at(file, h + 0x20) as usize,
                }
            })
            .collect();
        Self { sections }
    }

    fn find(&self, name: &str) -> &Section {
        self.sections
            .iter()
            .find(|s| s.name == name)
            .unwrap_or_else(|| panic!("no {name} section"))
    }

    /// The file offset and size of section `name`.
    fn section(&self, name: &str) -> (usize, usize) {
        let section = self.find(name);
        (section.offset, section.size)
    }

    /// The file offset of virtual address `vaddr`, if a section holds it.
    fn offset_of(&self, vaddr: u64) -> Option<usize> {
        self.sections
            .iter()
            .find(|s| s.addr != 0 && vaddr >= s.addr && vaddr < s.addr + s.size as u64)
            .map(|s| s.offset + (vaddr - s.addr) as usize)
    }

    /// Each relocation's file offset and the virtual address it writes.
    fn relocations<'a>(&'a self, file: &'a [u8]) -> impl Iterator<Item = (usize, u64)> + 'a {
        self.sections
            .iter()
            .filter(|s| s.kind == SHT_RELA)
            .flat_map(|s| (s.offset..s.offset + s.size).step_by(RELA_SIZE))
            .map(|at| (at, u64_at(file, at)))
    }

    /// The file offsets of every relocated word.
    fn relocated(&self, file: &[u8]) -> Vec<usize> {
        self.relocations(file)
            .filter_map(|(_, vaddr)| self.offset_of(vaddr))
            .collect()
    }

    /// The file offset of a relocation in `.rela.dyn` that writes section
    /// `name`.
    fn relocation_into(&self, file: &[u8], name: &str) -> usize {
        let rela = self.find(".rela.dyn");
        let target = self.find(name);
        self.relocations(file)
            .find(|&(at, vaddr)| {
                at >= rela.offset
                    && at < rela.offset + rela.size
                    && vaddr >= target.addr
                    && vaddr < target.addr + target.size as u64
            })
            .map(|(at, _)| at)
            .unwrap_or_else(|| panic!("no relocation in .rela.dyn writes {name}"))
    }

    /// The file offset of dynamic symbol `name`'s first byte.
    fn symbol(&self, file: &[u8], name: &str) -> usize {
        let (symbols, strings) = (self.find(".dynsym"), self.find(".dynstr"));
        (symbols.offset..symbols.offset + symbols.size)
            .step_by(SYM_SIZE)
            .find(|&at| str_at(file, strings.offset + u32_at(file, at) as usize) == name.as_bytes())
            .and_then(|at| self.offset_of(u64_at(file, at + 8)))
            .unwrap_or_else(|| panic!("no dynamic symbol {name}"))
    }
}
