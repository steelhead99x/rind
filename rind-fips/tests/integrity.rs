// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The module refuses to load once any byte its integrity test covers
//! changes: code, constants, relocation tables, or the constants beside
//! relocated pointers.
//!
//! Each case copies the built module, flips one byte, and runs this test
//! binary again with the copy first on its library path, so the dynamic
//! loader runs the copy's integrity test before anything else.

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

#[test]
fn tampering_fails_the_integrity_test() {
    let module = std::fs::read(MODULE).unwrap();
    let elf = Elf::parse(&module);
    let relocated = elf.relocated(&module);
    let in_section = |name: &str, pick: &dyn Fn(usize, usize) -> Option<usize>| {
        let (offset, size) = elf.section(&module, name);
        pick(offset, size).unwrap_or_else(|| panic!("no byte to flip in {name}"))
    };

    let cases = [
        (".text", in_section(".text", &|o, s| Some(o + s / 2))),
        (".rodata", in_section(".rodata", &|o, s| Some(o + s / 2))),
        (".rela.dyn", in_section(".rela.dyn", &|o, _| Some(o + 16))),
        // A byte of `.data.rel.ro` that no relocation writes, such as a
        // string's length beside its pointer.
        (
            ".data.rel.ro",
            in_section(".data.rel.ro", &|o, s| {
                (o..o + s).find(|&at| {
                    module[at] != 0 && !relocated.iter().any(|&r| at >= r && at < r + 8)
                })
            }),
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

/// Just enough of a little-endian ELF64 file to find sections and
/// relocations.
struct Elf {
    sections: Vec<(String, u32, usize, usize, u64)>,
}

impl Elf {
    fn parse(file: &[u8]) -> Self {
        let u16_at = |at: usize| u16::from_le_bytes(file[at..at + 2].try_into().unwrap());
        let u32_at = |at: usize| u32::from_le_bytes(file[at..at + 4].try_into().unwrap());
        let u64_at = |at: usize| u64::from_le_bytes(file[at..at + 8].try_into().unwrap());
        let shoff = u64_at(0x28) as usize;
        let (shentsize, shnum, shstrndx) = (
            u16_at(0x3a) as usize,
            u16_at(0x3c) as usize,
            u16_at(0x3e) as usize,
        );
        let header = |i: usize| shoff + i * shentsize;
        let names = u64_at(header(shstrndx) + 0x18) as usize;
        let sections = (0..shnum)
            .map(|i| {
                let h = header(i);
                let name_at = names + u32_at(h) as usize;
                let len = file[name_at..].iter().position(|&b| b == 0).unwrap();
                (
                    String::from_utf8_lossy(&file[name_at..name_at + len]).into_owned(),
                    u32_at(h + 4),
                    u64_at(h + 0x18) as usize,
                    u64_at(h + 0x20) as usize,
                    u64_at(h + 0x10),
                )
            })
            .collect();
        Self { sections }
    }

    /// The file offset and size of section `name`.
    fn section(&self, _file: &[u8], name: &str) -> (usize, usize) {
        let (_, _, offset, size, _) = self.sections.iter().find(|s| s.0 == name).unwrap();
        (*offset, *size)
    }

    /// The file offsets of every relocated word.
    fn relocated(&self, file: &[u8]) -> Vec<usize> {
        let to_offset = |vaddr: u64| {
            self.sections
                .iter()
                .find(|(_, _, _, size, addr)| {
                    *addr != 0 && vaddr >= *addr && vaddr < addr + *size as u64
                })
                .map(|(_, _, offset, _, addr)| offset + (vaddr - addr) as usize)
        };
        self.sections
            .iter()
            // SHT_RELA
            .filter(|s| s.1 == 4)
            .flat_map(|(_, _, offset, size, _)| (*offset..offset + size).step_by(24))
            .filter_map(|at| to_offset(u64::from_le_bytes(file[at..at + 8].try_into().unwrap())))
            .collect()
    }
}
