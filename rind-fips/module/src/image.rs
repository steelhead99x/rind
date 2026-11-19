// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! What the integrity test hashes: the module's read-only segments (its
//! code, constants, and relocation tables), then its RELRO region, whose
//! relocated words hash as what they are relative to the module's base, so
//! the dynamic loader's work does not change the hash and tampering with
//! the constants beside them does.
//!
//! `rind-fips`'s build script includes this file to compute the hash from the
//! linked library, and the module to recompute it from itself as loaded, so
//! both hash the same bytes by construction.

/// The integrity test's HMAC-SHA-256 key: fixed and public, as aws-lc's is,
/// since the test detects corruption, not an attacker who can rewrite it.
pub(crate) const HMAC_KEY: [u8; 32] = [0; 32];

/// Bytes `rind-fips`'s build script finds, then overwrites with the
/// expected hash: in a writable segment, which the hash leaves out.
pub(crate) const EXPECTED_PLACEHOLDER: [u8; 32] = *b"rind-fips: expected module HMAC!";

/// Bytes `rind-fips`'s build script finds, then follows with the location of
/// the relocation tables, before hashing: in a read-only segment, so the
/// hash covers what it writes.
pub(crate) const LAYOUT_MAGIC: [u8; 16] = *b"rind-fips layout";

/// The relocation tables' places, as the build script writes them after
/// [`LAYOUT_MAGIC`]: each table's virtual address and entry count.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub(crate) struct Layout {
    pub(crate) rela: u64,
    pub(crate) rela_count: u64,
    pub(crate) jmprel: u64,
    pub(crate) jmprel_count: u64,
}

/// [`LAYOUT_MAGIC`], then the [`Layout`], as the module holds them.
#[repr(C)]
pub(crate) struct Marked {
    pub(crate) magic: [u8; 16],
    pub(crate) layout: Layout,
}

pub(crate) const PT_LOAD: u32 = 1;
pub(crate) const PT_DYNAMIC: u32 = 2;
pub(crate) const PT_GNU_RELRO: u32 = 0x6474_e552;
pub(crate) const PF_W: u32 = 2;

/// A program header's fields that the hash reads.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Segment {
    pub(crate) kind: u32,
    pub(crate) flags: u32,
    pub(crate) vaddr: u64,
    pub(crate) filesz: u64,
}

/// An `Elf64_Rela`.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub(crate) struct Rela {
    pub(crate) offset: u64,
    pub(crate) info: u64,
    pub(crate) addend: i64,
}

impl Rela {
    pub(crate) fn kind(&self) -> u32 {
        self.info as u32
    }
}

/// The relocation types a module may hold, by how the hash treats them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// The base plus the addend: hashed as the addend.
    Relative,
    /// A symbol's address, or a TLS offset, which only the loader knows:
    /// hashed as zeros, this many 8-byte words.
    Symbol(usize),
}

/// How the hash treats relocation type `kind` on `arch`, or `None` if a
/// module must not hold it.
pub(crate) fn kind(arch: Arch, kind: u32) -> Option<Kind> {
    match (arch, kind) {
        // R_X86_64_RELATIVE, R_AARCH64_RELATIVE
        (Arch::X86_64, 8) | (Arch::Aarch64, 1027) => Some(Kind::Relative),
        // R_X86_64_64, GLOB_DAT, JUMP_SLOT, DTPMOD64, DTPOFF64, TPOFF64
        (Arch::X86_64, 1 | 6 | 7 | 16 | 17 | 18) => Some(Kind::Symbol(1)),
        // R_AARCH64_ABS64, GLOB_DAT, JUMP_SLOT, TLS_DTPMOD64, TLS_DTPREL64,
        // TLS_TPREL64
        (Arch::Aarch64, 257 | 1025 | 1026 | 1028 | 1029 | 1030) => Some(Kind::Symbol(1)),
        // R_AARCH64_TLSDESC, two words
        (Arch::Aarch64, 1031) => Some(Kind::Symbol(2)),
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "build.rs hashes either architecture's module; the module only its own"
)]
pub(crate) enum Arch {
    X86_64,
    Aarch64,
}

/// The module, read either from its file or from memory as loaded.
pub(crate) trait Image {
    /// The `len` bytes at virtual address `vaddr`.
    fn bytes(&self, vaddr: u64, len: u64) -> &[u8];

    /// What the word `rela` relocates hashes as, if it is relative: its
    /// addend in the file, its value less the base in memory.
    fn relative(&self, rela: &Rela) -> u64;
}

/// Feeds `update` the bytes the integrity test hashes, given the module's
/// program headers and its relocations. Fails, naming the reason, if a
/// relocation is of a type a module must not hold, or lands in a read-only
/// segment, where it would change hashed bytes.
pub(crate) fn hash(
    image: &impl Image,
    arch: Arch,
    segments: &[Segment],
    relas: &mut [Rela],
    mut update: impl FnMut(&[u8]),
) -> Result<(), &'static str> {
    let in_segment = |s: &Segment, vaddr: u64| vaddr >= s.vaddr && vaddr - s.vaddr < s.filesz;

    for segment in segments {
        if segment.kind == PT_LOAD && segment.flags & PF_W == 0 {
            if relas.iter().any(|r| in_segment(segment, r.offset)) {
                return Err("a relocation lands in a read-only segment");
            }
            update(image.bytes(segment.vaddr, segment.filesz));
        }
    }

    let dynamic = segments.iter().find(|s| s.kind == PT_DYNAMIC);
    let Some(relro) = segments.iter().find(|s| s.kind == PT_GNU_RELRO) else {
        return Err("no RELRO segment");
    };

    relas.sort_unstable_by_key(|r| r.offset);
    let mut at = relro.vaddr;
    let end = relro.vaddr + relro.filesz;
    let mut relas = relas
        .iter()
        .filter(|r| in_segment(relro, r.offset))
        .peekable();
    while at < end {
        // The dynamic section, which the loader may adjust in place, is
        // left out.
        if let Some(dynamic) = dynamic.filter(|d| in_segment(d, at)) {
            at = dynamic.vaddr + dynamic.filesz;
            while relas.next_if(|r| r.offset < at).is_some() {}
            continue;
        }
        let next = relas.peek().map_or(end, |r| r.offset);
        let next = dynamic
            .map(|d| d.vaddr)
            .filter(|&d| d > at && d < next)
            .unwrap_or(next);
        if next > at {
            update(image.bytes(at, next - at));
            at = next;
            continue;
        }
        let rela = relas.next().unwrap();
        if rela.offset < at {
            return Err("relocations overlap");
        }
        match kind(arch, rela.kind()) {
            Some(Kind::Relative) => {
                update(&image.relative(rela).to_le_bytes());
                at += 8;
            }
            Some(Kind::Symbol(words)) => {
                for _ in 0..words {
                    update(&[0; 8]);
                }
                at += 8 * words as u64;
            }
            None => return Err("an unexpected relocation type"),
        }
    }
    Ok(())
}
