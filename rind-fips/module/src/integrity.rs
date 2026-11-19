// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The software integrity test: an HMAC-SHA-256 over the module as loaded,
//! compared with the value `rind-fips`'s build script computed from the
//! linked library and wrote into it.

use core::cell::UnsafeCell;

use rind::hmac;

use crate::image::{
    self, Arch, EXPECTED_PLACEHOLDER, Image, LAYOUT_MAGIC, Layout, Marked, Rela, Segment,
};

/// The expected HMAC. Interior mutability puts it in a writable segment,
/// which the hash leaves out, so writing it changes nothing hashed.
#[repr(transparent)]
struct Expected(UnsafeCell<[u8; 32]>);

// SAFETY: only the build script writes it, before the library is loaded.
unsafe impl Sync for Expected {}

#[used]
static EXPECTED: Expected = Expected(UnsafeCell::new(EXPECTED_PLACEHOLDER));

/// The [`Layout`] the build script writes: in a read-only segment, so the
/// hash covers it.
#[used]
static LAYOUT: Marked = Marked {
    magic: LAYOUT_MAGIC,
    layout: Layout {
        rela: 0,
        rela_count: 0,
        jmprel: 0,
        jmprel_count: 0,
    },
};

#[cfg(target_arch = "x86_64")]
const ARCH: Arch = Arch::X86_64;
#[cfg(target_arch = "aarch64")]
const ARCH: Arch = Arch::Aarch64;

/// Runs the integrity test, returning whether the module is as built.
pub(crate) fn check() -> bool {
    let Some(loaded) = find_self() else {
        return false;
    };
    // SAFETY: both statics are as the build script left them, and volatile
    // reads keep the compiler from assuming their initial values.
    let (layout, mut expected) = unsafe {
        (
            core::ptr::read_volatile(&LAYOUT.layout),
            core::ptr::read_volatile(EXPECTED.0.get()),
        )
    };
    if rind::fips::broken("integrity") {
        expected[0] ^= 1;
    }

    let mut relas = Vec::new();
    for (table, count) in [
        (layout.rela, layout.rela_count),
        (layout.jmprel, layout.jmprel_count),
    ] {
        // The layout is checked only by the hash below, so a corrupted one
        // must fail the test rather than send these reads off the module.
        let end =
            (count.checked_mul(size_of::<Rela>() as u64)).and_then(|len| table.checked_add(len));
        let mapped = end.is_some_and(|end| {
            loaded.segments.iter().any(|s| {
                s.kind == image::PT_LOAD
                    && s.flags & image::PF_W == 0
                    && table >= s.vaddr
                    && end <= s.vaddr + s.filesz
            })
        });
        if count > 0 && !mapped {
            return false;
        }
        for i in 0..count {
            let at = loaded.base + table + i * size_of::<Rela>() as u64;
            // SAFETY: the table lies within a read-only segment, as checked
            // above, which is mapped while the module is loaded.
            relas.push(unsafe { core::ptr::read_unaligned(at as *const Rela) });
        }
    }

    let key = hmac::Key::new(&hmac::HMAC_SHA256, &image::HMAC_KEY);
    let mut context = hmac::Context::with_key(&key);
    let hashed = image::hash(&loaded, ARCH, &loaded.segments, &mut relas, |bytes| {
        context.update(bytes)
    });
    hashed.is_ok() && rind::constant_time::verify(context.sign().as_ref(), &expected).is_ok()
}

/// The module as mapped: its base address and program headers.
struct Loaded {
    base: u64,
    segments: Vec<Segment>,
}

impl Image for Loaded {
    fn bytes(&self, vaddr: u64, len: u64) -> &[u8] {
        // SAFETY: `hash` asks only for bytes within the module's segments,
        // which stay mapped while it is loaded.
        unsafe { core::slice::from_raw_parts((self.base + vaddr) as *const u8, len as usize) }
    }

    fn relative(&self, rela: &Rela) -> u64 {
        // SAFETY: as for `bytes`; the loader wrote this word.
        let value = unsafe { core::ptr::read_unaligned((self.base + rela.offset) as *const u64) };
        value.wrapping_sub(self.base)
    }
}

unsafe extern "C" {
    /// The module's ELF header, which the linker defines at the start of
    /// its first segment.
    static __ehdr_start: u8;
}

/// Finds the module as mapped from its own ELF header, without the dynamic
/// loader: `dl_iterate_phdr` takes the loader's lock, which `fork` does not
/// reset, so a child forked while another thread held it would hang in the
/// integrity test.
fn find_self() -> Option<Loaded> {
    let header = (&raw const __ehdr_start).cast::<u8>();
    let read = |at: usize, len: usize| -> u64 {
        let mut word = [0u8; 8];
        // SAFETY: the ELF header and its program headers are in the
        // module's first segment, mapped while it is loaded.
        unsafe { core::ptr::copy_nonoverlapping(header.add(at), word.as_mut_ptr(), len) };
        u64::from_le_bytes(word)
    };
    let (phoff, phentsize, phnum) = (read(0x20, 8), read(0x36, 2), read(0x38, 2));
    // Every linker places the program headers right after the 64-byte ELF
    // header, and the page holding the header is mapped, so a table that
    // ends within that page is readable whatever else the header says.
    if phoff != 64 || phentsize != 56 || phoff + phnum * phentsize > 4096 {
        return None;
    }
    let segments: Vec<Segment> = (0..phnum)
        .map(|i| {
            let at = (phoff + i * phentsize) as usize;
            Segment {
                kind: read(at, 4) as u32,
                flags: read(at + 4, 4) as u32,
                vaddr: read(at + 0x10, 8),
                filesz: read(at + 0x20, 8),
            }
        })
        .collect();
    // The header's address is the base only if the first segment maps the
    // start of the file at address zero, as a shared library's does.
    let first = segments.iter().find(|s| s.kind == image::PT_LOAD)?;
    if first.vaddr != 0 || first.filesz < phoff + phnum * phentsize {
        return None;
    }
    Some(Loaded {
        base: header as u64,
        segments,
    })
}
