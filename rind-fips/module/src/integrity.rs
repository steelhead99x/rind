// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The software integrity test: an HMAC-SHA-256 over the module as loaded,
//! compared with the value `rind-fips`'s build script computed from the
//! linked library and wrote into it.

use core::cell::UnsafeCell;
use core::ffi::{c_int, c_void};

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
        for i in 0..count {
            let at = loaded.base + table + i * size_of::<Rela>() as u64;
            // SAFETY: the build script found these tables in a read-only
            // segment, which is mapped while the module is loaded.
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

/// Finds the loaded object holding this module's code.
fn find_self() -> Option<Loaded> {
    let mut found: Option<Loaded> = None;
    // SAFETY: the callback reads only what the loader passes it.
    unsafe {
        libc::dl_iterate_phdr(Some(visit), (&raw mut found).cast());
    }
    found
}

unsafe extern "C" fn visit(
    info: *mut libc::dl_phdr_info,
    _size: usize,
    data: *mut c_void,
) -> c_int {
    // SAFETY: the loader passes a valid `info`, and `data` is `find_self`'s.
    let (info, found) = unsafe { (&*info, &mut *data.cast::<Option<Loaded>>()) };
    let base = info.dlpi_addr;
    let marker = (&raw const LAYOUT) as u64;
    // SAFETY: the loader's program headers for this object.
    let headers = unsafe { core::slice::from_raw_parts(info.dlpi_phdr, info.dlpi_phnum.into()) };
    let ours = headers.iter().any(|h| {
        h.p_type == image::PT_LOAD
            && marker >= base + h.p_vaddr
            && marker - (base + h.p_vaddr) < h.p_memsz
    });
    if !ours {
        return 0;
    }
    *found = Some(Loaded {
        base,
        segments: headers
            .iter()
            .map(|h| Segment {
                kind: h.p_type,
                flags: h.p_flags,
                vaddr: h.p_vaddr,
                filesz: h.p_filesz,
            })
            .collect(),
    });
    1
}
