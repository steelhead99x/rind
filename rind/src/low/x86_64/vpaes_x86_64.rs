// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES on SSSE3 alone, using aws-lc's `vpaes-x86_64` routines, for CPUs
//! without AES-NI.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. Its S-box is
//! Mike Hamburg's vector permutation AES, which computes with `pshufb` lookups
//! into registers, never memory, so its timing is independent of the key and
//! data. It is not formally verified: its correctness rests on its use and
//! testing in OpenSSL, BoringSSL, and aws-lc, and on rind's tests of it
//! against AES-NI, Wycheproof, and aws-lc-rs.

use super::cpu::HaveSsse3;
use crate::low;

/// An expanded AES-128, AES-192, or AES-256 encryption key, in vpaes's own format:
/// aws-lc's `AES_KEY`.
#[repr(C, align(16))]
pub(crate) struct VpaesKey {
    rd_key: [u32; 60],
    rounds: u32,
}

impl VpaesKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveSsse3) -> Self {
        let mut r = Self {
            rd_key: [0; 60],
            rounds: 0,
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and `r` is an
        // `AES_KEY`. The
        // routines need only SSSE3, which the token proves.
        let ret = unsafe {
            asm_call!(unsafe extern "sysv64" vpaes_set_encrypt_key(key.as_ptr(), key_bits(key), &mut r))
        };
        // aws-lc's always succeeds.
        assert_eq!(ret, 0);
        r
    }

    /// The key's length in bytes, from the `nbits / 32 + 5` rounds that
    /// `vpaes_set_encrypt_key` stores.
    pub(crate) fn key_len(&self) -> usize {
        (self.rounds as usize - 5) * 4
    }

    /// Encrypts one block.
    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        let mut out = [0u8; 16];
        // SAFETY: `block` is one readable block and `out` one writable one,
        // and `self` an expanded key, which only a `HaveSsse3` token builds.
        unsafe {
            asm_call!(unsafe extern "sysv64" vpaes_encrypt(block.as_ptr(), out.as_mut_ptr(), self))
        };
        out
    }

    /// XORs counter-mode keystream into whole blocks.
    ///
    /// The counter blocks are `ivec`, then `ivec` with its last four bytes,
    /// a big-endian counter, incremented with 32-bit wrapping.
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [[u8; 16]]) {
        let io = inout.as_mut_ptr().cast::<u8>();
        // SAFETY: `inout` is `inout.len()` readable and writable blocks, which
        // aws-lc allows to alias, and `self` an expanded key, which only a
        // `HaveSsse3` token builds. The routine returns at once for zero
        // blocks.
        unsafe {
            asm_call!(unsafe extern "sysv64" vpaes_ctr32_encrypt_blocks(
                io,
                io,
                inout.len(),
                self,
                ivec,
            ))
        }
    }

    /// Encrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_encrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        // SAFETY: as for `ctr32`; the routine returns at once for zero bytes.
        unsafe { cbc(blocks, (self as *const Self).cast(), iv, 1) }
    }
}

impl Drop for VpaesKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for VpaesKey {}

/// An expanded AES-128, AES-192, or AES-256 decryption key, in vpaes's own format:
/// aws-lc's `AES_KEY`.
#[repr(C, align(16))]
pub(crate) struct VpaesDecKey {
    rd_key: [u32; 60],
    rounds: u32,
}

impl VpaesDecKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveSsse3) -> Self {
        let mut r = Self {
            rd_key: [0; 60],
            rounds: 0,
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and `r` is an
        // `AES_KEY`. The
        // routines need only SSSE3, which the token proves.
        let ret = unsafe {
            asm_call!(unsafe extern "sysv64" vpaes_set_decrypt_key(key.as_ptr(), key_bits(key), &mut r))
        };
        // aws-lc's always succeeds.
        assert_eq!(ret, 0);
        r
    }

    /// Decrypts one block in place.
    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        let io = inout.as_mut_ptr();
        // SAFETY: `inout` is one readable and writable block, which aws-lc
        // allows to alias, and `self` an expanded decryption key, which only a
        // `HaveSsse3` token builds.
        unsafe { asm_call!(unsafe extern "sysv64" vpaes_decrypt(io, io, self)) }
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        // SAFETY: as for `decrypt_block`, over `blocks.len()` blocks; the
        // routine returns at once for zero bytes.
        unsafe { cbc(blocks, (self as *const Self).cast(), iv, 0) }
    }
}

impl Drop for VpaesDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for VpaesDecKey {}

/// Runs `vpaes_cbc_encrypt` over `blocks` in place, encrypting under a
/// [`VpaesKey`] if `enc` is 1 or decrypting under a [`VpaesDecKey`] if 0.
///
/// # Safety
///
/// `key` must be that key, which only a `HaveSsse3` token builds.
unsafe fn cbc(blocks: &mut [[u8; 16]], key: *const u8, iv: &[u8; 16], enc: i32) {
    // The routine leaves the next IV here; CBC callers here start afresh.
    let mut ivec = *iv;
    let io = blocks.as_mut_ptr().cast::<u8>();
    // SAFETY: `blocks` is `16 * blocks.len()` readable and writable bytes,
    // which aws-lc allows to alias, and the caller vouches for `key`.
    unsafe {
        asm_call!(unsafe extern "sysv64" vpaes_cbc_encrypt(
            io,
            io,
            16 * blocks.len(),
            key,
            &mut ivec,
            enc,
        ))
    }
}

/// `key`'s length in bits, which vpaes's key schedules take.
fn key_bits(key: &[u8]) -> u32 {
    match key.len() {
        16 => 128,
        24 => 192,
        32 => 256,
        _ => unreachable!("callers check the AES key length"),
    }
}

/// aws-lc's `_vpaes_consts`, as aligned as aws-lc places it: the routines
/// load it with `movdqa`.
#[repr(C, align(64))]
struct Consts([u64; 104]);

static VPAES_CONSTS: Consts = Consts(include!("aws_lc/vpaes-x86_64.vpaes_consts.rs"));

/// Defines a naked function running an imported routine, which reaches its
/// table and helpers through the `sym` operands listed. Each takes the System
/// V ABI on every OS, since its text is aws-lc's ELF and Mach-O flavors.
macro_rules! vpaes_routine {
    ($name:ident($($arg:ident: $ty:ty),*) $(-> $ret:ty)? { $($op:ident = $sym:ident),* }) => {
        #[unsafe(naked)]
        unsafe extern "sysv64" fn $name($($arg: $ty),*) $(-> $ret)? {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".linux.s"))
                $(, $op = sym $sym)*,
                options(att_syntax),
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".apple.s"))
                $(, $op = sym $sym)*,
                options(att_syntax),
            );
        }
    };
}

vpaes_routine!(vpaes_set_encrypt_key(user_key: *const u8, bits: u32, key: *mut VpaesKey) -> i32 {
    vpaes_schedule_core = vpaes_schedule_core
});
vpaes_routine!(vpaes_set_decrypt_key(user_key: *const u8, bits: u32, key: *mut VpaesDecKey) -> i32 {
    vpaes_schedule_core = vpaes_schedule_core
});
vpaes_routine!(vpaes_encrypt(input: *const u8, output: *mut u8, key: *const VpaesKey) {
    vpaes_preheat = vpaes_preheat,
    vpaes_encrypt_core = vpaes_encrypt_core
});
vpaes_routine!(vpaes_decrypt(input: *const u8, output: *mut u8, key: *const VpaesDecKey) {
    vpaes_preheat = vpaes_preheat,
    vpaes_decrypt_core = vpaes_decrypt_core
});
vpaes_routine!(vpaes_ctr32_encrypt_blocks(
    input: *const u8,
    output: *mut u8,
    blocks: usize,
    key: *const VpaesKey,
    ivec: *const [u8; 16]
) {
    vpaes_consts = VPAES_CONSTS,
    vpaes_preheat = vpaes_preheat,
    vpaes_encrypt_core = vpaes_encrypt_core,
    vpaes_encrypt_core_2x = vpaes_encrypt_core_2x
});

vpaes_routine!(vpaes_cbc_encrypt(
    input: *const u8,
    output: *mut u8,
    len: usize,
    key: *const u8,
    ivec: *mut [u8; 16],
    enc: i32
) {
    vpaes_preheat = vpaes_preheat,
    vpaes_encrypt_core = vpaes_encrypt_core,
    vpaes_decrypt_core = vpaes_decrypt_core
});

// The routines' helpers, which pass their arguments in registers of their
// own choosing rather than by the C ABI, so only the routines call them.
vpaes_routine!(vpaes_preheat() { vpaes_consts = VPAES_CONSTS });
vpaes_routine!(vpaes_encrypt_core() { vpaes_consts = VPAES_CONSTS });
vpaes_routine!(vpaes_encrypt_core_2x() { vpaes_consts = VPAES_CONSTS });
vpaes_routine!(vpaes_decrypt_core() { vpaes_consts = VPAES_CONSTS });
vpaes_routine!(vpaes_schedule_core() {
    vpaes_consts = VPAES_CONSTS,
    vpaes_preheat = vpaes_preheat,
    vpaes_schedule_192_smear = vpaes_schedule_192_smear,
    vpaes_schedule_round = vpaes_schedule_round,
    vpaes_schedule_low_round = vpaes_schedule_low_round,
    vpaes_schedule_transform = vpaes_schedule_transform,
    vpaes_schedule_mangle = vpaes_schedule_mangle
});
vpaes_routine!(vpaes_schedule_192_smear() {});
vpaes_routine!(vpaes_schedule_round() { vpaes_consts = VPAES_CONSTS });
vpaes_routine!(vpaes_schedule_low_round() { vpaes_consts = VPAES_CONSTS });
vpaes_routine!(vpaes_schedule_transform() {});
vpaes_routine!(vpaes_schedule_mangle() { vpaes_consts = VPAES_CONSTS });
