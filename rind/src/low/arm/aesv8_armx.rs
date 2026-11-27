// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES with the AArch32 crypto extension, using aws-lc's `aesv8-armx` routines.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. It is not
//! formally verified: its correctness rests on its use and testing in OpenSSL,
//! BoringSSL, and aws-lc, and on rind's tests of it against the portable code,
//! Wycheproof, and aws-lc-rs.

use super::cpu::HaveCryptoExt;
use crate::low;

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("aes_hw_set_encrypt_key")]
    fn aes_hw_set_encrypt_key(user_key: *const u8, bits: i32, key: *mut AesHwKey) -> i32;

    #[link_name = aws_lc_symbol!("aes_hw_set_decrypt_key")]
    fn aes_hw_set_decrypt_key(user_key: *const u8, bits: i32, key: *mut AesHwDecKey) -> i32;

    #[link_name = aws_lc_symbol!("aes_hw_encrypt")]
    fn aes_hw_encrypt(input: *const u8, output: *mut u8, key: *const AesHwKey);

    #[link_name = aws_lc_symbol!("aes_hw_decrypt")]
    fn aes_hw_decrypt(input: *const u8, output: *mut u8, key: *const AesHwDecKey);

    #[link_name = aws_lc_symbol!("aes_hw_ctr32_encrypt_blocks")]
    fn aes_hw_ctr32_encrypt_blocks(
        input: *const u8,
        output: *mut u8,
        blocks: usize,
        key: *const AesHwKey,
        ivec: *const [u8; 16],
    );

    /// Encrypts under an [`AesHwKey`] if `enc` is 1, or decrypts under an
    /// [`AesHwDecKey`] if 0.
    #[link_name = aws_lc_symbol!("aes_hw_cbc_encrypt")]
    fn aes_hw_cbc_encrypt(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const u8,
        ivec: *mut [u8; 16],
        enc: i32,
    );
}

// aws-lc assembles these in ARM mode with NEON, encoding the ARMv8
// instructions as bytes. Restoring `.fpu` afterwards keeps the object's build
// attributes at the target's ARMv7 VFPv3, rather than marking it as needing
// NEON.
core::arch::global_asm!(
    ".text",
    ".fpu neon",
    ".code 32",
    include_str!("aws_lc/aesv8-armx.s"),
    ".fpu vfpv3",
    aes_hw_set_encrypt_key = sym aes_hw_set_encrypt_key,
    aes_hw_set_decrypt_key = sym aes_hw_set_decrypt_key,
    aes_hw_encrypt = sym aes_hw_encrypt,
    aes_hw_decrypt = sym aes_hw_decrypt,
    aes_hw_ctr32_encrypt_blocks = sym aes_hw_ctr32_encrypt_blocks,
    aes_hw_cbc_encrypt = sym aes_hw_cbc_encrypt,
);

/// An expanded AES-128, AES-192, or AES-256 encryption key: aws-lc's `AES_KEY`.
#[repr(C, align(16))]
pub(crate) struct AesHwKey {
    rd_key: [u32; 60],
    rounds: u32,
}

impl AesHwKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveCryptoExt) -> Self {
        let mut r = Self {
            rd_key: [0; 60],
            rounds: 0,
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and `r` is an
        // `AES_KEY`. The token proves the CPU has the AES instructions.
        let ret = unsafe {
            asm_call!(unsafe extern "C" aes_hw_set_encrypt_key(key.as_ptr(), key_bits(key), &mut r))
        };
        // aws-lc refuses only a null pointer or another key size.
        assert_eq!(ret, 0);
        r
    }

    /// The key's length in bytes, from the 10, 12, or 14 rounds that
    /// `aes_hw_set_encrypt_key` stores.
    pub(crate) fn key_len(&self) -> usize {
        self.rounds as usize * 4 - 24
    }

    /// Encrypts one block.
    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        let mut out = [0u8; 16];
        // SAFETY: `block` is one readable block and `out` one writable one.
        // Only a `HaveCryptoExt` token builds `self`.
        unsafe {
            asm_call!(unsafe extern "C" aes_hw_encrypt(block.as_ptr(), out.as_mut_ptr(), self))
        };
        out
    }

    /// XORs counter-mode keystream into whole blocks.
    ///
    /// The counter blocks are `ivec`, then `ivec` with its last four bytes,
    /// a big-endian counter, incremented with 32-bit wrapping.
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [[u8; 16]]) {
        // One pointer for input and output, so neither reborrow invalidates
        // the other.
        let io = inout.as_mut_ptr().cast::<u8>();
        // SAFETY: `io` is `inout.len()` readable and writable blocks, which
        // aws-lc allows to alias. Only a `HaveCryptoExt` token builds `self`.
        unsafe {
            asm_call!(unsafe extern "C" aes_hw_ctr32_encrypt_blocks(
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
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { cbc(blocks, (self as *const Self).cast(), iv, 1) }
    }
}

impl Drop for AesHwKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for AesHwKey {}

/// An expanded AES-128, AES-192, or AES-256 decryption key: aws-lc's `AES_KEY`.
#[repr(C, align(16))]
pub(crate) struct AesHwDecKey {
    rd_key: [u32; 60],
    rounds: u32,
}

impl AesHwDecKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveCryptoExt) -> Self {
        let mut r = Self {
            rd_key: [0; 60],
            rounds: 0,
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and `r` is an
        // `AES_KEY`. The token proves the CPU has the AES instructions.
        let ret = unsafe {
            asm_call!(unsafe extern "C" aes_hw_set_decrypt_key(key.as_ptr(), key_bits(key), &mut r))
        };
        // aws-lc refuses only a null pointer or another key size.
        assert_eq!(ret, 0);
        r
    }

    /// Decrypts one block in place.
    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        let io = inout.as_mut_ptr();
        // SAFETY: `io` is one readable and writable block, which aws-lc
        // allows to alias. Only a `HaveCryptoExt` token builds `self`.
        unsafe { asm_call!(unsafe extern "C" aes_hw_decrypt(io, io, self)) }
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { cbc(blocks, (self as *const Self).cast(), iv, 0) }
    }
}

/// Runs `aes_hw_cbc_encrypt` over `blocks` in place.
///
/// # Safety
///
/// `key` must be the [`AesHwKey`] or [`AesHwDecKey`] for `enc`, which only a
/// `HaveCryptoExt` token builds.
unsafe fn cbc(blocks: &mut [[u8; 16]], key: *const u8, iv: &[u8; 16], enc: i32) {
    // The routine leaves the next IV here; CBC callers here start afresh.
    let mut ivec = *iv;
    let io = blocks.as_mut_ptr().cast::<u8>();
    // SAFETY: `io` is `16 * blocks.len()` readable and writable bytes,
    // which aws-lc allows to alias, and the caller vouches for `key`. The
    // routine returns at once for fewer than 16 bytes.
    unsafe {
        asm_call!(unsafe extern "C" aes_hw_cbc_encrypt(
            io,
            io,
            16 * blocks.len(),
            key,
            &mut ivec,
            enc,
        ))
    }
}

impl Drop for AesHwDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for AesHwDecKey {}

/// `key`'s length in bits, which aws-lc's key schedules take.
fn key_bits(key: &[u8]) -> i32 {
    match key.len() {
        16 => 128,
        24 => 192,
        32 => 256,
        _ => unreachable!("callers check the AES key length"),
    }
}
