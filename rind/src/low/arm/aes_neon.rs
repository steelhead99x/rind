// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES with NEON but without the crypto extension, using aws-lc's `vpaes-armv7`
//! and `bsaes-armv7` routines.
//!
//! `vpaes` (vector permutes, no table indexed by a secret) runs key schedules
//! and single blocks. `bsaes` (bitsliced) runs counter mode and CBC decryption,
//! eight blocks at a time. Both are constant time. A key holds its `vpaes`
//! schedule and the `bsaes` form of it, converted when the key is built, so a
//! key works for every mode.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. It is not
//! formally verified: its correctness rests on its use and testing in OpenSSL,
//! BoringSSL, and aws-lc, and on rind's tests of it against the portable code,
//! Wycheproof, and aws-lc-rs.

use super::cpu::HaveNeon;
use crate::low;

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("vpaes_set_encrypt_key")]
    fn vpaes_set_encrypt_key(user_key: *const u8, bits: i32, key: *mut Schedule) -> i32;

    #[link_name = aws_lc_symbol!("vpaes_set_decrypt_key")]
    fn vpaes_set_decrypt_key(user_key: *const u8, bits: i32, key: *mut Schedule) -> i32;

    #[link_name = aws_lc_symbol!("vpaes_encrypt")]
    fn vpaes_encrypt(input: *const u8, output: *mut u8, key: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_decrypt")]
    fn vpaes_decrypt(input: *const u8, output: *mut u8, key: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_ctr32_encrypt_blocks")]
    fn vpaes_ctr32_encrypt_blocks(
        input: *const u8,
        output: *mut u8,
        blocks: usize,
        key: *const Schedule,
        ivec: *const [u8; 16],
    );

    #[link_name = aws_lc_symbol!("vpaes_encrypt_key_to_bsaes")]
    fn vpaes_encrypt_key_to_bsaes(bsaes: *mut Schedule, vpaes: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_decrypt_key_to_bsaes")]
    fn vpaes_decrypt_key_to_bsaes(bsaes: *mut Schedule, vpaes: *const Schedule);

    #[link_name = aws_lc_symbol!("bsaes_ctr32_encrypt_blocks")]
    fn bsaes_ctr32_encrypt_blocks(
        input: *const u8,
        output: *mut u8,
        blocks: usize,
        key: *const Schedule,
        ivec: *const [u8; 16],
    );

    /// Decrypts only: `enc` must be 0.
    #[link_name = aws_lc_symbol!("bsaes_cbc_encrypt")]
    fn bsaes_cbc_encrypt(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const Schedule,
        ivec: *mut [u8; 16],
        enc: i32,
    );
}

// As in `aesv8_armx`: ARM mode with NEON, then the target's `.fpu` again.
core::arch::global_asm!(
    ".text",
    ".fpu neon",
    ".code 32",
    include_str!("aws_lc/vpaes-armv7.s"),
    include_str!("aws_lc/bsaes-armv7.s"),
    ".fpu vfpv3",
    vpaes_set_encrypt_key = sym vpaes_set_encrypt_key,
    vpaes_set_decrypt_key = sym vpaes_set_decrypt_key,
    vpaes_encrypt = sym vpaes_encrypt,
    vpaes_decrypt = sym vpaes_decrypt,
    vpaes_ctr32_encrypt_blocks = sym vpaes_ctr32_encrypt_blocks,
    vpaes_encrypt_key_to_bsaes = sym vpaes_encrypt_key_to_bsaes,
    vpaes_decrypt_key_to_bsaes = sym vpaes_decrypt_key_to_bsaes,
    bsaes_ctr32_encrypt_blocks = sym bsaes_ctr32_encrypt_blocks,
    bsaes_cbc_encrypt = sym bsaes_cbc_encrypt,
);

/// An expanded key in aws-lc's `AES_KEY`: round keys, then the round count,
/// which `vpaes` stores one short of the cipher's and `bsaes` in full.
#[repr(C, align(16))]
struct Schedule {
    rd_key: [u32; 60],
    rounds: u32,
}

impl Schedule {
    const ZERO: Self = Self {
        rd_key: [0; 60],
        rounds: 0,
    };

    /// The key's length in bytes, from the 9, 11, or 13 rounds `vpaes` stores.
    fn key_len(&self) -> usize {
        (self.rounds as usize + 1) * 4 - 24
    }
}

/// An AES-128, AES-192, or AES-256 encryption key.
#[repr(C)]
pub(crate) struct NeonKey {
    vpaes: Schedule,
    bsaes: Schedule,
}

impl NeonKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveNeon) -> Self {
        let mut r = Self {
            vpaes: Schedule::ZERO,
            bsaes: Schedule::ZERO,
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and the schedules are
        // `AES_KEY`s. The token proves the CPU has NEON.
        let ret = unsafe {
            asm_call!(unsafe extern "C" vpaes_set_encrypt_key(key.as_ptr(), key_bits(key), &mut r.vpaes))
        };
        // aws-lc refuses only a null pointer or another key size.
        assert_eq!(ret, 0);
        // SAFETY: as above, and `vpaes` is the schedule just made.
        unsafe {
            asm_call!(unsafe extern "C" vpaes_encrypt_key_to_bsaes(&mut r.bsaes, &r.vpaes))
        };
        r
    }

    /// The key's length in bytes, 16, 24, or 32, which no API reads but
    /// `Debug`.
    pub(crate) fn key_len(&self) -> usize {
        self.vpaes.key_len()
    }

    /// Encrypts one block.
    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        let mut out = [0u8; 16];
        // SAFETY: `block` is one readable block and `out` one writable one.
        // Only a `HaveNeon` token builds `self`.
        unsafe {
            asm_call!(unsafe extern "C" vpaes_encrypt(block.as_ptr(), out.as_mut_ptr(), &self.vpaes))
        };
        out
    }

    /// XORs counter-mode keystream into whole blocks.
    ///
    /// The counter blocks are `ivec`, then `ivec` with its last four bytes,
    /// a big-endian counter, incremented with 32-bit wrapping.
    ///
    /// As aws-lc's `vpaes_ctr32_encrypt_blocks_with_bsaes` does, `bsaes`
    /// takes the eight-block batches and a final batch of six or seven, which
    /// amortize its key schedule, and `vpaes` the rest.
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [[u8; 16]]) {
        let n = inout.len();
        let bsaes = if n < 8 {
            0
        } else if n % 8 < 6 {
            n - n % 8
        } else {
            n
        };
        let (head, tail) = inout.split_at_mut(bsaes);
        if !head.is_empty() {
            // SAFETY: `head` is `head.len()` readable and writable blocks,
            // which aws-lc allows to alias. Only a `HaveNeon` token builds
            // `self`.
            unsafe {
                asm_call!(unsafe extern "C" bsaes_ctr32_encrypt_blocks(
                    head.as_ptr().cast(),
                    head.as_mut_ptr().cast(),
                    head.len(),
                    &self.bsaes,
                    ivec,
                ))
            }
        }
        if !tail.is_empty() {
            let mut next = *ivec;
            let counter = u32::from_be_bytes([next[12], next[13], next[14], next[15]]);
            next[12..].copy_from_slice(&counter.wrapping_add(bsaes as u32).to_be_bytes());
            // SAFETY: as above.
            unsafe {
                asm_call!(unsafe extern "C" vpaes_ctr32_encrypt_blocks(
                    tail.as_ptr().cast(),
                    tail.as_mut_ptr().cast(),
                    tail.len(),
                    &self.vpaes,
                    &next,
                ))
            }
        }
    }

    /// Encrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_encrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let mut prev = *iv;
        for block in blocks {
            for (b, p) in block.iter_mut().zip(prev) {
                *b ^= p;
            }
            *block = self.encrypt_block(block);
            prev = *block;
        }
    }
}

impl Drop for NeonKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for NeonKey {}

/// An AES-128, AES-192, or AES-256 decryption key.
#[repr(C)]
pub(crate) struct NeonDecKey {
    vpaes: Schedule,
    bsaes: Schedule,
}

impl NeonDecKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveNeon) -> Self {
        let mut r = Self {
            vpaes: Schedule::ZERO,
            bsaes: Schedule::ZERO,
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and the schedules are
        // `AES_KEY`s. The token proves the CPU has NEON.
        let ret = unsafe {
            asm_call!(unsafe extern "C" vpaes_set_decrypt_key(key.as_ptr(), key_bits(key), &mut r.vpaes))
        };
        // aws-lc refuses only a null pointer or another key size.
        assert_eq!(ret, 0);
        // SAFETY: as above, and `vpaes` is the schedule just made.
        unsafe {
            asm_call!(unsafe extern "C" vpaes_decrypt_key_to_bsaes(&mut r.bsaes, &r.vpaes))
        };
        r
    }

    /// Decrypts one block in place.
    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        // SAFETY: `inout` is one readable and writable block, which aws-lc
        // allows to alias. Only a `HaveNeon` token builds `self`.
        unsafe {
            asm_call!(unsafe extern "C" vpaes_decrypt(inout.as_ptr(), inout.as_mut_ptr(), &self.vpaes))
        }
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        if blocks.is_empty() {
            return;
        }
        // The routine leaves the next IV here; CBC callers here start afresh.
        let mut ivec = *iv;
        // SAFETY: `blocks` is `16 * blocks.len()` readable and writable
        // bytes, which aws-lc allows to alias. Only a `HaveNeon` token builds
        // `self`.
        unsafe {
            asm_call!(unsafe extern "C" bsaes_cbc_encrypt(
                blocks.as_ptr().cast(),
                blocks.as_mut_ptr().cast(),
                16 * blocks.len(),
                &self.bsaes,
                &mut ivec,
                0,
            ))
        }
    }
}

impl Drop for NeonDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for NeonDecKey {}

/// `key`'s length in bits, which aws-lc's key schedules take.
fn key_bits(key: &[u8]) -> i32 {
    match key.len() {
        16 => 128,
        24 => 192,
        32 => 256,
        _ => unreachable!("callers check the AES key length"),
    }
}
