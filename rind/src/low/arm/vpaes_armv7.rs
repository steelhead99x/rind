// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES on NEON alone, for CPUs without the crypto extension, as aws-lc runs
//! it there: its `vpaes-armv7` routines for key setup, single blocks, and
//! short runs, and its `bsaes-armv7` routines for CTR and CBC decryption
//! from eight blocks on.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. vpaes is Mike
//! Hamburg's vector permutation AES, whose S-box is `vtbl` lookups into
//! registers, and bsaes bitsliced AES, which computes on eight blocks at
//! once with logic alone, so neither indexes memory by the key or data. Each
//! key holds its vpaes schedule and that schedule converted to the plain one
//! bsaes reads, converted once at setup rather than per call, as aws-lc's
//! CTR does. It is not formally verified: its correctness rests on its use
//! and testing in OpenSSL, BoringSSL, and aws-lc, and on rind's tests of it
//! against the portable code, Wycheproof, and aws-lc-rs.

use super::cpu::HaveNeon;
use crate::low;

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("vpaes_set_encrypt_key")]
    fn vpaes_set_encrypt_key(user_key: *const u8, bits: u32, key: *mut Schedule) -> i32;

    #[link_name = aws_lc_symbol!("vpaes_set_decrypt_key")]
    fn vpaes_set_decrypt_key(user_key: *const u8, bits: u32, key: *mut Schedule) -> i32;

    #[link_name = aws_lc_symbol!("vpaes_encrypt")]
    fn vpaes_encrypt(input: *const u8, output: *mut u8, key: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_decrypt")]
    fn vpaes_decrypt(input: *const u8, output: *mut u8, key: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_encrypt_key_to_bsaes")]
    fn vpaes_encrypt_key_to_bsaes(bsaes: *mut Schedule, vpaes: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_decrypt_key_to_bsaes")]
    fn vpaes_decrypt_key_to_bsaes(bsaes: *mut Schedule, vpaes: *const Schedule);

    #[link_name = aws_lc_symbol!("vpaes_ctr32_encrypt_blocks")]
    fn vpaes_ctr32_encrypt_blocks(
        input: *const u8,
        output: *mut u8,
        blocks: usize,
        key: *const Schedule,
        ivec: *const [u8; 16],
    );

    /// Decrypts only: aws-lc's takes `enc` as 0 alone.
    #[link_name = aws_lc_symbol!("bsaes_cbc_encrypt")]
    fn bsaes_cbc_encrypt(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const Schedule,
        ivec: *mut [u8; 16],
        enc: i32,
    );

    #[link_name = aws_lc_symbol!("bsaes_ctr32_encrypt_blocks")]
    fn bsaes_ctr32_encrypt_blocks(
        input: *const u8,
        output: *mut u8,
        blocks: usize,
        key: *const Schedule,
        ivec: *const [u8; 16],
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
    vpaes_encrypt_key_to_bsaes = sym vpaes_encrypt_key_to_bsaes,
    vpaes_decrypt_key_to_bsaes = sym vpaes_decrypt_key_to_bsaes,
    vpaes_ctr32_encrypt_blocks = sym vpaes_ctr32_encrypt_blocks,
    bsaes_cbc_encrypt = sym bsaes_cbc_encrypt,
    bsaes_ctr32_encrypt_blocks = sym bsaes_ctr32_encrypt_blocks,
);

/// An expanded key in one of the routines' formats: aws-lc's `AES_KEY`.
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
}

/// An AES-128, AES-192, or AES-256 encryption key for NEON, which only a
/// `HaveNeon` token builds.
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
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and each schedule is
        // an `AES_KEY`. The token proves the CPU has NEON.
        let ret = unsafe {
            asm_call!(unsafe extern "C" vpaes_set_encrypt_key(key.as_ptr(), key_bits(key), &mut r.vpaes))
        };
        // aws-lc's always succeeds.
        assert_eq!(ret, 0);
        // SAFETY: as above.
        unsafe { asm_call!(unsafe extern "C" vpaes_encrypt_key_to_bsaes(&mut r.bsaes, &r.vpaes)) };
        r
    }

    /// The key's length in bytes, from the `nbits / 32 + 5` rounds that
    /// `vpaes_set_encrypt_key` stores.
    pub(crate) fn key_len(&self) -> usize {
        (self.vpaes.rounds as usize - 5) * 4
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
    /// a big-endian counter, incremented with 32-bit wrapping. bsaes takes
    /// the runs [`bsaes_blocks`] picks, as aws-lc's
    /// `vpaes_ctr32_encrypt_blocks_with_bsaes` does, and vpaes the rest.
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [[u8; 16]]) {
        let (bulk, rest) = inout.split_at_mut(bsaes_blocks(inout.len()));
        if !bulk.is_empty() {
            // One pointer for input and output, so neither reborrow
            // invalidates the other.
            let io = bulk.as_mut_ptr().cast::<u8>();
            // SAFETY: `io` is `bulk.len()` readable and writable blocks,
            // which aws-lc allows to alias, at least eight. Only a `HaveNeon`
            // token builds `self`.
            unsafe {
                asm_call!(unsafe extern "C" bsaes_ctr32_encrypt_blocks(
                    io,
                    io,
                    bulk.len(),
                    &self.bsaes,
                    ivec,
                ))
            }
        }
        if rest.is_empty() {
            return;
        }
        let ivec = add32(ivec, bulk.len());
        let io = rest.as_mut_ptr().cast::<u8>();
        // SAFETY: as above, for `rest`.
        unsafe {
            asm_call!(unsafe extern "C" vpaes_ctr32_encrypt_blocks(
                io,
                io,
                rest.len(),
                &self.vpaes,
                &ivec,
            ))
        }
    }

    /// Encrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`, one block at a time, since each depends on the last.
    pub(crate) fn cbc_encrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let mut chain = *iv;
        for block in blocks {
            for (b, c) in block.iter_mut().zip(chain) {
                *b ^= c;
            }
            chain = self.encrypt_block(block);
            *block = chain;
        }
    }
}

impl Drop for NeonKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for NeonKey {}

/// An AES-128, AES-192, or AES-256 decryption key for NEON, which only a
/// `HaveNeon` token builds.
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
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and each schedule is
        // an `AES_KEY`. The token proves the CPU has NEON.
        let ret = unsafe {
            asm_call!(unsafe extern "C" vpaes_set_decrypt_key(key.as_ptr(), key_bits(key), &mut r.vpaes))
        };
        // aws-lc's always succeeds.
        assert_eq!(ret, 0);
        // SAFETY: as above.
        unsafe { asm_call!(unsafe extern "C" vpaes_decrypt_key_to_bsaes(&mut r.bsaes, &r.vpaes)) };
        r
    }

    /// Decrypts one block in place.
    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        let io = inout.as_mut_ptr();
        // SAFETY: `io` is one readable and writable block, which aws-lc
        // allows to alias. Only a `HaveNeon` token builds `self`.
        unsafe { asm_call!(unsafe extern "C" vpaes_decrypt(io, io, &self.vpaes)) }
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`: bsaes the runs [`bsaes_blocks`] picks, and vpaes the rest.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let (bulk, rest) = blocks.split_at_mut(bsaes_blocks(blocks.len()));
        // The routine leaves the next IV here: the last ciphertext block.
        let mut chain = *iv;
        if !bulk.is_empty() {
            let io = bulk.as_mut_ptr().cast::<u8>();
            // SAFETY: `io` is `16 * bulk.len()` readable and writable
            // bytes, which aws-lc allows to alias, and `enc` 0, as the
            // routine requires. Only a `HaveNeon` token builds `self`.
            unsafe {
                asm_call!(unsafe extern "C" bsaes_cbc_encrypt(
                    io,
                    io,
                    16 * bulk.len(),
                    &self.bsaes,
                    &mut chain,
                    0,
                ))
            }
        }
        for block in rest {
            let next = *block;
            self.decrypt_block(block);
            for (b, c) in block.iter_mut().zip(chain) {
                *b ^= c;
            }
            chain = next;
        }
    }
}

impl Drop for NeonDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for NeonDecKey {}

/// How many of `blocks` blocks bsaes takes, as aws-lc's
/// `vpaes_ctr32_encrypt_blocks_with_bsaes` decides: none below one eight-block
/// batch, which the per-call conversion of its schedule needs to pay off,
/// then whole batches, and a final partial batch too from six blocks on,
/// below which vpaes is faster one block at a time.
fn bsaes_blocks(blocks: usize) -> usize {
    match (blocks, blocks % 8) {
        (..8, _) => 0,
        (_, ..6) => blocks - blocks % 8,
        _ => blocks,
    }
}

/// `ivec` with `n` added to its big-endian counter in its last four bytes,
/// modulo 2^32.
fn add32(ivec: &[u8; 16], n: usize) -> [u8; 16] {
    let mut r = *ivec;
    let ctr = u32::from_be_bytes(ivec[12..].try_into().unwrap()).wrapping_add(n as u32);
    r[12..].copy_from_slice(&ctr.to_be_bytes());
    r
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

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn bsaes_takes_aws_lcs_runs() {
        let picks: Vec<usize> = (0..=24).map(bsaes_blocks).collect();
        #[rustfmt::skip]
        assert_eq!(picks, [
            0, 0, 0, 0, 0, 0, 0, 0,
            8, 8, 8, 8, 8, 8, 14, 15,
            16, 16, 16, 16, 16, 16, 22, 23,
            24,
        ]);
    }
}
