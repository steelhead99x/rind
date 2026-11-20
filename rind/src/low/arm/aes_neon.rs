// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES with NEON but without the crypto extension, using aws-lc's `vpaes-armv7`
//! and `bsaes-armv7` routines.
//!
//! `vpaes` (vector permutes, no table indexed by a secret) runs key schedules
//! and single blocks. `bsaes` (bitsliced) runs counter mode and CBC decryption,
//! eight blocks at a time. Both are constant time. A key holds its `vpaes`
//! schedule, which every mode can run, and the first call that `bsaes` takes
//! converts it to `bsaes`'s form and keeps that, so a key works for every
//! mode and its setup costs no more than `vpaes`'s. aws-lc converts on every
//! such call.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. It is not
//! formally verified: its correctness rests on its use and testing in OpenSSL,
//! BoringSSL, and aws-lc, and on rind's tests of it against the portable code,
//! Wycheproof, and aws-lc-rs.

use super::cpu::HaveNeon;
use crate::low;
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU8, Ordering};

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

impl low::generic::zeroise::Zeroable for Schedule {}

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

/// A key's `bsaes` schedule, converted from its `vpaes` one by the first call
/// that needs it.
///
/// Zero is a valid, unconverted value, so a drop that wipes the whole key
/// leaves nothing to undo.
#[repr(C)]
struct Bsaes {
    /// 0 until a call claims the conversion, 1 while it converts, 2 once
    /// `schedule` holds it, which nothing writes again.
    state: AtomicU8,
    schedule: UnsafeCell<Schedule>,
}

// SAFETY: a call writes `schedule` only after winning the compare-exchange
// from 0 to 1, which one call ever does, and reads it only after loading 2,
// which the winner stores with `Release` once it has written it.
unsafe impl Sync for Bsaes {}

// A panic cannot leave a half-converted schedule readable: a call reads one
// only after the state says it is whole, and the conversion cannot panic.
impl core::panic::RefUnwindSafe for Bsaes {}

impl Bsaes {
    fn new() -> Self {
        Self {
            state: AtomicU8::new(0),
            schedule: UnsafeCell::new(Schedule::ZERO),
        }
    }

    /// The `bsaes` schedule `convert` makes from `vpaes`: the key's own,
    /// converted by the first call, or else `scratch`, converted by this one
    /// while another call converts or after it failed to claim. The caller
    /// wipes `scratch`.
    fn get<'a>(
        &'a self,
        vpaes: &Schedule,
        scratch: &'a mut Schedule,
        convert: fn(&mut Schedule, &Schedule),
    ) -> &'a Schedule {
        if self.state.load(Ordering::Acquire) == 2 {
            // SAFETY: state 2 means the winner finished writing, and nothing
            // writes again.
            return unsafe { &*self.schedule.get() };
        }
        if self
            .state
            .compare_exchange(0, 1, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
        {
            // SAFETY: this call won the claim, so no other call touches
            // `schedule` until it stores 2.
            let schedule = unsafe { &mut *self.schedule.get() };
            convert(schedule, vpaes);
            self.state.store(2, Ordering::Release);
            return schedule;
        }
        convert(scratch, vpaes);
        scratch
    }
}

fn convert_encrypt(bsaes: &mut Schedule, vpaes: &Schedule) {
    // SAFETY: both are `AES_KEY`s, `vpaes` an encryption key's. Only a
    // `HaveNeon` token builds the keys that call this.
    unsafe { asm_call!(unsafe extern "C" vpaes_encrypt_key_to_bsaes(bsaes, vpaes)) }
}

fn convert_decrypt(bsaes: &mut Schedule, vpaes: &Schedule) {
    // SAFETY: both are `AES_KEY`s, `vpaes` a decryption key's. Only a
    // `HaveNeon` token builds the keys that call this.
    unsafe { asm_call!(unsafe extern "C" vpaes_decrypt_key_to_bsaes(bsaes, vpaes)) }
}

/// An AES-128, AES-192, or AES-256 encryption key.
#[repr(C)]
pub(crate) struct NeonKey {
    vpaes: Schedule,
    bsaes: Bsaes,
}

impl NeonKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveNeon) -> Self {
        let mut r = Self {
            vpaes: Schedule::ZERO,
            bsaes: Bsaes::new(),
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and the schedule is
        // an `AES_KEY`. The token proves the CPU has NEON.
        let ret = unsafe {
            asm_call!(unsafe extern "C" vpaes_set_encrypt_key(key.as_ptr(), key_bits(key), &mut r.vpaes))
        };
        // aws-lc refuses only a null pointer or another key size.
        assert_eq!(ret, 0);
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
        let bsaes = batched(inout.len());
        let (head, tail) = inout.split_at_mut(bsaes);
        if !head.is_empty() {
            let mut scratch = Schedule::ZERO;
            let key = self.bsaes.get(&self.vpaes, &mut scratch, convert_encrypt);
            // SAFETY: `head` is `head.len()` readable and writable blocks,
            // which aws-lc allows to alias, and `key` is `self`'s.
            unsafe {
                asm_call!(unsafe extern "C" bsaes_ctr32_encrypt_blocks(
                    head.as_ptr().cast(),
                    head.as_mut_ptr().cast(),
                    head.len(),
                    key,
                    ivec,
                ))
            }
            low::zeroise_value(&mut scratch);
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
        let mut prev = u128::from_ne_bytes(*iv);
        for block in blocks {
            *block = (u128::from_ne_bytes(*block) ^ prev).to_ne_bytes();
            // SAFETY: `block` is one readable and writable block, which
            // aws-lc allows to alias. Only a `HaveNeon` token builds `self`.
            unsafe {
                asm_call!(unsafe extern "C" vpaes_encrypt(block.as_ptr(), block.as_mut_ptr(), &self.vpaes))
            };
            prev = u128::from_ne_bytes(*block);
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
    bsaes: Bsaes,
}

impl NeonDecKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8], _: HaveNeon) -> Self {
        let mut r = Self {
            vpaes: Schedule::ZERO,
            bsaes: Bsaes::new(),
        };
        // SAFETY: `key` holds `key_bits(key) / 8` bytes and the schedule is
        // an `AES_KEY`. The token proves the CPU has NEON.
        let ret = unsafe {
            asm_call!(unsafe extern "C" vpaes_set_decrypt_key(key.as_ptr(), key_bits(key), &mut r.vpaes))
        };
        // aws-lc refuses only a null pointer or another key size.
        assert_eq!(ret, 0);
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
    ///
    /// `bsaes` takes the eight-block batches and a final batch of six or
    /// seven, which amortize its key conversion, and `vpaes` the rest, as
    /// for counter mode.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let n = blocks.len();
        let bsaes = batched(n);
        let (head, tail) = blocks.split_at_mut(bsaes);
        // The routine leaves the next IV here; CBC callers here start afresh.
        let mut ivec = *iv;
        if !head.is_empty() {
            let mut scratch = Schedule::ZERO;
            let key = self.bsaes.get(&self.vpaes, &mut scratch, convert_decrypt);
            // SAFETY: `head` is `16 * head.len()` readable and writable bytes,
            // which aws-lc allows to alias, and `key` is `self`'s.
            unsafe {
                asm_call!(unsafe extern "C" bsaes_cbc_encrypt(
                    head.as_ptr().cast(),
                    head.as_mut_ptr().cast(),
                    16 * head.len(),
                    key,
                    &mut ivec,
                    0,
                ))
            }
            low::zeroise_value(&mut scratch);
        }
        // Backwards, so each block's predecessor is still ciphertext.
        for i in (0..tail.len()).rev() {
            let prev = if i == 0 { ivec } else { tail[i - 1] };
            self.decrypt_block(&mut tail[i]);
            tail[i] = (u128::from_ne_bytes(tail[i]) ^ u128::from_ne_bytes(prev)).to_ne_bytes();
        }
    }
}

/// How many of `n` blocks `bsaes` takes: none under eight, then the
/// eight-block batches, and a last batch of six or seven too, as aws-lc's
/// `vpaes_ctr32_encrypt_blocks_with_bsaes` does.
fn batched(n: usize) -> usize {
    if n < 8 {
        0
    } else if n % 8 < 6 {
        n - n % 8
    } else {
        n
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

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn bytes(n: usize, seed: u32) -> Vec<u8> {
        (0..n as u32)
            .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect()
    }

    /// Counter mode over `blocks`, in runs of seven, which `vpaes` alone takes.
    fn ctr_vpaes_only(key: &NeonKey, ivec: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let mut ivec = *ivec;
        for run in blocks.chunks_mut(7) {
            key.ctr32(&ivec, run);
            let counter = u32::from_be_bytes(ivec[12..].try_into().unwrap());
            ivec[12..].copy_from_slice(&counter.wrapping_add(7).to_be_bytes());
        }
    }

    // A conversion `bsaes` took from the key's own cache, from the first call
    // that makes it, and from a call's scratch while another converts, gives
    // one result, which `vpaes` alone gives too.
    #[test]
    fn every_conversion_matches_vpaes() {
        let Some(token) = HaveNeon::check() else {
            return;
        };
        for key_len in [16, 24, 32] {
            let raw = bytes(key_len, 1);
            let ivec: [u8; 16] = bytes(16, 2).try_into().unwrap();
            let plain = bytes(16 * 21, 3);
            let (plain, _) = plain.as_chunks::<16>();

            let mut want = plain.to_vec();
            ctr_vpaes_only(&NeonKey::new(&raw, token), &ivec, &mut want);
            let enc = NeonDecKey::new(&raw, token);
            let mut cbc_want = plain.to_vec();
            for i in (0..cbc_want.len()).rev() {
                let prev = if i == 0 { ivec } else { cbc_want[i - 1] };
                enc.decrypt_block(&mut cbc_want[i]);
                for (b, p) in cbc_want[i].iter_mut().zip(prev) {
                    *b ^= p;
                }
            }

            for state in [0, 1] {
                let key = NeonKey::new(&raw, token);
                key.bsaes.state.store(state, Ordering::Relaxed);
                let dec = NeonDecKey::new(&raw, token);
                dec.bsaes.state.store(state, Ordering::Relaxed);
                // The first call, and then the cache it left, if it left one.
                for call in 0..2 {
                    let mut got = plain.to_vec();
                    key.ctr32(&ivec, &mut got);
                    assert_eq!(
                        got, want,
                        "{key_len}-byte key, ctr, state {state}, call {call}"
                    );
                    let mut got = plain.to_vec();
                    dec.cbc_decrypt(&ivec, &mut got);
                    assert_eq!(
                        got, cbc_want,
                        "{key_len}-byte key, cbc, state {state}, call {call}"
                    );
                }
                let converted = if state == 0 { 2 } else { 1 };
                assert_eq!(key.bsaes.state.load(Ordering::Relaxed), converted);
            }
        }
    }

    // Threads that share a key, each its first use, all get the right result.
    #[test]
    fn threads_sharing_a_key_agree() {
        let Some(token) = HaveNeon::check() else {
            return;
        };
        let raw = bytes(16, 4);
        let ivec: [u8; 16] = bytes(16, 5).try_into().unwrap();
        let plain = bytes(16 * 16, 6);
        let (plain, _) = plain.as_chunks::<16>();
        let mut want = plain.to_vec();
        ctr_vpaes_only(&NeonKey::new(&raw, token), &ivec, &mut want);
        for _ in 0..50 {
            let key = NeonKey::new(&raw, token);
            std::thread::scope(|s| {
                for _ in 0..4 {
                    s.spawn(|| {
                        let mut got = plain.to_vec();
                        key.ctr32(&ivec, &mut got);
                        assert_eq!(got, want);
                    });
                }
            });
        }
    }
}
