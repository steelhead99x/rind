// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// References:
// - https://iacr.org/archive/fse2009/56650054/56650054.pdf (or)
// - https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf

use core::arch::x86_64::*;

use super::aes_nohw::NohwKey;
use super::cpu::{HaveAesHardware, HaveSsse3};
use super::ghash::u128_to_m128i;
use super::vpaes_x86_64::{VpaesDecKey, VpaesKey};
use crate::low;

// Keep all-zero valid when drop wipes the whole enum.
#[repr(u8)]
pub(crate) enum AesKey {
    /// AES-NI's, which the key picks when the CPU has AES-NI and PCLMULQDQ.
    Hw(HwKey),
    /// SSSE3's, without AES-NI.
    Vpaes(VpaesKey),
    /// SSE2's, which the key picks when the CPU also lacks SSSE3.
    Nohw(NohwKey),
}

impl AesKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        match (key.len(), HaveAesHardware::check(), HaveSsse3::check()) {
            (16, Some(token), _) => Self::Hw(HwKey::Aes128(AesKey128::new(
                key.try_into().unwrap(),
                token,
            ))),
            (24, Some(token), _) => Self::Hw(HwKey::Aes192(AesKey192::new(
                key.try_into().unwrap(),
                token,
            ))),
            (32, Some(token), _) => Self::Hw(HwKey::Aes256(AesKey256::new(
                key.try_into().unwrap(),
                token,
            ))),
            (16 | 24 | 32, None, Some(token)) => Self::Vpaes(VpaesKey::new(key, token)),
            (16 | 24 | 32, None, None) => Self::Nohw(NohwKey::new(key)),
            _ => unreachable!("callers check the AES key length"),
        }
    }

    /// Encrypts one block.
    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        match self {
            Self::Hw(key) => key.encrypt_block(block),
            Self::Vpaes(key) => key.encrypt_block(block),
            Self::Nohw(key) => key.encrypt_block(block),
        }
    }

    /// The key's length in bytes, 16, 24, or 32, which no API reads but
    /// `Debug`.
    pub(crate) fn key_len(&self) -> usize {
        match self {
            Self::Hw(HwKey::Aes128(_)) => 16,
            Self::Hw(HwKey::Aes192(_)) => 24,
            Self::Hw(HwKey::Aes256(_)) => 32,
            Self::Vpaes(key) => key.key_len(),
            Self::Nohw(key) => key.key_len(),
        }
    }
}

impl Drop for AesKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for AesKey {}

/// An AES key that decrypts, on the path [`AesKey`] picks for the CPU.
#[repr(u8)]
pub(crate) enum AesDecKey {
    Hw(HwDecKey),
    Vpaes(VpaesDecKey),
    Nohw(NohwKey),
}

impl AesDecKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        match (key.len(), HaveAesHardware::check(), HaveSsse3::check()) {
            (16, Some(token), _) => Self::Hw(HwDecKey::Aes128(
                AesKey128::new(key.try_into().unwrap(), token).inverse(),
            )),
            (24, Some(token), _) => Self::Hw(HwDecKey::Aes192(
                AesKey192::new(key.try_into().unwrap(), token).inverse(),
            )),
            (32, Some(token), _) => Self::Hw(HwDecKey::Aes256(
                AesKey256::new(key.try_into().unwrap(), token).inverse(),
            )),
            (16 | 24 | 32, None, Some(token)) => Self::Vpaes(VpaesDecKey::new(key, token)),
            (16 | 24 | 32, None, None) => Self::Nohw(NohwKey::new(key)),
            _ => unreachable!("callers check the AES key length"),
        }
    }

    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        match self {
            // SAFETY: only a `HaveAesHardware` token builds the round keys.
            Self::Hw(HwDecKey::Aes128(key)) => unsafe { hw_decrypt_block(&key.round_keys, inout) },
            // SAFETY: as above.
            Self::Hw(HwDecKey::Aes192(key)) => unsafe { hw_decrypt_block(&key.round_keys, inout) },
            // SAFETY: as above.
            Self::Hw(HwDecKey::Aes256(key)) => unsafe { hw_decrypt_block(&key.round_keys, inout) },
            Self::Vpaes(key) => key.decrypt_block(inout),
            Self::Nohw(key) => key.decrypt_block(inout),
        }
    }
}

impl Drop for AesDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for AesDecKey {}

/// AES-NI round keys for the equivalent inverse cipher, FIPS 197 section
/// 5.3.5, which only a `HaveAesHardware` token builds: the encryption round
/// keys reversed, all but the outer two through InvMixColumns, laid out as
/// aws-lc's `aes_hw_set_decrypt_key` writes them.
pub(crate) enum HwDecKey {
    Aes128(AesKey128),
    Aes192(AesKey192),
    Aes256(AesKey256),
}

impl HwDecKey {
    /// This key as BoringSSL's `AES_KEY`, for its CBC decryption.
    pub(crate) fn as_aes_key(&self) -> *const u8 {
        match self {
            Self::Aes128(a128) => (a128 as *const AesKey128).cast(),
            Self::Aes192(a192) => (a192 as *const AesKey192).cast(),
            Self::Aes256(a256) => (a256 as *const AesKey256).cast(),
        }
    }
}

/// A key for AES-NI.
pub(crate) enum HwKey {
    Aes128(AesKey128),
    Aes192(AesKey192),
    Aes256(AesKey256),
}

impl HwKey {
    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        match self {
            Self::Aes128(a128) => a128.encrypt_block(block),
            Self::Aes192(a192) => a192.encrypt_block(block),
            Self::Aes256(a256) => a256.encrypt_block(block),
        }
    }

    pub(crate) fn round_keys(&self) -> (__m128i, &[__m128i], __m128i) {
        match self {
            Self::Aes128(a128) => (
                a128.round_keys[0],
                &a128.round_keys[1..10],
                a128.round_keys[10],
            ),
            Self::Aes192(a192) => (
                a192.round_keys[0],
                &a192.round_keys[1..12],
                a192.round_keys[12],
            ),
            Self::Aes256(a256) => (
                a256.round_keys[0],
                &a256.round_keys[1..14],
                a256.round_keys[14],
            ),
        }
    }

    /// This key as BoringSSL's `AES_KEY`, for its AES-GCM kernels.
    pub(crate) fn as_aes_key(&self) -> *const u8 {
        match self {
            Self::Aes128(a128) => (a128 as *const AesKey128).cast(),
            Self::Aes192(a192) => (a192 as *const AesKey192).cast(),
            Self::Aes256(a256) => (a256 as *const AesKey256).cast(),
        }
    }

    #[target_feature(enable = "avx512f")]
    pub(crate) fn round_keys_512(&self) -> RoundKeys512 {
        match self {
            Self::Aes128(AesKey128 {
                round_keys: [a, b, c, d, e, f, g, h, i, j, k],
                ..
            }) => RoundKeys512::Aes128([
                _mm512_broadcast_i32x4(*a),
                _mm512_broadcast_i32x4(*b),
                _mm512_broadcast_i32x4(*c),
                _mm512_broadcast_i32x4(*d),
                _mm512_broadcast_i32x4(*e),
                _mm512_broadcast_i32x4(*f),
                _mm512_broadcast_i32x4(*g),
                _mm512_broadcast_i32x4(*h),
                _mm512_broadcast_i32x4(*i),
                _mm512_broadcast_i32x4(*j),
                _mm512_broadcast_i32x4(*k),
            ]),
            Self::Aes192(a192) => {
                let mut rks = [_mm512_setzero_si512(); 13];
                for (out, rk) in rks.iter_mut().zip(&a192.round_keys) {
                    *out = _mm512_broadcast_i32x4(*rk);
                }
                RoundKeys512::Aes192(rks)
            }
            Self::Aes256(AesKey256 {
                round_keys: [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o],
                ..
            }) => RoundKeys512::Aes256([
                _mm512_broadcast_i32x4(*a),
                _mm512_broadcast_i32x4(*b),
                _mm512_broadcast_i32x4(*c),
                _mm512_broadcast_i32x4(*d),
                _mm512_broadcast_i32x4(*e),
                _mm512_broadcast_i32x4(*f),
                _mm512_broadcast_i32x4(*g),
                _mm512_broadcast_i32x4(*h),
                _mm512_broadcast_i32x4(*i),
                _mm512_broadcast_i32x4(*j),
                _mm512_broadcast_i32x4(*k),
                _mm512_broadcast_i32x4(*l),
                _mm512_broadcast_i32x4(*m),
                _mm512_broadcast_i32x4(*n),
                _mm512_broadcast_i32x4(*o),
            ]),
        }
    }
}

pub(crate) enum RoundKeys512 {
    Aes128([__m512i; 11]),
    Aes192([__m512i; 13]),
    Aes256([__m512i; 15]),
}

impl RoundKeys512 {
    pub(crate) fn split(&self) -> (__m512i, &[__m512i], __m512i) {
        match self {
            Self::Aes128(rks) => (rks[0], &rks[1..10], rks[10]),
            Self::Aes192(rks) => (rks[0], &rks[1..12], rks[12]),
            Self::Aes256(rks) => (rks[0], &rks[1..14], rks[14]),
        }
    }
}

/// An AES-128 key for AES-NI, which only a `HaveAesHardware` token builds.
///
/// Laid out as BoringSSL's `AES_KEY`: round key `i` at byte `16 * i`, and at
/// byte 240 the number of rounds less one, as AES-NI code counts them.
#[repr(C)]
pub(crate) struct AesKey128 {
    round_keys: [__m128i; 10 + 1],
    unused: [__m128i; 4],
    rounds: u32,
}

impl AesKey128 {
    pub(crate) fn new(key: &[u8; 16], _: HaveAesHardware) -> Self {
        let mut round_keys = [zero(); (10 + 1)];

        // SAFETY: the token proves the CPU has AES-NI and SSSE3.
        unsafe {
            aes128_expand(key, &mut round_keys);
        }

        Self {
            round_keys,
            unused: [zero(); 4],
            rounds: 9,
        }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        // SAFETY: only a `HaveAesHardware` token builds `self`.
        unsafe { aes128_block(&self.round_keys, block) }
    }

    /// The inverse cipher's key, as [`HwDecKey`] holds it.
    fn inverse(&self) -> Self {
        Self {
            // SAFETY: only a `HaveAesHardware` token builds `self`.
            round_keys: unsafe { invert_round_keys(&self.round_keys) },
            unused: [zero(); 4],
            rounds: self.rounds,
        }
    }
}

/// An AES-192 key for AES-NI, which only a `HaveAesHardware` token builds.
///
/// Laid out as BoringSSL's `AES_KEY`, as [`AesKey128`] is.
#[repr(C)]
pub(crate) struct AesKey192 {
    round_keys: [__m128i; 12 + 1],
    unused: [__m128i; 2],
    rounds: u32,
}

impl AesKey192 {
    pub(crate) fn new(key: &[u8; 24], _: HaveAesHardware) -> Self {
        // SAFETY: the token proves the CPU has AES-NI.
        let round_keys = unsafe { aes192_expand(key) };
        Self {
            round_keys,
            unused: [zero(); 2],
            rounds: 11,
        }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        // SAFETY: only a `HaveAesHardware` token builds `self`.
        unsafe { aes_block(&self.round_keys, block) }
    }

    /// The inverse cipher's key, as [`HwDecKey`] holds it.
    fn inverse(&self) -> Self {
        Self {
            // SAFETY: only a `HaveAesHardware` token builds `self`.
            round_keys: unsafe { invert_round_keys(&self.round_keys) },
            unused: [zero(); 2],
            rounds: self.rounds,
        }
    }
}

fn zero() -> __m128i {
    // SAFETY: every x86_64 CPU has SSE2
    unsafe { _mm_setzero_si128() }
}

/// An AES-256 key for AES-NI, which only a `HaveAesHardware` token builds.
///
/// Laid out as BoringSSL's `AES_KEY`, as [`AesKey128`] is.
#[repr(C)]
pub(crate) struct AesKey256 {
    round_keys: [__m128i; 14 + 1],
    rounds: u32,
}

const _: () = assert!(core::mem::offset_of!(AesKey128, rounds) == 240);
const _: () = assert!(core::mem::offset_of!(AesKey192, rounds) == 240);
const _: () = assert!(core::mem::offset_of!(AesKey256, rounds) == 240);

impl AesKey256 {
    pub(crate) fn new(key: &[u8; 32], _: HaveAesHardware) -> Self {
        let mut round_keys = [zero(); 14 + 1];

        // SAFETY: the token proves the CPU has AES-NI and SSSE3.
        unsafe {
            aes256_expand(key, &mut round_keys);
        }

        Self {
            round_keys,
            rounds: 13,
        }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        // SAFETY: only a `HaveAesHardware` token builds `self`.
        unsafe { aes256_block(&self.round_keys, block) }
    }

    /// The inverse cipher's key, as [`HwDecKey`] holds it.
    fn inverse(&self) -> Self {
        Self {
            // SAFETY: only a `HaveAesHardware` token builds `self`.
            round_keys: unsafe { invert_round_keys(&self.round_keys) },
            rounds: self.rounds,
        }
    }
}

const RCON: [i32; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

// The expansions fill a local array, indexing their loops, and write `out`
// once: Aeneas translates neither a loop that writes through a reference nor
// one over an iterator of the round constants.
#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "aes,ssse3")]
fn aes128_expand(key: &[u8; 16], out: &mut [__m128i; 11]) {
    let mut t = load(key);
    let mut rk = [t; 11];
    for i in 0..10 {
        t = _mm_xor_si128(xor_prefix(t), sub_rot_word(t, RCON[i]));
        rk[i + 1] = t;
    }
    *out = rk;
}

#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "aes,ssse3")]
fn aes256_expand(key: &[u8; 32], out: &mut [__m128i; 15]) {
    let mut a = load(key[..16].try_into().unwrap());
    let mut b = load(key[16..].try_into().unwrap());
    let mut rk = [a; 15];
    rk[1] = b;

    // Round keys alternate: the first of each pair takes RotWord and the
    // round constant, as AES-128's do, and the second only SubWord.
    for i in 0..7 {
        a = _mm_xor_si128(xor_prefix(a), sub_rot_word(b, RCON[i]));
        rk[2 * i + 2] = a;
        if i == 6 {
            break;
        }
        let sub = _mm_aesenclast_si128(_mm_shuffle_epi32(a, 0b11_11_11_11), zero());
        b = _mm_xor_si128(xor_prefix(b), sub);
        rk[2 * i + 3] = b;
    }
    *out = rk;
}

/// AES-192's schedule six words at a time: `a` holds each step's first four
/// words and `b` its last two, in its low half, so every other round key
/// straddles the two. Each step's first word takes RotWord, SubWord, and the
/// round constant of the step before's last, as `sub_rot_word` computes
/// them from a vector's last word.
#[target_feature(enable = "aes,ssse3")]
fn aes192_expand(key: &[u8; 24]) -> [__m128i; 13] {
    let mut a = load(key[..16].try_into().unwrap());
    let mut b = u128_to_m128i(u128::from(u64::from_le_bytes(
        key[16..].try_into().unwrap(),
    )));
    let rot_word_1 = _mm_setr_epi8(5, 6, 7, 4, 5, 6, 7, 4, 5, 6, 7, 4, 5, 6, 7, 4);
    let mut out = [a; 13];
    for step in 1..9 {
        let sub = _mm_aesenclast_si128(
            _mm_shuffle_epi8(b, rot_word_1),
            _mm_set1_epi32(RCON[step - 1]),
        );
        a = _mm_xor_si128(xor_prefix(a), sub);
        if step % 2 == 1 {
            out[3 * (step - 1) / 2 + 1] = _mm_unpacklo_epi64(b, a);
        } else {
            out[3 * step / 2] = a;
        }
        if step == 8 {
            break;
        }
        let w3 = _mm_shuffle_epi32(a, 0b11_11_11_11);
        b = _mm_xor_si128(_mm_xor_si128(b, _mm_slli_si128(b, 4)), w3);
        if step % 2 == 1 {
            out[3 * (step - 1) / 2 + 2] = _mm_alignr_epi8(b, a, 8);
        }
    }
    out
}

/// SubWord(RotWord(w3)) XOR `rcon` in every word, where w3 is `t`'s last.
///
/// `aesenclast` on four equal columns is SubBytes alone, since ShiftRows
/// moves nothing, and then XORs its round key. `aeskeygenassist` computes
/// this too, but is slow on Intel cores: this form expands an AES-256 key in
/// under half the time on Skylake, and aws-lc prefers it on CPUs with AVX.
#[inline]
#[target_feature(enable = "aes,ssse3")]
fn sub_rot_word(t: __m128i, rcon: i32) -> __m128i {
    let rot_word_3 = _mm_setr_epi8(
        13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12,
    );
    _mm_aesenclast_si128(_mm_shuffle_epi8(t, rot_word_3), _mm_set1_epi32(rcon))
}

/// Each word of `t` XORed with the words before it: the round key's words
/// before the SubWord term is added.
#[inline]
#[target_feature(enable = "sse2")]
fn xor_prefix(t: __m128i) -> __m128i {
    let t = _mm_xor_si128(t, _mm_slli_si128(t, 4));
    _mm_xor_si128(t, _mm_slli_si128(t, 8))
}

/// `block` as a vector, its first byte lowest, as `_mm_loadu_si128` loads it.
/// A value rather than a pointer, which Aeneas cannot translate.
#[inline]
fn load(block: &[u8; 16]) -> __m128i {
    u128_to_m128i(u128::from_le_bytes(*block))
}

/// `v`'s bytes, the lowest first, as `_mm_storeu_si128` stores them.
#[inline]
fn store(v: __m128i) -> [u8; 16] {
    // SAFETY: every x86_64 CPU has SSE2
    let (lo, hi) = unsafe {
        (
            _mm_cvtsi128_si64(v) as u64,
            _mm_cvtsi128_si64(_mm_unpackhi_epi64(v, v)) as u64,
        )
    };
    (u128::from(hi) << 64 | u128::from(lo)).to_le_bytes()
}

#[target_feature(enable = "aes")]
fn aes128_block(round_keys: &[__m128i; 11], block: &[u8; 16]) -> [u8; 16] {
    let block = load(block);
    let block = _mm_xor_si128(block, round_keys[0]);
    let block = _mm_aesenc_si128(block, round_keys[1]);
    let block = _mm_aesenc_si128(block, round_keys[2]);
    let block = _mm_aesenc_si128(block, round_keys[3]);
    let block = _mm_aesenc_si128(block, round_keys[4]);
    let block = _mm_aesenc_si128(block, round_keys[5]);
    let block = _mm_aesenc_si128(block, round_keys[6]);
    let block = _mm_aesenc_si128(block, round_keys[7]);
    let block = _mm_aesenc_si128(block, round_keys[8]);
    let block = _mm_aesenc_si128(block, round_keys[9]);
    let block = _mm_aesenclast_si128(block, round_keys[10]);
    store(block)
}

/// One block under any key size, by its number of round keys.
#[target_feature(enable = "aes")]
fn aes_block<const N: usize>(round_keys: &[__m128i; N], block: &[u8; 16]) -> [u8; 16] {
    let mut block = load(block);
    block = _mm_xor_si128(block, round_keys[0]);
    for round_key in &round_keys[1..N - 1] {
        block = _mm_aesenc_si128(block, *round_key);
    }
    block = _mm_aesenclast_si128(block, round_keys[N - 1]);
    store(block)
}

#[target_feature(enable = "aes")]
fn aes256_block(round_keys: &[__m128i; 15], block: &[u8; 16]) -> [u8; 16] {
    let block = load(block);
    let block = _mm_xor_si128(block, round_keys[0]);
    let block = _mm_aesenc_si128(block, round_keys[1]);
    let block = _mm_aesenc_si128(block, round_keys[2]);
    let block = _mm_aesenc_si128(block, round_keys[3]);
    let block = _mm_aesenc_si128(block, round_keys[4]);
    let block = _mm_aesenc_si128(block, round_keys[5]);
    let block = _mm_aesenc_si128(block, round_keys[6]);
    let block = _mm_aesenc_si128(block, round_keys[7]);
    let block = _mm_aesenc_si128(block, round_keys[8]);
    let block = _mm_aesenc_si128(block, round_keys[9]);
    let block = _mm_aesenc_si128(block, round_keys[10]);
    let block = _mm_aesenc_si128(block, round_keys[11]);
    let block = _mm_aesenc_si128(block, round_keys[12]);
    let block = _mm_aesenc_si128(block, round_keys[13]);
    let block = _mm_aesenclast_si128(block, round_keys[14]);
    store(block)
}

/// The round keys for `aesdec` from those for `aesenc`.
#[target_feature(enable = "aes")]
fn invert_round_keys<const N: usize>(round_keys: &[__m128i; N]) -> [__m128i; N] {
    let mut out = [zero(); N];
    out[0] = round_keys[N - 1];
    for i in 1..N - 1 {
        out[i] = _mm_aesimc_si128(round_keys[N - 1 - i]);
    }
    out[N - 1] = round_keys[0];
    out
}

#[target_feature(enable = "aes")]
fn hw_decrypt_block<const N: usize>(round_keys: &[__m128i; N], block_inout: &mut [u8; 16]) {
    let mut block = load(block_inout);
    block = _mm_xor_si128(block, round_keys[0]);
    for round_key in &round_keys[1..N - 1] {
        block = _mm_aesdec_si128(block, *round_key);
    }
    block = _mm_aesdeclast_si128(block, round_keys[N - 1]);
    *block_inout = store(block);
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn key_len() {
        for key in [&[0u8; 16][..], &[0u8; 24], &[0u8; 32]] {
            assert_eq!(AesKey::new(key).key_len(), key.len());
            if let Some(token) = HaveSsse3::check() {
                let vpaes = AesKey::Vpaes(VpaesKey::new(key, token));
                assert_eq!(vpaes.key_len(), key.len());
            }
            assert_eq!(AesKey::Nohw(NohwKey::new(key)).key_len(), key.len());
        }
    }

    fn to_u128(v: __m128i) -> u128 {
        let mut u = 0;
        // SAFETY: __m128i has the same layout/meaning as u128
        unsafe {
            _mm_store_si128((&mut u as *mut u128).cast(), v);
        }
        u
    }

    // these test vectors from FIPS-197 appendices A.1 - A.3.

    #[test]
    fn test_construct() {
        for len in [16, 24, 32] {
            match AesKey::new(&[0; 32][..len]) {
                AesKey::Hw(HwKey::Aes128(_)) => assert_eq!(len, 16),
                AesKey::Hw(HwKey::Aes192(_)) => assert_eq!(len, 24),
                AesKey::Hw(HwKey::Aes256(_)) => assert_eq!(len, 32),
                AesKey::Vpaes(_) | AesKey::Nohw(_) => assert!(HaveAesHardware::check().is_none()),
            }
        }
    }

    #[test]
    fn test_key_expansion_128() {
        let Some(token) = HaveAesHardware::check() else {
            return;
        };
        let context = AesKey128::new(
            &[
                0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf,
                0x4f, 0x3c,
            ],
            token,
        );

        let expected = [
            0x2b7e1516_28aed2a6_abf71588_09cf4f3c,
            0xa0fafe17_88542cb1_23a33939_2a6c7605,
            0xf2c295f2_7a96b943_5935807a_7359f67f,
            0x3d80477d_4716fe3e_1e237e44_6d7a883b,
            0xef44a541_a8525b7f_b671253b_db0bad00,
            0xd4d1c6f8_7c839d87_caf2b8bc_11f915bc,
            0x6d88a37a_110b3efd_dbf98641_ca0093fd,
            0x4e54f70e_5f5fc9f3_84a64fb2_4ea6dc4f,
            0xead27321_b58dbad2_312bf560_7f8d292f,
            0xac7766f3_19fadc21_28d12941_575c006e,
            0xd014f9a8_c9ee2589_e13f0cc8_b6630ca6,
        ];

        for (i, expect) in expected.into_iter().enumerate() {
            assert_eq!(to_u128(context.round_keys[i]).swap_bytes(), expect);
        }
    }

    #[test]
    fn test_key_expansion_256() {
        let Some(token) = HaveAesHardware::check() else {
            return;
        };
        let context = AesKey256::new(
            &[
                0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae, 0xf0, 0x85, 0x7d,
                0x77, 0x81, 0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61, 0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3,
                0x09, 0x14, 0xdf, 0xf4,
            ],
            token,
        );

        let expected = [
            0x603deb10_15ca71be_2b73aef0_857d7781,
            0x1f352c07_3b6108d7_2d9810a3_0914dff4,
            0x9ba35411_8e6925af_a51a8b5f_2067fcde,
            0xa8b09c1a_93d194cd_be49846e_b75d5b9a,
            0xd59aecb8_5bf3c917_fee94248_de8ebe96,
            0xb5a9328a_2678a647_98312229_2f6c79b3,
            0x812c81ad_dadf48ba_24360af2_fab8b464,
            0x98c5bfc9_bebd198e_268c3ba7_09e04214,
            0x68007bac_b2df3316_96e939e4_6c518d80,
            0xc814e204_76a9fb8a_5025c02d_59c58239,
            0xde136967_6ccc5a71_fa256395_9674ee15,
            0x5886ca5d_2e2f31d7_7e0af1fa_27cf73c3,
            0x749c47ab_18501dda_e2757e4f_7401905a,
            0xcafaaae3_e4d59b34_9adf6ace_bd10190d,
            0xfe4890d1_e6188d0b_046df344_706c631e,
        ];

        for (i, expect) in expected.into_iter().enumerate() {
            assert_eq!(to_u128(context.round_keys[i]).swap_bytes(), expect);
        }
    }

    // FIPS-197 appendix A.2.
    #[test]
    fn test_key_expansion_192() {
        let Some(token) = HaveAesHardware::check() else {
            return;
        };
        let context = AesKey192::new(
            &[
                0x8e, 0x73, 0xb0, 0xf7, 0xda, 0x0e, 0x64, 0x52, 0xc8, 0x10, 0xf3, 0x2b, 0x80, 0x90,
                0x79, 0xe5, 0x62, 0xf8, 0xea, 0xd2, 0x52, 0x2c, 0x6b, 0x7b,
            ],
            token,
        );

        let expected = [
            0x8e73b0f7_da0e6452_c810f32b_809079e5,
            0x62f8ead2_522c6b7b_fe0c91f7_2402f5a5,
            0xec12068e_6c827f6b_0e7a95b9_5c56fec2,
            0x4db7b4bd_69b54118_85a74796_e92538fd,
            0xe75fad44_bb095386_485af057_21efb14f,
            0xa448f6d9_4d6dce24_aa326360_113b30e6,
            0xa25e7ed5_83b1cf9a_27f93943_6a94f767,
            0xc0a69407_d19da4e1_ec1786eb_6fa64971,
            0x485f7032_22cb8755_e26d1352_33f0b7b3,
            0x40beeb28_2f18a259_6747d26b_458c553e,
            0xa7e1466c_9411f1df_821f750a_ad07d753,
            0xca400538_8fcc5006_282d166a_bc3ce7b5,
            0xe98ba06f_448c773c_8ecc7204_01002202,
        ];

        for (i, expect) in expected.into_iter().enumerate() {
            assert_eq!(to_u128(context.round_keys[i]).swap_bytes(), expect);
        }
    }

    #[test]
    fn test_block_128() {
        let context = AesKey::new(&[
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f,
        ]);
        let block = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        assert_eq!(
            context.encrypt_block(&block),
            [
                0x69, 0xc4, 0xe0, 0xd8, 0x6a, 0x7b, 0x04, 0x30, 0xd8, 0xcd, 0xb7, 0x80, 0x70, 0xb4,
                0xc5, 0x5a
            ]
        );
    }

    #[test]
    fn test_block_256() {
        let context = AesKey::new(&[
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
            0x1c, 0x1d, 0x1e, 0x1f,
        ]);
        let block = [
            0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd,
            0xee, 0xff,
        ];
        assert_eq!(
            context.encrypt_block(&block),
            [
                0x8e, 0xa2, 0xb7, 0xca, 0x51, 0x67, 0x45, 0xbf, 0xea, 0xfc, 0x49, 0x90, 0x4b, 0x49,
                0x60, 0x89
            ]
        );
    }

    // Every other test sees only the path the CPU picks, so AES-NI is checked
    // against vpaes here, for each key size; `aes_ctr` and `aes_gcm` compare
    // their modes.
    #[test]
    fn hw_matches_vpaes() {
        let (Some(_), Some(ssse3)) = (HaveAesHardware::check(), HaveSsse3::check()) else {
            return;
        };
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let hw = AesKey::new(&key);
            assert!(matches!(hw, AesKey::Hw(_)));
            let vpaes = AesKey::Vpaes(VpaesKey::new(&key, ssse3));
            for block_seed in 0..4 {
                let block: [u8; 16] = bytes(16, block_seed).try_into().unwrap();
                assert_eq!(
                    vpaes.encrypt_block(&block),
                    hw.encrypt_block(&block),
                    "{key_len}-byte key, block {block_seed}"
                );
            }
        }
    }

    // Each decryption path the CPU offers must invert encryption, which the
    // tests above hold to AES on every path.
    #[test]
    fn every_path_decrypts() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let enc = AesKey::new(&key);
            let mut paths = vec![AesDecKey::Nohw(NohwKey::new(&key))];
            if let Some(token) = HaveSsse3::check() {
                paths.push(AesDecKey::Vpaes(VpaesDecKey::new(&key, token)));
            }
            if HaveAesHardware::check().is_some() {
                let hw = AesDecKey::new(&key);
                assert!(matches!(hw, AesDecKey::Hw(_)));
                paths.push(hw);
            }
            for block_seed in 0..4 {
                let block: [u8; 16] = bytes(16, block_seed).try_into().unwrap();
                let ct = enc.encrypt_block(&block);
                for (i, dec) in paths.iter().enumerate() {
                    let mut pt = ct;
                    dec.decrypt_block(&mut pt);
                    assert_eq!(
                        pt, block,
                        "{key_len}-byte key, path {i}, block {block_seed}"
                    );
                }
            }
        }
    }
}
