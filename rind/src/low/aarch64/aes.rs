// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
// refs:
// - https://documentation-service.arm.com/static/5f202270bb903e39c84d7ede
// - https://documentation-service.arm.com/static/65fdad3c1bc22b03bca90781
//   (sections C7.2.8, C7.2.10)
//
// cf. the x86_64 version, on which this one is based.

use core::arch::aarch64::*;

use super::cpu::HaveCryptoExt;
use super::vpaes_armv8::{VpaesDecKey, VpaesKey};
use crate::low;

// Keep all-zero valid when drop wipes the whole enum.
#[repr(u8)]
pub(crate) enum AesKey {
    /// The AES instructions', which the key picks when the CPU has the crypto
    /// extension.
    Hw(HwKey),
    /// NEON's, otherwise.
    Vpaes(VpaesKey),
}

impl AesKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        match (key.len(), HaveCryptoExt::check()) {
            (16, Some(token)) => Self::Hw(HwKey::Aes128(AesKey128::new(
                key.try_into().unwrap(),
                token,
            ))),
            (24, Some(token)) => Self::Hw(HwKey::Aes192(AesKey192::new(
                key.try_into().unwrap(),
                token,
            ))),
            (32, Some(token)) => Self::Hw(HwKey::Aes256(AesKey256::new(
                key.try_into().unwrap(),
                token,
            ))),
            (16 | 24 | 32, None) => Self::Vpaes(VpaesKey::new(key)),
            _ => unreachable!("callers check the AES key length"),
        }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        match self {
            Self::Hw(HwKey::Aes128(a128)) => a128.encrypt_block(block),
            Self::Hw(HwKey::Aes192(a192)) => a192.encrypt_block(block),
            Self::Hw(HwKey::Aes256(a256)) => a256.encrypt_block(block),
            Self::Vpaes(key) => key.encrypt_block(block),
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
        }
    }
}

/// A key for the AES instructions.
pub(crate) enum HwKey {
    Aes128(AesKey128),
    Aes192(AesKey192),
    Aes256(AesKey256),
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
}

impl AesDecKey {
    /// Expands `key`, which must be 16, 24, or 32 bytes.
    pub(crate) fn new(key: &[u8]) -> Self {
        match (key.len(), HaveCryptoExt::check()) {
            (16, Some(token)) => Self::Hw(HwDecKey::Aes128(
                AesKey128::new(key.try_into().unwrap(), token).decryption_round_keys(),
            )),
            (24, Some(token)) => Self::Hw(HwDecKey::Aes192(
                AesKey192::new(key.try_into().unwrap(), token).decryption_round_keys(),
            )),
            (32, Some(token)) => Self::Hw(HwDecKey::Aes256(
                AesKey256::new(key.try_into().unwrap(), token).decryption_round_keys(),
            )),
            (16 | 24 | 32, None) => Self::Vpaes(VpaesDecKey::new(key)),
            _ => unreachable!("callers check the AES key length"),
        }
    }

    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        match self {
            // SAFETY: only a `HaveCryptoExt` token builds the round keys.
            Self::Hw(HwDecKey::Aes128(round_keys)) => unsafe {
                hw_decrypt_block(round_keys, inout)
            },
            // SAFETY: as above.
            Self::Hw(HwDecKey::Aes192(round_keys)) => unsafe {
                hw_decrypt_block(round_keys, inout)
            },
            // SAFETY: as above.
            Self::Hw(HwDecKey::Aes256(round_keys)) => unsafe {
                hw_decrypt_block(round_keys, inout)
            },
            Self::Vpaes(key) => key.decrypt_block(inout),
        }
    }
}

impl Drop for AesDecKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for AesDecKey {}

/// Round keys for `aesd` in the equivalent inverse cipher, FIPS 197 section
/// 5.3.5, which only a `HaveCryptoExt` token builds: the encryption round
/// keys reversed, all but the outer two through InvMixColumns.
pub(crate) enum HwDecKey {
    Aes128([uint8x16_t; 10 + 1]),
    Aes192([uint8x16_t; 12 + 1]),
    Aes256([uint8x16_t; 14 + 1]),
}

/// An AES-128 key for the AES instructions, which only a `HaveCryptoExt`
/// token builds.
pub(crate) struct AesKey128 {
    round_keys: [uint8x16_t; 10 + 1],
}

impl AesKey128 {
    pub(crate) fn new(key: &[u8; 16], _: HaveCryptoExt) -> Self {
        let mut round_keys = [zero(); 10 + 1];
        // SAFETY: the token proves the CPU has the AES instructions.
        unsafe { aes128_expand(key, &mut round_keys) };
        Self { round_keys }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { aes128_block(&self.round_keys, block) }
    }

    pub(crate) fn round_keys(&self) -> &[uint8x16_t; 11] {
        &self.round_keys
    }

    fn decryption_round_keys(&self) -> [uint8x16_t; 10 + 1] {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { invert_round_keys(&self.round_keys) }
    }
}

/// An AES-192 key for the AES instructions, which only a `HaveCryptoExt`
/// token builds.
pub(crate) struct AesKey192 {
    round_keys: [uint8x16_t; 12 + 1],
}

impl AesKey192 {
    pub(crate) fn new(key: &[u8; 24], _: HaveCryptoExt) -> Self {
        // SAFETY: the token proves the CPU has the AES instructions.
        let round_keys = unsafe { aes192_expand(key) };
        Self { round_keys }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { aes_block(&self.round_keys, block) }
    }

    pub(crate) fn round_keys(&self) -> &[uint8x16_t; 13] {
        &self.round_keys
    }

    fn decryption_round_keys(&self) -> [uint8x16_t; 12 + 1] {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { invert_round_keys(&self.round_keys) }
    }
}

/// An AES-256 key for the AES instructions, which only a `HaveCryptoExt`
/// token builds.
pub(crate) struct AesKey256 {
    round_keys: [uint8x16_t; 14 + 1],
}

impl AesKey256 {
    pub(crate) fn new(key: &[u8; 32], _: HaveCryptoExt) -> Self {
        let mut round_keys = [zero(); 14 + 1];
        // SAFETY: the token proves the CPU has the AES instructions.
        unsafe { aes256_expand(key, &mut round_keys) };
        Self { round_keys }
    }

    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { aes256_block(&self.round_keys, block) }
    }

    pub(crate) fn round_keys(&self) -> &[uint8x16_t; 15] {
        &self.round_keys
    }

    fn decryption_round_keys(&self) -> [uint8x16_t; 14 + 1] {
        // SAFETY: only a `HaveCryptoExt` token builds `self`.
        unsafe { invert_round_keys(&self.round_keys) }
    }
}

fn zero() -> uint8x16_t {
    // SAFETY: this crate requires the `neon` cpu feature
    unsafe { vdupq_n_u8(0) }
}

const RCON: [u32; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

// The key schedule in vector registers, as aws-lc's `aes_hw_set_encrypt_key`
// runs it, rather than word by word through general registers. The
// expansions fill a local array, indexing their loops, and write `out` once:
// Aeneas translates neither a loop that writes through a reference nor one
// over an iterator of the round constants.
#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "aes")]
fn aes128_expand(key: &[u8; 16], out: &mut [uint8x16_t; 11]) {
    let mut t = load(key);
    let mut rk = [t; 11];
    for i in 0..10 {
        t = veorq_u8(xor_prefix(t), sub_rot_word(t, RCON[i]));
        rk[i + 1] = t;
    }
    *out = rk;
}

#[allow(clippy::needless_range_loop)]
#[target_feature(enable = "aes")]
fn aes256_expand(key: &[u8; 32], out: &mut [uint8x16_t; 15]) {
    let mut a = load(key[..16].try_into().unwrap());
    let mut b = load(key[16..].try_into().unwrap());
    let mut rk = [a; 15];
    rk[1] = b;

    // Round keys alternate: the first of each pair takes RotWord and the
    // round constant, as AES-128's do, and the second only SubWord.
    for i in 0..7 {
        a = veorq_u8(xor_prefix(a), sub_rot_word(b, RCON[i]));
        rk[2 * i + 2] = a;
        if i == 6 {
            break;
        }
        let w3 = vreinterpretq_u8_u32(vdupq_laneq_u32::<3>(vreinterpretq_u32_u8(a)));
        b = veorq_u8(xor_prefix(b), vaeseq_u8(w3, zero()));
        rk[2 * i + 3] = b;
    }
    *out = rk;
}

/// AES-192's schedule six words at a time: `a` holds each step's first four
/// words and `b` its last two, in its low half, so every other round key
/// straddles the two. Each step's first word takes RotWord, SubWord, and the
/// round constant of the step before's last, as `sub_rot_word` computes
/// them from a vector's last word.
#[target_feature(enable = "aes")]
fn aes192_expand(key: &[u8; 24]) -> [uint8x16_t; 13] {
    const ROT_WORD_1: [u8; 16] = [5, 6, 7, 4, 5, 6, 7, 4, 5, 6, 7, 4, 5, 6, 7, 4];
    let mut a = load(key[..16].try_into().unwrap());
    let mut b = vreinterpretq_u8_p128(u128::from(u64::from_le_bytes(
        key[16..].try_into().unwrap(),
    )));
    let rot_word_1 = load(&ROT_WORD_1);
    let mut out = [a; 13];
    for step in 1..9 {
        let sub = veorq_u8(
            vaeseq_u8(vqtbl1q_u8(b, rot_word_1), zero()),
            vreinterpretq_u8_u32(vdupq_n_u32(RCON[step - 1])),
        );
        a = veorq_u8(xor_prefix(a), sub);
        if step % 2 == 1 {
            // The low halves of `b` then `a`.
            out[3 * (step - 1) / 2 + 1] =
                vreinterpretq_u8_u64(vzip1q_u64(vreinterpretq_u64_u8(b), vreinterpretq_u64_u8(a)));
        } else {
            out[3 * step / 2] = a;
        }
        if step == 8 {
            break;
        }
        let w3 = vreinterpretq_u8_u32(vdupq_laneq_u32::<3>(vreinterpretq_u32_u8(a)));
        b = veorq_u8(veorq_u8(b, vextq_u8::<12>(zero(), b)), w3);
        if step % 2 == 1 {
            // The high half of `a`, then the low of `b`.
            out[3 * (step - 1) / 2 + 2] = vextq_u8::<8>(a, b);
        }
    }
    out
}

/// SubWord(RotWord(w3)) XOR `rcon` in every word, where w3 is `t`'s last.
///
/// `aese` with a zero key on four equal columns is SubBytes alone, since
/// ShiftRows moves nothing.
#[inline]
#[target_feature(enable = "aes")]
fn sub_rot_word(t: uint8x16_t, rcon: u32) -> uint8x16_t {
    const ROT_WORD_3: [u8; 16] = [
        13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12, 13, 14, 15, 12,
    ];
    let rot = vqtbl1q_u8(t, load(&ROT_WORD_3));
    veorq_u8(
        vaeseq_u8(rot, zero()),
        vreinterpretq_u8_u32(vdupq_n_u32(rcon)),
    )
}

/// Each word of `t` XORed with the words before it: the round key's words
/// before the SubWord term is added.
#[inline]
#[target_feature(enable = "neon")]
fn xor_prefix(t: uint8x16_t) -> uint8x16_t {
    let t = veorq_u8(t, vextq_u8::<12>(zero(), t));
    veorq_u8(t, vextq_u8::<8>(zero(), t))
}

/// `block` as a vector, its first byte in lane 0, as `vld1q_u8` loads it.
/// A value rather than a pointer, which Aeneas cannot translate.
#[inline]
#[target_feature(enable = "aes")]
fn load(block: &[u8; 16]) -> uint8x16_t {
    vreinterpretq_u8_p128(u128::from_le_bytes(*block))
}

/// `v`'s bytes, lane 0 first, as `vst1q_u8` stores them.
#[inline]
#[target_feature(enable = "aes")]
fn store(v: uint8x16_t) -> [u8; 16] {
    vreinterpretq_p128_u8(v).to_le_bytes()
}

/// The round keys for `aesd` from those for `aese`.
#[target_feature(enable = "aes")]
fn invert_round_keys<const N: usize>(round_keys: &[uint8x16_t; N]) -> [uint8x16_t; N] {
    let mut out = [zero(); N];
    out[0] = round_keys[N - 1];
    for i in 1..N - 1 {
        out[i] = vaesimcq_u8(round_keys[N - 1 - i]);
    }
    out[N - 1] = round_keys[0];
    out
}

#[target_feature(enable = "aes")]
fn hw_decrypt_block<const N: usize>(round_keys: &[uint8x16_t; N], block_inout: &mut [u8; 16]) {
    let mut block = load(block_inout);
    block = vaesdq_u8(block, round_keys[0]);
    for round_key in &round_keys[1..N - 1] {
        block = vaesdq_u8(vaesimcq_u8(block), *round_key);
    }
    block = veorq_u8(block, round_keys[N - 1]);
    *block_inout = store(block);
}

#[target_feature(enable = "aes")]
fn aes128_block(round_keys: &[uint8x16_t; 11], block: &[u8; 16]) -> [u8; 16] {
    store(_aes128_block(round_keys, load(block)))
}

#[target_feature(enable = "aes")]
#[inline]
pub(crate) fn _aes128_block(round_keys: &[uint8x16_t; 11], block: uint8x16_t) -> uint8x16_t {
    let block = vaeseq_u8(block, round_keys[0]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[1]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[2]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[3]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[4]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[5]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[6]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[7]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[8]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[9]);
    veorq_u8(block, round_keys[10])
}

macro_rules! round_8 {
    ($b0:ident, $b1:ident, $b2:ident, $b3:ident, $b4:ident, $b5:ident, $b6:ident, $b7:ident, $rk:expr) => {
        let rk = $rk;
        $b0 = vaeseq_u8($b0, rk);
        $b0 = vaesmcq_u8($b0);
        $b1 = vaeseq_u8($b1, rk);
        $b1 = vaesmcq_u8($b1);
        $b2 = vaeseq_u8($b2, rk);
        $b2 = vaesmcq_u8($b2);
        $b3 = vaeseq_u8($b3, rk);
        $b3 = vaesmcq_u8($b3);
        $b4 = vaeseq_u8($b4, rk);
        $b4 = vaesmcq_u8($b4);
        $b5 = vaeseq_u8($b5, rk);
        $b5 = vaesmcq_u8($b5);
        $b6 = vaeseq_u8($b6, rk);
        $b6 = vaesmcq_u8($b6);
        $b7 = vaeseq_u8($b7, rk);
        $b7 = vaesmcq_u8($b7);
    };
}

#[target_feature(enable = "aes")]
#[inline]
pub(crate) fn _aes128_8_blocks(
    round_keys: &[uint8x16_t; 11],
    mut b0: uint8x16_t,
    mut b1: uint8x16_t,
    mut b2: uint8x16_t,
    mut b3: uint8x16_t,
    mut b4: uint8x16_t,
    mut b5: uint8x16_t,
    mut b6: uint8x16_t,
    mut b7: uint8x16_t,
) -> (
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
) {
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[0]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[1]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[2]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[3]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[4]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[5]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[6]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[7]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[8]);

    let b0 = vaeseq_u8(b0, round_keys[9]);
    let b1 = vaeseq_u8(b1, round_keys[9]);
    let b2 = vaeseq_u8(b2, round_keys[9]);
    let b3 = vaeseq_u8(b3, round_keys[9]);
    let b4 = vaeseq_u8(b4, round_keys[9]);
    let b5 = vaeseq_u8(b5, round_keys[9]);
    let b6 = vaeseq_u8(b6, round_keys[9]);
    let b7 = vaeseq_u8(b7, round_keys[9]);
    (
        veorq_u8(b0, round_keys[10]),
        veorq_u8(b1, round_keys[10]),
        veorq_u8(b2, round_keys[10]),
        veorq_u8(b3, round_keys[10]),
        veorq_u8(b4, round_keys[10]),
        veorq_u8(b5, round_keys[10]),
        veorq_u8(b6, round_keys[10]),
        veorq_u8(b7, round_keys[10]),
    )
}

/// One block under any key size, by its number of round keys.
#[target_feature(enable = "aes")]
fn aes_block<const N: usize>(round_keys: &[uint8x16_t; N], block: &[u8; 16]) -> [u8; 16] {
    let mut b = load(block);
    for rk in &round_keys[..N - 2] {
        b = vaesmcq_u8(vaeseq_u8(b, *rk));
    }
    b = veorq_u8(vaeseq_u8(b, round_keys[N - 2]), round_keys[N - 1]);
    store(b)
}

#[target_feature(enable = "aes")]
fn aes256_block(round_keys: &[uint8x16_t; 15], block: &[u8; 16]) -> [u8; 16] {
    store(_aes256_block(round_keys, load(block)))
}

#[target_feature(enable = "aes")]
#[inline]
pub(crate) fn _aes256_block(round_keys: &[uint8x16_t; 15], block: uint8x16_t) -> uint8x16_t {
    let block = vaeseq_u8(block, round_keys[0]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[1]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[2]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[3]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[4]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[5]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[6]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[7]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[8]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[9]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[10]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[11]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[12]);
    let block = vaesmcq_u8(block);
    let block = vaeseq_u8(block, round_keys[13]);
    veorq_u8(block, round_keys[14])
}

#[target_feature(enable = "aes")]
#[inline]
pub(crate) fn _aes256_8_blocks(
    round_keys: &[uint8x16_t; 15],
    mut b0: uint8x16_t,
    mut b1: uint8x16_t,
    mut b2: uint8x16_t,
    mut b3: uint8x16_t,
    mut b4: uint8x16_t,
    mut b5: uint8x16_t,
    mut b6: uint8x16_t,
    mut b7: uint8x16_t,
) -> (
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
    uint8x16_t,
) {
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[0]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[1]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[2]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[3]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[4]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[5]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[6]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[7]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[8]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[9]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[10]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[11]);
    round_8!(b0, b1, b2, b3, b4, b5, b6, b7, round_keys[12]);

    let b0 = vaeseq_u8(b0, round_keys[13]);
    let b1 = vaeseq_u8(b1, round_keys[13]);
    let b2 = vaeseq_u8(b2, round_keys[13]);
    let b3 = vaeseq_u8(b3, round_keys[13]);
    let b4 = vaeseq_u8(b4, round_keys[13]);
    let b5 = vaeseq_u8(b5, round_keys[13]);
    let b6 = vaeseq_u8(b6, round_keys[13]);
    let b7 = vaeseq_u8(b7, round_keys[13]);
    (
        veorq_u8(b0, round_keys[14]),
        veorq_u8(b1, round_keys[14]),
        veorq_u8(b2, round_keys[14]),
        veorq_u8(b3, round_keys[14]),
        veorq_u8(b4, round_keys[14]),
        veorq_u8(b5, round_keys[14]),
        veorq_u8(b6, round_keys[14]),
        veorq_u8(b7, round_keys[14]),
    )
}

/// Eight blocks under any key size, by its number of round keys,
/// interleaved as [`_aes128_8_blocks`] does.
#[target_feature(enable = "aes")]
#[inline]
pub(crate) fn _aes_8_blocks<const N: usize>(
    round_keys: &[uint8x16_t; N],
    mut b: [uint8x16_t; 8],
) -> [uint8x16_t; 8] {
    for rk in &round_keys[..N - 2] {
        for b in &mut b {
            *b = vaesmcq_u8(vaeseq_u8(*b, *rk));
        }
    }
    for b in &mut b {
        *b = veorq_u8(vaeseq_u8(*b, round_keys[N - 2]), round_keys[N - 1]);
    }
    b
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::aes_ctr;

    #[test]
    fn key_len() {
        for key in [&[0u8; 16][..], &[0u8; 24], &[0u8; 32]] {
            assert_eq!(AesKey::new(key).key_len(), key.len());
            assert_eq!(AesKey::Vpaes(VpaesKey::new(key)).key_len(), key.len());
        }
    }

    fn to_u128(v: uint8x16_t) -> u128 {
        let mut buf = [0u8; 16];
        // SAFETY: This crate requires the `neon` cpu feature.
        unsafe {
            vst1q_u8(buf.as_mut_ptr(), v);
        }
        u128::from_be_bytes(buf)
    }

    // these test vectors from FIPS-197 appendices A.1 - A.3.

    #[test]
    fn test_construct() {
        for len in [16, 24, 32] {
            match AesKey::new(&[0; 32][..len]) {
                AesKey::Hw(HwKey::Aes128(_)) => assert_eq!(len, 16),
                AesKey::Hw(HwKey::Aes192(_)) => assert_eq!(len, 24),
                AesKey::Hw(HwKey::Aes256(_)) => assert_eq!(len, 32),
                AesKey::Vpaes(_) => assert!(HaveCryptoExt::check().is_none()),
            }
        }
    }

    #[test]
    fn test_key_expansion_128() {
        let Some(token) = HaveCryptoExt::check() else {
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
            assert_eq!(to_u128(context.round_keys[i]), expect);
        }
    }

    #[test]
    fn test_key_expansion_256() {
        let Some(token) = HaveCryptoExt::check() else {
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
            assert_eq!(to_u128(context.round_keys[i]), expect);
        }
    }

    // FIPS-197 appendix A.2.
    #[test]
    fn test_key_expansion_192() {
        let Some(token) = HaveCryptoExt::check() else {
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
            assert_eq!(to_u128(context.round_keys[i]), expect);
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

    // Every other test sees only the path the CPU picks, so the AES
    // instructions are checked against vpaes here: each key size, single
    // blocks, and counter mode across the 32-bit counter's wrap.
    #[test]
    fn hw_matches_vpaes() {
        if HaveCryptoExt::check().is_none() {
            return;
        }
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let hw = AesKey::new(&key);
            assert!(matches!(hw, AesKey::Hw(_)));
            let vpaes = AesKey::Vpaes(VpaesKey::new(&key));

            let block: [u8; 16] = bytes(16, seed).try_into().unwrap();
            assert_eq!(
                vpaes.encrypt_block(&block),
                hw.encrypt_block(&block),
                "{key_len}-byte key block"
            );

            let nonce = bytes(12, seed).try_into().unwrap();
            for counter in [0, 1, u32::MAX - 3, u32::MAX] {
                for len in [1, 15, 16, 17, 127, 128, 129, 300] {
                    let mut want = bytes(len, counter);
                    let mut got = want.clone();
                    aes_ctr::apply(&hw, &nonce, counter, &mut want);
                    aes_ctr::apply(&vpaes, &nonce, counter, &mut got);
                    assert_eq!(
                        got, want,
                        "{key_len}-byte key, counter {counter}, {len} bytes"
                    );
                }
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
            let mut paths = vec![AesDecKey::Vpaes(VpaesDecKey::new(&key))];
            if HaveCryptoExt::check().is_some() {
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
