// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//
//! Refs.
//! - <https://www.intel.com/content/dam/www/public/us/en/documents/software-support/enabling-high-performance-gcm.pdf>
//! - <https://www.intel.com/content/dam/develop/external/us/en/documents/clmul-wp-rev-2-02-2014-04-20.pdf>
//! - <https://patchwork.kernel.org/project/linux-crypto/patch/20240527075626.142576-3-ebiggers@kernel.org/>
//! - <https://github.com/google/boringssl/blob/d5440dd2c2c500ac2d3bba4afec47a054b4d99ae/crypto/fipsmodule/aes/asm/aes-gcm-avx512-x86_64.pl>
//!
//! The latter two especially, as we're using the arithmetic from those.

use core::arch::x86_64::*;
use core::mem;

use super::aes_gcm_avx::AvxKernel;
use super::aes_gcm_vaes::VaesKernel;
use super::cpu::{
    HaveAesHardware, HaveAvx512ForAesGcm, HaveAvxMovbeForAesGcm, HaveSsse3, HaveVaesAvx2ForAesGcm,
};
use super::ghash_nohw::NohwTable;
use super::ghash_ssse3_x86_64::Ssse3Table;
use crate::low;

macro_rules! mul {
    ($lo:ident, $mi:ident, $hi:ident, $x:ident, $h:expr, $hx:expr) => {
        let tlo = _mm_clmulepi64_si128($x, $h, 0x00);
        $lo = _mm_xor_si128(tlo, $lo);

        let xx = _mm_shuffle_epi32($x, 0b01_00_11_10);
        let xx = _mm_xor_si128(xx, $x);

        let thi = _mm_clmulepi64_si128($x, $h, 0x11);
        $hi = _mm_xor_si128(thi, $hi);

        let tmi = _mm_clmulepi64_si128(xx, $hx, 0x00);
        $mi = _mm_xor_si128(tmi, $mi);
    };
}

macro_rules! reduce {
    ($lo:ident, $mi:ident, $hi:ident) => {{
        let $mi = _mm_xor_si128($mi, $lo);
        let $mi = _mm_xor_si128($mi, $hi);

        let ls = _mm_shuffle_epi32($lo, 0b01_00_11_10);
        let $lo = _mm_clmulepi64_si128(u128_to_m128i(GF128_POLY_HI), $lo, 0x00);
        let $mi = _mm_xor_si128($mi, ls);
        let $mi = _mm_xor_si128($mi, $lo);

        let ms = _mm_shuffle_epi32($mi, 0b01_00_11_10);
        let $mi = _mm_clmulepi64_si128(u128_to_m128i(GF128_POLY_HI), $mi, 0x00);
        let $hi = _mm_xor_si128($hi, ms);
        let $hi = _mm_xor_si128($hi, $mi);
        $hi
    }};
}

pub(crate) enum GhashTable {
    Clmul(ClmulTable),
    /// VAES without AVX-512: Vale's AES-GCM or the PCLMULQDQ path for short
    /// messages, and BoringSSL's 256-bit kernel for long ones.
    VaesAvx2(ClmulTable, VaesKernel, AvxKernel),
    /// AVX and MOVBE without VAES: Vale's AES-GCM, and the PCLMULQDQ path
    /// for an AAD or message of 2^32 bytes or more, beyond Vale's proof.
    Avx(ClmulTable, AvxKernel),
    Avx512(GhashTableAvx512),
    /// SSSE3's, which the table picks when the CPU lacks AES-NI or
    /// PCLMULQDQ.
    Ssse3(Ssse3Table),
    /// Integer code's, which the table picks when the CPU also lacks SSSE3.
    Nohw(NohwTable),
}

impl GhashTable {
    pub(crate) fn new(h: u128) -> Self {
        let Some(hw) = HaveAesHardware::check() else {
            return match HaveSsse3::check() {
                Some(token) => Self::Ssse3(Ssse3Table::new(&h.to_be_bytes(), token)),
                None => Self::Nohw(NohwTable::new(&h.to_be_bytes())),
            };
        };
        if let Some(token) = HaveAvx512ForAesGcm::check() {
            return Self::Avx512(GhashTableAvx512::new(h, hw, token));
        }
        if let Some(token) = HaveVaesAvx2ForAesGcm::check() {
            let vaes = VaesKernel::avx2(h, token);
            let table = ClmulTable::from_powers(vaes.powers(), hw);
            let vale = AvxKernel::new(&table, h, token.avx_movbe());
            return Self::VaesAvx2(table, vaes, vale);
        }
        if let Some(token) = HaveAvxMovbeForAesGcm::check() {
            let table = ClmulTable::new(h, hw);
            let kernel = AvxKernel::new(&table, h, token);
            return Self::Avx(table, kernel);
        }

        Self::Clmul(ClmulTable::new(h, hw))
    }
}

impl Drop for GhashTable {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

// SAFETY: GhashTable is POD type
impl low::generic::zeroise::Zeroable for GhashTable {}

/// Powers of a GHASH key for PCLMULQDQ, which only a `HaveAesHardware` token
/// builds.
pub(crate) struct ClmulTable {
    /// H, H^2, H^3, H^4, ... H^8
    powers: [__m128i; 8],

    /// `powers_xor[i]` is `powers[i].lo64 ^ powers[i].hi64`
    ///
    /// This can be used directly in the middle Karatsuba term.
    powers_xor: [__m128i; 8],
}

impl ClmulTable {
    pub(crate) fn new(h: u128, _: HaveAesHardware) -> Self {
        // SAFETY: the token proves the CPU has PCLMULQDQ.
        unsafe { Self::with_powers(&Self::powers(h)) }
    }

    /// The table for the powers a VAES kernel's table holds, H^n down to H^1
    /// for some `n` of at least 8, so they are not computed twice.
    pub(crate) fn from_powers(descending: &[__m128i], _: HaveAesHardware) -> Self {
        let mut powers = [zero(); 8];
        for (p, d) in powers.iter_mut().zip(descending.iter().rev()) {
            *p = *d;
        }
        // SAFETY: the token proves the CPU has PCLMULQDQ.
        unsafe { Self::with_powers(&powers) }
    }

    /// H to H^8, multiplied as a tree, so the longest chain of dependent
    /// multiplies is three rather than seven.
    #[target_feature(enable = "pclmulqdq")]
    fn powers(h: u128) -> [__m128i; 8] {
        let h = gf128_big_endian(u128_to_m128i(h));
        let h2 = _mul(h, h);
        let (h3, h4) = (_mul(h2, h), _mul(h2, h2));
        let (h5, h6, h7, h8) = (_mul(h4, h), _mul(h4, h2), _mul(h4, h3), _mul(h4, h4));
        [h, h2, h3, h4, h5, h6, h7, h8]
    }

    #[target_feature(enable = "pclmulqdq")]
    fn with_powers(powers: &[__m128i; 8]) -> Self {
        Self {
            powers: *powers,
            powers_xor: powers.map(|p| xor_halves(p)),
        }
    }

    /// The GHASH key powers in the layout Vale's AES-GCM reads, for the
    /// GHASH key `h` this table was made from.
    pub(crate) fn vale_hkeys(&self, h: u128) -> [__m128i; 8] {
        let [h1, h2, h3, h4, h5, h6, ..] = self.powers;
        [h1, h2, u128_to_m128i(h), h3, h4, zero(), h5, h6]
    }

    /// Hashes `bytes` into `current`.
    ///
    /// It is SSE-encoded on every CPU, as the by-8 AES-GCM kernel is.
    #[target_feature(enable = "pclmulqdq,ssse3")]
    fn add(&self, bytes: &[u8], mut current: __m128i) -> __m128i {
        let (eight_blocks, remainder) = bytes.as_chunks::<128>();

        for chunk8 in eight_blocks {
            let [b1, b2, b3, b4, b5, b6, b7, b8] = chunk8.as_chunks::<16>().0 else {
                unreachable!()
            };
            let b1 = _mm_xor_si128(current, load_be(b1));
            current = _mul8(
                self,
                b1,
                load_be(b2),
                load_be(b3),
                load_be(b4),
                load_be(b5),
                load_be(b6),
                load_be(b7),
                load_be(b8),
            );
        }

        self.add_tail(remainder, current)
    }

    /// Multiplies `x` by H.
    #[target_feature(enable = "pclmulqdq")]
    fn mul_h(&self, x: __m128i) -> __m128i {
        let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
        mul!(lo, mi, hi, x, self.powers[0], self.powers_xor[0]);
        reduce!(lo, mi, hi)
    }

    /// Hashes the fewer than eight blocks after `add`'s chunks, zero-padding
    /// the last: block `i` of `n` is multiplied by H^(n-i), so the sum needs
    /// one reduction rather than one per block.
    #[target_feature(enable = "pclmulqdq,ssse3")]
    fn add_tail(&self, bytes: &[u8], current: __m128i) -> __m128i {
        if bytes.is_empty() {
            return current;
        }

        let n = bytes.len().div_ceil(16);
        let mut powers = self.powers[..n].iter().zip(&self.powers_xor[..n]).rev();

        let (blocks, partial) = bytes.as_chunks::<16>();
        let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
        let mut x = current;
        for (block, (h, hx)) in blocks.iter().zip(&mut powers) {
            let b = _mm_xor_si128(x, load_be(block));
            mul!(lo, mi, hi, b, *h, *hx);
            x = zero();
        }
        if let Some((h, hx)) = powers.next() {
            let b = _mm_xor_si128(x, _mm_shuffle_epi8(load_partial(partial), BYTESWAP));
            mul!(lo, mi, hi, b, *h, *hx);
        }
        reduce!(lo, mi, hi)
    }
}

pub(crate) struct GhashTableAvx512 {
    /// For inputs too short to fill the 512-bit vectors.
    pub(crate) clmul: ClmulTable,
    /// BoringSSL's 512-bit kernel, for long messages, whose table also holds
    /// the powers the 512-bit multiplies here take.
    pub(crate) vaes: VaesKernel,
    pub(crate) token: HaveAvx512ForAesGcm,
}

impl GhashTableAvx512 {
    pub(crate) fn new(h: u128, hw: HaveAesHardware, token: HaveAvx512ForAesGcm) -> Self {
        let vaes = VaesKernel::avx512(h, token);
        let clmul = ClmulTable::from_powers(vaes.powers(), hw);
        Self { clmul, vaes, token }
    }

    /// H^16, H^15, ... H^1: descending, so a tail of `n` blocks multiplies
    /// by the last `n`.
    fn powers(&self) -> &[__m512i; 4] {
        let powers = self.vaes.powers();
        assert_eq!(powers.len(), 16);
        // SAFETY: the 512-bit kernel's table holds 16 powers, 64-byte
        // aligned as `__m512i` needs, and any bits are a valid `__m512i`.
        unsafe { &*powers.as_ptr().cast() }
    }

    #[target_feature(enable = "vpclmulqdq,avx512bw,avx512f,avx512vl")]
    fn add(&self, bytes: &[u8], mut current: __m128i) -> __m128i {
        let bswap_mask = _mm512_broadcast_i32x4(BYTESWAP);

        let (by_16_blocks, remainder) = bytes.as_chunks::<256>();
        for chunk16 in by_16_blocks {
            // SAFETY: `chunk16` is 256 bytes and readable, via `chunks_exact`
            let (m0123, m4567, m89ab, mcdef) = unsafe {
                (
                    _mm512_loadu_epi8(chunk16.as_ptr().add(0).cast()),
                    _mm512_loadu_epi8(chunk16.as_ptr().add(64).cast()),
                    _mm512_loadu_epi8(chunk16.as_ptr().add(128).cast()),
                    _mm512_loadu_epi8(chunk16.as_ptr().add(192).cast()),
                )
            };

            let m0123 = _mm512_shuffle_epi8(m0123, bswap_mask);
            let m4567 = _mm512_shuffle_epi8(m4567, bswap_mask);
            let m89ab = _mm512_shuffle_epi8(m89ab, bswap_mask);
            let mcdef = _mm512_shuffle_epi8(mcdef, bswap_mask);

            let c0___ = _mm512_inserti32x4::<0>(_mm512_setzero_si512(), current);
            let m0123 = _mm512_xor_epi64(m0123, c0___);

            current = _mul16(self, m0123, m4567, m89ab, mcdef);
        }

        // A short input, such as AAD or the length block, has too few blocks
        // to fill vectors, so it is quicker to hash it by the PCLMULQDQ path.
        self.clmul.add(remainder, current)
    }
}

pub(crate) struct Ghash<'a> {
    pub(crate) table: &'a GhashTable,
    pub(crate) current: __m128i,
}

impl<'a> Ghash<'a> {
    pub(crate) fn new(table: &'a GhashTable) -> Self {
        Self {
            table,
            current: zero(),
        }
    }

    /// Input `bytes` to the computation.
    ///
    /// `bytes` is zero-padded, if required.
    pub(crate) fn add(&mut self, bytes: &[u8]) {
        self.current = match self.table {
            GhashTable::Clmul(table)
            | GhashTable::VaesAvx2(table, ..)
            | GhashTable::Avx(table, _) => {
                // SAFETY: only a `HaveAesHardware` token builds `table`,
                // proving PCLMULQDQ.
                unsafe { table.add(bytes, self.current) }
            }
            // SAFETY: avx512.token proves features were dynamically checked
            GhashTable::Avx512(avx512) => unsafe { avx512.add(bytes, self.current) },
            GhashTable::Ssse3(table) => {
                return self.add_by(bytes, |xi, blocks| table.ghash(xi, blocks));
            }
            GhashTable::Nohw(table) => {
                return self.add_by(bytes, |xi, blocks| table.ghash(xi, blocks));
            }
        };
    }

    /// Inputs `bytes`, zero-padded, by `ghash`, which folds whole blocks into
    /// the state in GCM's byte order.
    fn add_by(&mut self, bytes: &[u8], ghash: impl Fn(&mut [u8; 16], &[[u8; 16]])) {
        let mut xi = self.xi();
        let (blocks, tail) = bytes.as_chunks::<16>();
        ghash(&mut xi, blocks);
        if !tail.is_empty() {
            let mut last = [0u8; 16];
            last[..tail.len()].copy_from_slice(tail);
            ghash(&mut xi, &[last]);
        }
        self.set_xi(&xi);
    }

    /// Inputs GCM's last block: the bit lengths of the AAD and the message.
    pub(crate) fn add_lengths(&mut self, aad_len: usize, msg_len: usize) {
        let block = ((aad_len as u128 * 8) << 64) | (msg_len as u128 * 8);
        let table = match self.table {
            GhashTable::Clmul(table)
            | GhashTable::VaesAvx2(table, ..)
            | GhashTable::Avx(table, _)
            | GhashTable::Avx512(GhashTableAvx512 { clmul: table, .. }) => table,
            GhashTable::Ssse3(_) | GhashTable::Nohw(_) => return self.add(&block.to_be_bytes()),
        };
        // SAFETY: only a `HaveAesHardware` token builds `table`, proving
        // PCLMULQDQ, and every x86_64 CPU has SSE2.
        self.current = unsafe { table.mul_h(_mm_xor_si128(self.current, u128_to_m128i(block))) };
    }

    /// The tag: the hash, in GCM's byte order, XORed with `mask`.
    pub(crate) fn tag(self, mask: &[u8; 16]) -> [u8; 16] {
        let mut tag = [0u8; 16];
        // SAFETY: every x86_64 CPU has SSE2, and `mask` and `tag` are 16
        // readable and writable bytes
        unsafe {
            let mask = _mm_loadu_si128(mask.as_ptr().cast());
            let tag_v = _mm_xor_si128(byte_reverse(self.current), mask);
            _mm_storeu_si128(tag.as_mut_ptr().cast(), tag_v);
        }
        tag
    }

    /// The state in GCM's byte order, as BoringSSL's `Xi`.
    #[inline]
    pub(crate) fn xi(&self) -> [u8; 16] {
        let mut xi = [0u8; 16];
        // SAFETY: every x86_64 CPU has SSE2, and `xi` is 16 writable bytes.
        // One vector store, so the kernels' 16-byte load of it is forwarded.
        unsafe { _mm_storeu_si128(xi.as_mut_ptr().cast(), byte_reverse(self.current)) };
        xi
    }

    /// Sets the state from GCM's byte order, as BoringSSL's `Xi`.
    #[inline]
    pub(crate) fn set_xi(&mut self, xi: &[u8; 16]) {
        // SAFETY: every x86_64 CPU has SSE2, and `xi` is 16 readable bytes
        self.current = byte_reverse(unsafe { _mm_loadu_si128(xi.as_ptr().cast()) });
    }
}

#[inline]
#[target_feature(enable = "pclmulqdq")]
fn _mul(a: __m128i, b: __m128i) -> __m128i {
    // SAFETY: intrinsics. see [crate::low::inline_assembly_safety#safety-of-intrinsics] for safety info.
    let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
    let bx = xor_halves(b);
    mul!(lo, mi, hi, a, b, bx);
    reduce!(lo, mi, hi)
}

#[inline]
#[target_feature(enable = "pclmulqdq")]
pub(crate) fn _mul8(
    table: &ClmulTable,
    x1: __m128i,
    x2: __m128i,
    x3: __m128i,
    x4: __m128i,
    x5: __m128i,
    x6: __m128i,
    x7: __m128i,
    x8: __m128i,
) -> __m128i {
    let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
    mul!(lo, mi, hi, x1, table.powers[7], table.powers_xor[7]);
    mul!(lo, mi, hi, x2, table.powers[6], table.powers_xor[6]);
    mul!(lo, mi, hi, x3, table.powers[5], table.powers_xor[5]);
    mul!(lo, mi, hi, x4, table.powers[4], table.powers_xor[4]);
    mul!(lo, mi, hi, x5, table.powers[3], table.powers_xor[3]);
    mul!(lo, mi, hi, x6, table.powers[2], table.powers_xor[2]);
    mul!(lo, mi, hi, x7, table.powers[1], table.powers_xor[1]);
    mul!(lo, mi, hi, x8, table.powers[0], table.powers_xor[0]);
    reduce!(lo, mi, hi)
}

#[inline]
#[target_feature(enable = "vpclmulqdq,avx512f,avx512vl")]
pub(crate) fn _mul16(
    table: &GhashTableAvx512,
    x0123: __m512i,
    x4567: __m512i,
    x89ab: __m512i,
    xcdef: __m512i,
) -> __m128i {
    let powers = table.powers();
    let gfpoly = _mm512_broadcast_i32x4(GF128_POLY_LO);

    let lo0 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x00);
    let lo1 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x00);
    let lo2 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x00);

    let lo01 = _mm512_xor_epi32(lo0, lo1);
    let lo3 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x00);
    let lo = _mm512_ternarylogic_epi64(lo2, lo3, lo01, TERNARY_XOR);
    let mi0 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x01);

    let mi1 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x01);
    let mi2 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x01);
    let mi012 = _mm512_ternarylogic_epi32(mi0, mi1, mi2, TERNARY_XOR);
    let mi3 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x01);

    let mi4 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x10);
    let mi01234 = _mm512_ternarylogic_epi32(mi012, mi3, mi4, TERNARY_XOR);
    let mi5 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x10);
    let mi6 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x10);

    let mi = _mm512_ternarylogic_epi64(mi01234, mi5, mi6, TERNARY_XOR);
    let lo_r = _mm512_clmulepi64_epi128(gfpoly, lo, 0x01);
    let mi7 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x10);
    let mi = _mm512_xor_epi32(mi7, mi);

    let lo_s = _mm512_shuffle_epi32(lo, 0b01_00_11_10);
    let hi0 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x11);
    let hi1 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x11);
    let hi2 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x11);

    let mi = _mm512_ternarylogic_epi32(lo_r, lo_s, mi, TERNARY_XOR);
    let hi3 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x11);
    let hi012 = _mm512_ternarylogic_epi32(hi0, hi1, hi2, TERNARY_XOR);
    let mi_r = _mm512_clmulepi64_epi128(gfpoly, mi, 0x01);

    let hi = _mm512_xor_epi32(hi012, hi3);
    let mi_s = _mm512_shuffle_epi32(mi, 0b01_00_11_10);
    let r = _mm512_ternarylogic_epi32(mi_r, mi_s, hi, TERNARY_XOR);

    // xor together all terms of `r`
    let a = _mm512_extracti32x4_epi32::<0>(r);
    let b = _mm512_extracti32x4_epi32::<1>(r);
    let c = _mm512_extracti32x4_epi32::<2>(r);
    let d = _mm512_extracti32x4_epi32::<3>(r);
    let ab = _mm_xor_si128(a, b);
    _mm_ternarylogic_epi32(ab, c, d, TERNARY_XOR)
}

/// Hashes a tail of `len` bytes, under 256, into `current`.
///
/// `x` holds the tail's blocks byte-reversed and zero-padded, so the vectors
/// past it are zero. Block `i` of `n` is multiplied by H^(n-i), so the sum
/// needs one reduction rather than one per block.
#[inline]
#[target_feature(enable = "vpclmulqdq,avx512f,avx512vl")]
pub(crate) fn _mul_tail(
    table: &GhashTableAvx512,
    current: __m128i,
    x: [__m512i; 4],
    len: usize,
) -> __m128i {
    // `x` holds at most 16 blocks, and the table 16 powers.
    assert!(len <= 256);
    let n = len.div_ceil(16);
    if n == 0 {
        return current;
    }

    // The powers descend to H^1, so H^n is `n` blocks before their end.
    let powers = table.vaes.powers();
    let (mut lo, mut mi, mut hi) = (
        _mm512_setzero_si512(),
        _mm512_setzero_si512(),
        _mm512_setzero_si512(),
    );
    for (j, x) in x.into_iter().enumerate().take(n.div_ceil(4)) {
        let x = match j {
            0 => _mm512_xor_epi64(x, _mm512_inserti32x4::<0>(_mm512_setzero_si512(), current)),
            _ => x,
        };
        // Up to four blocks left from here on, from H^(n-4j); slicing them
        // bounds the load by the table, whatever the arithmetic.
        let h = &powers[16 - n + 4 * j..][..(n - 4 * j).min(4)];
        // Two quadwords per block.
        let mask = u8::MAX >> (8 - 2 * h.len());
        // SAFETY: the mask covers `h`; masked-off lanes are not read.
        let h = unsafe { _mm512_maskz_loadu_epi64(mask, h.as_ptr().cast()) };
        lo = _mm512_xor_epi32(lo, _mm512_clmulepi64_epi128(x, h, 0x00));
        mi = _mm512_ternarylogic_epi32(
            mi,
            _mm512_clmulepi64_epi128(x, h, 0x01),
            _mm512_clmulepi64_epi128(x, h, 0x10),
            TERNARY_XOR,
        );
        hi = _mm512_xor_epi32(hi, _mm512_clmulepi64_epi128(x, h, 0x11));
    }

    let gfpoly = _mm512_broadcast_i32x4(GF128_POLY_LO);
    let lo_r = _mm512_clmulepi64_epi128(gfpoly, lo, 0x01);
    let lo_s = _mm512_shuffle_epi32(lo, 0b01_00_11_10);
    let mi = _mm512_ternarylogic_epi32(lo_r, lo_s, mi, TERNARY_XOR);
    let mi_r = _mm512_clmulepi64_epi128(gfpoly, mi, 0x01);
    let mi_s = _mm512_shuffle_epi32(mi, 0b01_00_11_10);
    let r = _mm512_ternarylogic_epi32(mi_r, mi_s, hi, TERNARY_XOR);

    // xor together all terms of `r`
    let a = _mm512_extracti32x4_epi32::<0>(r);
    let b = _mm512_extracti32x4_epi32::<1>(r);
    let c = _mm512_extracti32x4_epi32::<2>(r);
    let d = _mm512_extracti32x4_epi32::<3>(r);
    let ab = _mm_xor_si128(a, b);
    _mm_ternarylogic_epi32(ab, c, d, TERNARY_XOR)
}

#[target_feature(enable = "sse2")]
fn gf128_big_endian(h: __m128i) -> __m128i {
    // takes a raw hash subkey, and arranges that it can
    // be used in big endian ordering.
    let t = _mm_shuffle_epi32(h, 0b11_01_00_11);
    let t = _mm_srai_epi32(t, 31);
    let h = _mm_add_epi64(h, h);
    let t = _mm_and_si128(u128_to_m128i(GF128_POLY_CARRY_MASK), t);
    _mm_xor_si128(h, t)
}

#[target_feature(enable = "sse2")]
fn xor_halves(h: __m128i) -> __m128i {
    let hx = _mm_shuffle_epi32(h, 0b01_00_11_10);
    _mm_xor_si128(hx, h)
}

/// Reverses the bytes of `x`, between GCM's byte order and the polynomial the
/// multiplies take. SSE2 alone, so every table's state can use it.
#[inline]
fn byte_reverse(x: __m128i) -> __m128i {
    // SAFETY: every x86_64 CPU has SSE2
    unsafe {
        let x = _mm_shuffle_epi32(x, 0b00_01_10_11);
        let x = _mm_shufflehi_epi16(_mm_shufflelo_epi16(x, 0b10_11_00_01), 0b10_11_00_01);
        _mm_or_si128(_mm_slli_epi16(x, 8), _mm_srli_epi16(x, 8))
    }
}

#[inline]
fn zero() -> __m128i {
    // SAFETY: every x86_64 CPU has SSE2
    unsafe { _mm_setzero_si128() }
}

/// Loads a block in GCM's byte order as the polynomial the multiplies take.
#[inline]
#[target_feature(enable = "ssse3")]
fn load_be(block: &[u8; 16]) -> __m128i {
    // SAFETY: `block` is 16 readable bytes
    _mm_shuffle_epi8(unsafe { _mm_loadu_si128(block.as_ptr().cast()) }, BYTESWAP)
}

/// Loads `bytes`, fewer than 16, zero-padded to a block in GCM's byte order.
///
/// It builds the block in registers from overlapping loads, branching on the
/// length alone. Copying to a zeroed block instead calls `memcpy`, whose
/// narrow stores then stall the block's 16-byte load, which nearly doubled a
/// short seal's time on Xeons under a partial-block AAD, such as QUIC's.
#[inline]
pub(crate) fn load_partial(bytes: &[u8]) -> __m128i {
    let n = bytes.len();
    assert!(n < 16);
    let le64 = |i: usize| u64::from_le_bytes(bytes[i..i + 8].try_into().unwrap());
    let le32 = |i: usize| u64::from(u32::from_le_bytes(bytes[i..i + 4].try_into().unwrap()));
    let (lo, hi) = match n {
        // The second load ends at the last byte, overlapping the first, and
        // the shift drops what the first already holds.
        9.. => (le64(0), le64(n - 8) >> (8 * (16 - n))),
        4..=8 => (le32(0) | le32(n - 4) << (8 * (n - 4)), 0),
        1..=3 => {
            let byte = |i: usize| u64::from(bytes[i]) << (8 * i);
            (byte(0) | byte(n / 2) | byte(n - 1), 0)
        }
        0 => (0, 0),
    };
    // SAFETY: every x86_64 CPU has SSE2
    unsafe { _mm_set_epi64x(hi as i64, lo as i64) }
}

/// Stores the first `out.len()` bytes, fewer than 16, of `block` in GCM's
/// byte order, without `load_partial`'s `memcpy` either.
#[inline]
pub(crate) fn store_partial(out: &mut [u8], block: __m128i) {
    let n = out.len();
    assert!(n < 16);
    // SAFETY: every x86_64 CPU has SSE2
    let (lo, hi) = unsafe {
        (
            _mm_cvtsi128_si64(block) as u64,
            _mm_cvtsi128_si64(_mm_unpackhi_epi64(block, block)) as u64,
        )
    };
    match n {
        // Overlapping stores, as `load_partial`'s loads: the second ends at
        // the last byte and repeats what the first wrote.
        9.. => {
            out[..8].copy_from_slice(&lo.to_le_bytes());
            let last = lo >> (8 * (n - 8)) | hi << (8 * (16 - n));
            out[n - 8..].copy_from_slice(&last.to_le_bytes());
        }
        4..=8 => {
            out[..4].copy_from_slice(&(lo as u32).to_le_bytes());
            out[n - 4..].copy_from_slice(&((lo >> (8 * (n - 4))) as u32).to_le_bytes());
        }
        1..=3 => {
            out[0] = lo as u8;
            out[n / 2] = (lo >> (8 * (n / 2))) as u8;
            out[n - 1] = (lo >> (8 * (n - 1))) as u8;
        }
        0 => {}
    }
}

/// `v` as a vector, its bits unchanged: computed from its halves, rather than
/// transmuted, so that Aeneas translates it.
#[inline]
pub(super) fn u128_to_m128i(v: u128) -> __m128i {
    // SAFETY: every x86_64 CPU has SSE2
    unsafe { _mm_set_epi64x((v >> 64) as i64, v as i64) }
}

// SAFETY: sizeof(u128) == sizeof(__m128i), all bits have same meaning
const BYTESWAP: __m128i = unsafe { mem::transmute(0x00010203_04050607_08090a0b_0c0d0e0fu128) };

/// Constant for vpternlogd which is three-operand XOR.
///
/// Find `xorABC` in Table 5.2, Intel Volume 2C: Instruction Set Reference, V
/// <https://cdrdv2-public.intel.com/825761/326018-sdm-vol-2c.pdf>
const TERNARY_XOR: i32 = 0x96;

/// The high half of the ghash polynomial R, rotated left by one
///
/// R is 0xe100..00u128
///
/// We need this in a __m128i, but only the bottom 64-bits are used.
const GF128_POLY_HI: u128 = 0xc2000000_00000000;

/// The same as GF128_POLY_HI, but in the top qword.
// SAFETY: sizeof(u128) == sizeof(__m128i), all bits have same meaning
const GF128_POLY_LO: __m128i =
    unsafe { mem::transmute([0xc2000000_00000000_00000000_00000000u128]) };

/// This is, again, R rotated left by one, but with a 2^64 term
const GF128_POLY_CARRY_MASK: u128 = 0xc2000000_00000001_00000000_00000001;

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::generic::ghash as model;

    #[test]
    fn pairwise() {
        check(0, b"");
        check(0, b"hello");
        check(1, b"");
        check(1, b"hello");
        let k = 0x00112233_44556677_8899aabb_ccddeeffu128;
        check(k, b"hello");
        check(k, b"hello world!");
        check(k, &[b'a'; 32]);
        check(k, &[b'b'; 64]);
        check(k, &[b'c'; 512 + 64 + 32 + 16]);

        let mut pattern = [0; 512 + 64 + 32 + 16];
        for (i, p) in pattern.iter_mut().enumerate() {
            *p = i as u8;
        }
        check(k, &pattern);

        let k = 0xffeeeedd_ffeeeedd_ff0000dd_ff0000ddu128;
        for (i, p) in pattern.iter_mut().enumerate() {
            *p = 0xf0 | (i & 0xf) as u8;
        }
        check(k, &pattern);
    }

    // Every length a partial block can have, each byte distinct, and a store
    // that leaves the bytes past its slice alone.
    #[test]
    fn partial_blocks() {
        let bytes: [u8; 16] = core::array::from_fn(|i| 0xa0 + i as u8);
        for n in 0..16 {
            let mut want = [0u8; 16];
            want[..n].copy_from_slice(&bytes[..n]);
            // SAFETY: both are 16 bytes, and any bits are a valid `[u8; 16]`
            let got: [u8; 16] = unsafe { mem::transmute(load_partial(&bytes[..n])) };
            assert_eq!(got, want, "{n}");

            let mut out = [0x55u8; 17];
            store_partial(&mut out[..n], u128_to_m128i(u128::from_le_bytes(bytes)));
            assert_eq!(out[..n], bytes[..n], "{n}");
            assert!(out[n..].iter().all(|&b| b == 0x55), "{n}");
        }
    }

    // Checks the table the CPU picks, and every slower one it can run: the
    // integer and SSSE3 tables, and PCLMULQDQ where the CPU picks VAES.
    fn check(key: u128, input: &[u8]) {
        println!("check: input={input:02x?}");
        let tb = model::GhashTable::new(key);
        let mut b = model::Ghash::new(&tb);
        b.add(input);
        let fb = b.into_bytes();

        let mut tables = vec![
            GhashTable::new(key),
            GhashTable::Nohw(NohwTable::new(&key.to_be_bytes())),
        ];
        if let Some(token) = HaveSsse3::check() {
            tables.push(GhashTable::Ssse3(Ssse3Table::new(
                &key.to_be_bytes(),
                token,
            )));
        }
        if let Some(hw) = HaveAesHardware::check() {
            tables.push(GhashTable::Clmul(ClmulTable::new(key, hw)));
        }
        for ta in &tables {
            let mut a = Ghash::new(ta);
            a.add(input);
            let fa = a.xi();

            if fa != fb {
                panic!("for input: {input:02x?}:\n\n impl  {fa:02x?}\n    !=\nmodel  {fb:02x?}");
            }
        }
    }
}
