// Copyright (c) 2019, Google Inc.
// SPDX-License-Identifier: ISC

//! Bitsliced AES for CPUs without AES instructions: aws-lc's
//! `crypto/fipsmodule/aes/aes_nohw.c` at commit
//! 91c93a8eb860e51482a871a8772cb9b1b310baea, in Rust. It bitslices eight
//! blocks into 128-bit SSE2 words on x86_64 CPUs without SSSE3, and in the
//! portable backend, which armv7 without the crypto extension runs, four
//! blocks into 64-bit words on 64-bit targets and two into 32-bit words
//! otherwise, as aws-lc's configurations do.
//!
//! The S-box is a circuit of ANDs and XORs, so no branch or memory index
//! depends on the key or data. It is not formally verified: its correctness
//! rests on its use and testing in BoringSSL and aws-lc, and on rind's tests
//! of it against FIPS-197, Wycheproof, aws-lc-rs, and each CPU's faster AES.
//! It follows <https://bearssl.org/constanttime.html#aes>,
//! <https://eprint.iacr.org/2009/129.pdf>, and
//! <https://eprint.iacr.org/2009/191.pdf>.
//!
//! Bits and bytes are ordered little-endian, though "left" and "right" shifts
//! match the operations themselves. A word's bits fall in 16 "logical bytes"
//! of `BATCH_SIZE` bits each, which stand for a block's 16 bytes in AES's
//! column-major order. In a bitsliced batch, word `j` holds bit `j` of each
//! block byte, and bit `i` of each logical byte comes from block `i`. With
//! narrower words a block spans several, and aws-lc's "compact" form permutes
//! its bits so that word `k` of a block holds bits `k * BATCH_SIZE` to
//! `(k + 1) * BATCH_SIZE - 1` of each byte: the transpose between compact and
//! bitsliced form then stays within each `BATCH_SIZE` square of bits.

use word::*;

#[cfg(rind_backend = "x86_64")]
mod word {
    use core::arch::x86_64::*;

    pub(super) type Word = __m128i;
    pub(super) const BATCH_SIZE: usize = 8;

    const fn splat(mask: [u32; 4]) -> Word {
        // SAFETY: `__m128i` is 16 bytes, any bits of which are valid.
        unsafe { core::mem::transmute(mask) }
    }

    pub(super) const ZERO: Word = splat([0; 4]);
    pub(super) const ROW0: Word = splat([0x000000ff; 4]);
    pub(super) const ROW1: Word = splat([0x0000ff00; 4]);
    pub(super) const ROW2: Word = splat([0x00ff0000; 4]);
    pub(super) const ROW3: Word = splat([0xff000000; 4]);
    pub(super) const COL01: Word = splat([!0, !0, 0, 0]);
    pub(super) const COL2: Word = splat([0, 0, !0, 0]);
    pub(super) const COL3: Word = splat([0, 0, 0, !0]);

    #[inline(always)]
    pub(super) fn and(a: Word, b: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_and_si128(a, b) }
    }

    #[inline(always)]
    pub(super) fn or(a: Word, b: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_or_si128(a, b) }
    }

    #[inline(always)]
    pub(super) fn xor(a: Word, b: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_xor_si128(a, b) }
    }

    #[inline(always)]
    pub(super) fn not(a: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_xor_si128(a, _mm_set1_epi32(-1)) }
    }

    /// Shifts left by `N` logical bytes.
    #[inline(always)]
    pub(super) fn shift_left<const N: i32>(a: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_slli_si128::<N>(a) }
    }

    /// Shifts right by `N` logical bytes.
    #[inline(always)]
    pub(super) fn shift_right<const N: i32>(a: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_srli_si128::<N>(a) }
    }

    /// Rotates the rows in each column down by one.
    #[inline(always)]
    pub(super) fn rotate_rows_down(v: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { or(_mm_srli_epi32::<8>(v), _mm_slli_epi32::<24>(v)) }
    }

    /// Rotates the rows in each column by two.
    #[inline(always)]
    pub(super) fn rotate_rows_twice(v: Word) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { or(_mm_srli_epi32::<16>(v), _mm_slli_epi32::<16>(v)) }
    }

    /// Swaps the bits in `a & (mask << SHIFT)` with those in `b & mask`,
    /// `mask` repeated in every 32-bit lane. `mask` and `mask << SHIFT` must
    /// not overlap.
    #[inline(always)]
    pub(super) fn swap_bits<const SHIFT: i32>(a: Word, b: Word, mask: u32) -> (Word, Word) {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe {
            let swap = and(
                xor(_mm_srli_epi32::<SHIFT>(a), b),
                _mm_set1_epi32(mask as i32),
            );
            (xor(a, _mm_slli_epi32::<SHIFT>(swap)), xor(b, swap))
        }
    }

    /// The `i`th group of `BATCH_SIZE` bits of `rcon`: with 128-bit words,
    /// all of it, in the first logical byte.
    #[inline(always)]
    pub(super) fn rcon_slice(rcon: u8, _i: usize) -> Word {
        // SAFETY: every x86_64 CPU has SSE2.
        unsafe { _mm_set_epi32(0, 0, 0, rcon.into()) }
    }

    /// A block in compact form, which with 128-bit words is its bytes.
    #[inline(always)]
    pub(super) fn compact_block(input: &[u8; 16]) -> [Word; 1] {
        // SAFETY: `input` is 16 readable bytes, and every x86_64 CPU has
        // SSE2.
        [unsafe { _mm_loadu_si128(input.as_ptr().cast()) }]
    }

    #[inline(always)]
    pub(super) fn uncompact_block(out: &mut [u8; 16], input: &[Word; 1]) {
        // SAFETY: `out` is 16 writable bytes, and every x86_64 CPU has SSE2.
        unsafe { _mm_storeu_si128(out.as_mut_ptr().cast(), input[0]) }
    }
}

/// Plain integer words, whose operations are Rust's own; the masks and
/// shifts then differ by width.
#[cfg(not(rind_backend = "x86_64"))]
macro_rules! integer_word_ops {
    () => {
        pub(super) const ZERO: Word = 0;

        #[inline(always)]
        pub(super) fn and(a: Word, b: Word) -> Word {
            a & b
        }

        #[inline(always)]
        pub(super) fn or(a: Word, b: Word) -> Word {
            a | b
        }

        #[inline(always)]
        pub(super) fn xor(a: Word, b: Word) -> Word {
            a ^ b
        }

        #[inline(always)]
        pub(super) fn not(a: Word) -> Word {
            !a
        }

        /// Shifts left by `N` logical bytes.
        #[inline(always)]
        pub(super) fn shift_left<const N: i32>(a: Word) -> Word {
            a << (N as usize * BATCH_SIZE)
        }

        /// Shifts right by `N` logical bytes.
        #[inline(always)]
        pub(super) fn shift_right<const N: i32>(a: Word) -> Word {
            a >> (N as usize * BATCH_SIZE)
        }

        /// Swaps the bits in `a & (mask << SHIFT)` with those in `b & mask`,
        /// `mask` repeated to the word's width. `mask` and `mask << SHIFT`
        /// must not overlap.
        #[inline(always)]
        pub(super) fn swap_bits<const SHIFT: i32>(a: Word, b: Word, mask: u32) -> (Word, Word) {
            let mask = Word::from(mask) * (Word::MAX / Word::from(u32::MAX));
            let swap = ((a >> SHIFT) ^ b) & mask;
            (a ^ (swap << SHIFT), b ^ swap)
        }

        /// The `i`th group of `BATCH_SIZE` bits of `rcon`.
        #[inline(always)]
        pub(super) fn rcon_slice(rcon: u8, i: usize) -> Word {
            Word::from((rcon >> (i * BATCH_SIZE)) & ((1 << BATCH_SIZE) - 1))
        }

        /// Returns `a` with the bits in `a & mask` and `a & (mask << shift)`
        /// swapped, which must not overlap. See
        /// <https://reflectionsonsecurity.wordpress.com/2014/05/11/efficient-bit-permutation-using-delta-swaps/>.
        #[inline(always)]
        fn delta_swap(a: Word, mask: Word, shift: u32) -> Word {
            let b = (a ^ (a >> shift)) & mask;
            a ^ b ^ (b << shift)
        }
    };
}

#[cfg(all(not(rind_backend = "x86_64"), target_pointer_width = "64"))]
mod word {
    pub(super) type Word = u64;
    pub(super) const BATCH_SIZE: usize = 4;

    pub(super) const ROW0: Word = 0x000f000f000f000f;
    pub(super) const ROW1: Word = 0x00f000f000f000f0;
    pub(super) const ROW2: Word = 0x0f000f000f000f00;
    pub(super) const ROW3: Word = 0xf000f000f000f000;
    pub(super) const COL01: Word = 0x00000000ffffffff;
    pub(super) const COL2: Word = 0x0000ffff00000000;
    pub(super) const COL3: Word = 0xffff000000000000;

    integer_word_ops!();

    #[inline(always)]
    pub(super) fn rotate_rows_down(v: Word) -> Word {
        ((v >> 4) & 0x0fff0fff0fff0fff) | ((v << 12) & 0xf000f000f000f000)
    }

    #[inline(always)]
    pub(super) fn rotate_rows_twice(v: Word) -> Word {
        ((v >> 8) & 0x00ff00ff00ff00ff) | ((v << 8) & 0xff00ff00ff00ff00)
    }

    /// Permutes the 16 nibbles of `a`, least significant first, from
    /// `0 1 2 3 | 4 5 6 7 | 8 9 10 11 | 12 13 14 15` to
    /// `0 2 4 6 | 8 10 12 14 | 1 3 5 7 | 9 11 13 15`.
    #[inline(always)]
    fn compact_word(a: Word) -> Word {
        let a = delta_swap(a, 0x00f000f000f000f0, 4);
        let a = delta_swap(a, 0x0000ff000000ff00, 8);
        delta_swap(a, 0x00000000ffff0000, 16)
    }

    #[inline(always)]
    fn uncompact_word(a: Word) -> Word {
        let a = delta_swap(a, 0x00000000ffff0000, 16);
        let a = delta_swap(a, 0x0000ff000000ff00, 8);
        delta_swap(a, 0x00f000f000f000f0, 4)
    }

    #[inline(always)]
    pub(super) fn compact_block(input: &[u8; 16]) -> [Word; 2] {
        let (lo, hi) = input.split_at(8);
        let a0 = compact_word(Word::from_le_bytes(lo.try_into().unwrap()));
        let a1 = compact_word(Word::from_le_bytes(hi.try_into().unwrap()));
        [
            (a0 & 0x00000000ffffffff) | (a1 << 32),
            (a1 & 0xffffffff00000000) | (a0 >> 32),
        ]
    }

    #[inline(always)]
    pub(super) fn uncompact_block(out: &mut [u8; 16], input: &[Word; 2]) {
        let [a0, a1] = *input;
        let b0 = uncompact_word((a0 & 0x00000000ffffffff) | (a1 << 32));
        let b1 = uncompact_word((a1 & 0xffffffff00000000) | (a0 >> 32));
        out[..8].copy_from_slice(&b0.to_le_bytes());
        out[8..].copy_from_slice(&b1.to_le_bytes());
    }
}

#[cfg(all(not(rind_backend = "x86_64"), not(target_pointer_width = "64")))]
mod word {
    pub(super) type Word = u32;
    pub(super) const BATCH_SIZE: usize = 2;

    pub(super) const ROW0: Word = 0x03030303;
    pub(super) const ROW1: Word = 0x0c0c0c0c;
    pub(super) const ROW2: Word = 0x30303030;
    pub(super) const ROW3: Word = 0xc0c0c0c0;
    pub(super) const COL01: Word = 0x0000ffff;
    pub(super) const COL2: Word = 0x00ff0000;
    pub(super) const COL3: Word = 0xff000000;

    integer_word_ops!();

    #[inline(always)]
    pub(super) fn rotate_rows_down(v: Word) -> Word {
        ((v >> 2) & 0x3f3f3f3f) | ((v << 6) & 0xc0c0c0c0)
    }

    #[inline(always)]
    pub(super) fn rotate_rows_twice(v: Word) -> Word {
        ((v >> 4) & 0x0f0f0f0f) | ((v << 4) & 0xf0f0f0f0)
    }

    /// Permutes the 16 bit pairs of `a`, least significant first, from
    /// `0 1 2 3 | 4 5 6 7 | 8 9 10 11 | 12 13 14 15` to
    /// `0 4 8 12 | 1 5 9 13 | 2 6 10 14 | 3 7 11 15`.
    #[inline(always)]
    fn compact_word(a: Word) -> Word {
        let a = delta_swap(a, 0x00cc00cc, 6);
        delta_swap(a, 0x0000f0f0, 12)
    }

    #[inline(always)]
    fn uncompact_word(a: Word) -> Word {
        let a = delta_swap(a, 0x0000f0f0, 12);
        delta_swap(a, 0x00cc00cc, 6)
    }

    /// Byte `k` of each of `a`, as a word.
    #[inline(always)]
    fn byte_column(a: &[Word; 4], k: usize) -> Word {
        Word::from_le_bytes(a.map(|a| (a >> (8 * k)) as u8))
    }

    #[inline(always)]
    pub(super) fn compact_block(input: &[u8; 16]) -> [Word; 4] {
        let words = input.as_chunks::<4>().0;
        let a = core::array::from_fn(|k| compact_word(Word::from_le_bytes(words[k])));
        core::array::from_fn(|k| byte_column(&a, k))
    }

    #[inline(always)]
    pub(super) fn uncompact_block(out: &mut [u8; 16], input: &[Word; 4]) {
        for (k, bytes) in out.as_chunks_mut::<4>().0.iter_mut().enumerate() {
            *bytes = uncompact_word(byte_column(input, k)).to_le_bytes();
        }
    }
}

/// Words per block.
const BLOCK_WORDS: usize = 16 / size_of::<Word>();

/// A block in compact form.
type Compact = [Word; BLOCK_WORDS];

/// `BATCH_SIZE` blocks, bitsliced unless said otherwise: aws-lc's
/// `AES_NOHW_BATCH`.
#[derive(Clone, Copy)]
struct Batch {
    w: [Word; 8],
}

const EMPTY: Batch = Batch { w: [ZERO; 8] };

// Block representations.

impl Batch {
    /// Sets block `i` of a compact batch. A block's words go `BATCH_SIZE`
    /// apart, which puts the bits along the diagonals of each `BATCH_SIZE`
    /// square where the transpose expects them.
    #[inline(always)]
    fn set(&mut self, block: &Compact, i: usize) {
        for (k, w) in block.iter().enumerate() {
            self.w[i + k * BATCH_SIZE] = *w;
        }
    }

    /// Block `i` of a compact batch.
    #[inline(always)]
    fn get(&self, i: usize) -> Compact {
        core::array::from_fn(|k| self.w[i + k * BATCH_SIZE])
    }
}

/// Converts `batch` to and from bitsliced form, transposing each `BATCH_SIZE`
/// by `BATCH_SIZE` square of bits.
#[inline(always)]
fn transpose(batch: &mut Batch) {
    let w = &mut batch.w;
    // Swap bits with index 0 and 1 mod 2 (0x55 = 0b01010101).
    (w[0], w[1]) = swap_bits::<1>(w[0], w[1], 0x55555555);
    (w[2], w[3]) = swap_bits::<1>(w[2], w[3], 0x55555555);
    (w[4], w[5]) = swap_bits::<1>(w[4], w[5], 0x55555555);
    (w[6], w[7]) = swap_bits::<1>(w[6], w[7], 0x55555555);

    if BATCH_SIZE >= 4 {
        // Swap bits with index 0-1 and 2-3 mod 4 (0x33 = 0b00110011).
        (w[0], w[2]) = swap_bits::<2>(w[0], w[2], 0x33333333);
        (w[1], w[3]) = swap_bits::<2>(w[1], w[3], 0x33333333);
        (w[4], w[6]) = swap_bits::<2>(w[4], w[6], 0x33333333);
        (w[5], w[7]) = swap_bits::<2>(w[5], w[7], 0x33333333);
    }

    if BATCH_SIZE >= 8 {
        // Swap bits with index 0-3 and 4-7 mod 8 (0x0f = 0b00001111).
        (w[0], w[4]) = swap_bits::<4>(w[0], w[4], 0x0f0f0f0f);
        (w[1], w[5]) = swap_bits::<4>(w[1], w[5], 0x0f0f0f0f);
        (w[2], w[6]) = swap_bits::<4>(w[2], w[6], 0x0f0f0f0f);
        (w[3], w[7]) = swap_bits::<4>(w[3], w[7], 0x0f0f0f0f);
    }
}

/// Bitslices up to `BATCH_SIZE` blocks, leaving the rest zero.
#[inline(always)]
fn to_batch(input: &[[u8; 16]]) -> Batch {
    assert!(input.len() <= BATCH_SIZE);
    let mut out = EMPTY;
    for (i, block) in input.iter().enumerate() {
        out.set(&compact_block(block), i);
    }
    transpose(&mut out);
    out
}

/// Writes the first `out.len()` blocks of `batch`.
#[inline(always)]
fn from_batch(out: &mut [[u8; 16]], batch: &Batch) {
    assert!(out.len() <= BATCH_SIZE);
    let mut copy = *batch;
    transpose(&mut copy);
    for (i, block) in out.iter_mut().enumerate() {
        uncompact_block(block, &copy.get(i));
    }
}

// AES round steps.

#[inline(always)]
fn add_round_key(batch: &mut Batch, key: &Batch) {
    for (w, k) in batch.w.iter_mut().zip(key.w) {
        *w = xor(*w, k);
    }
}

#[inline(always)]
fn sub_bytes(batch: &mut Batch) {
    // See https://eprint.iacr.org/2009/191.pdf, Appendix C.
    let x0 = batch.w[7];
    let x1 = batch.w[6];
    let x2 = batch.w[5];
    let x3 = batch.w[4];
    let x4 = batch.w[3];
    let x5 = batch.w[2];
    let x6 = batch.w[1];
    let x7 = batch.w[0];

    // Figure 2, the top linear transformation.
    let y14 = xor(x3, x5);
    let y13 = xor(x0, x6);
    let y9 = xor(x0, x3);
    let y8 = xor(x0, x5);
    let t0 = xor(x1, x2);
    let y1 = xor(t0, x7);
    let y4 = xor(y1, x3);
    let y12 = xor(y13, y14);
    let y2 = xor(y1, x0);
    let y5 = xor(y1, x6);
    let y3 = xor(y5, y8);
    let t1 = xor(x4, y12);
    let y15 = xor(t1, x5);
    let y20 = xor(t1, x1);
    let y6 = xor(y15, x7);
    let y10 = xor(y15, t0);
    let y11 = xor(y20, y9);
    let y7 = xor(x7, y11);
    let y17 = xor(y10, y11);
    let y19 = xor(y10, y8);
    let y16 = xor(t0, y11);
    let y21 = xor(y13, y16);
    let y18 = xor(x0, y16);

    // Figure 3, the middle non-linear section.
    let t2 = and(y12, y15);
    let t3 = and(y3, y6);
    let t4 = xor(t3, t2);
    let t5 = and(y4, x7);
    let t6 = xor(t5, t2);
    let t7 = and(y13, y16);
    let t8 = and(y5, y1);
    let t9 = xor(t8, t7);
    let t10 = and(y2, y7);
    let t11 = xor(t10, t7);
    let t12 = and(y9, y11);
    let t13 = and(y14, y17);
    let t14 = xor(t13, t12);
    let t15 = and(y8, y10);
    let t16 = xor(t15, t12);
    let t17 = xor(t4, t14);
    let t18 = xor(t6, t16);
    let t19 = xor(t9, t14);
    let t20 = xor(t11, t16);
    let t21 = xor(t17, y20);
    let t22 = xor(t18, y19);
    let t23 = xor(t19, y21);
    let t24 = xor(t20, y18);
    let t25 = xor(t21, t22);
    let t26 = and(t21, t23);
    let t27 = xor(t24, t26);
    let t28 = and(t25, t27);
    let t29 = xor(t28, t22);
    let t30 = xor(t23, t24);
    let t31 = xor(t22, t26);
    let t32 = and(t31, t30);
    let t33 = xor(t32, t24);
    let t34 = xor(t23, t33);
    let t35 = xor(t27, t33);
    let t36 = and(t24, t35);
    let t37 = xor(t36, t34);
    let t38 = xor(t27, t36);
    let t39 = and(t29, t38);
    let t40 = xor(t25, t39);
    let t41 = xor(t40, t37);
    let t42 = xor(t29, t33);
    let t43 = xor(t29, t40);
    let t44 = xor(t33, t37);
    let t45 = xor(t42, t41);
    let z0 = and(t44, y15);
    let z1 = and(t37, y6);
    let z2 = and(t33, x7);
    let z3 = and(t43, y16);
    let z4 = and(t40, y1);
    let z5 = and(t29, y7);
    let z6 = and(t42, y11);
    let z7 = and(t45, y17);
    let z8 = and(t41, y10);
    let z9 = and(t44, y12);
    let z10 = and(t37, y3);
    let z11 = and(t33, y4);
    let z12 = and(t43, y13);
    let z13 = and(t40, y5);
    let z14 = and(t29, y2);
    let z15 = and(t42, y9);
    let z16 = and(t45, y14);
    let z17 = and(t41, y8);

    // Figure 4, bottom linear transformation.
    let t46 = xor(z15, z16);
    let t47 = xor(z10, z11);
    let t48 = xor(z5, z13);
    let t49 = xor(z9, z10);
    let t50 = xor(z2, z12);
    let t51 = xor(z2, z5);
    let t52 = xor(z7, z8);
    let t53 = xor(z0, z3);
    let t54 = xor(z6, z7);
    let t55 = xor(z16, z17);
    let t56 = xor(z12, t48);
    let t57 = xor(t50, t53);
    let t58 = xor(z4, t46);
    let t59 = xor(z3, t54);
    let t60 = xor(t46, t57);
    let t61 = xor(z14, t57);
    let t62 = xor(t52, t58);
    let t63 = xor(t49, t58);
    let t64 = xor(z4, t59);
    let t65 = xor(t61, t62);
    let t66 = xor(z1, t63);
    let s0 = xor(t59, t63);
    let s6 = xor(t56, not(t62));
    let s7 = xor(t48, not(t60));
    let t67 = xor(t64, t65);
    let s3 = xor(t53, t66);
    let s4 = xor(t51, t66);
    let s5 = xor(t47, t65);
    let s1 = xor(t64, not(s3));
    let s2 = xor(t55, not(t67));

    batch.w = [s7, s6, s5, s4, s3, s2, s1, s0];
}

/// Inverts the affine transform of the S-box, FIPS 197 section 5.1.1 step 2.
#[inline(always)]
fn sub_bytes_inv_affine(batch: &mut Batch) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = batch.w;

    // Apply the circulant [0 0 1 0 0 1 0 1], the inverse of the circulant
    // [1 0 0 0 1 1 1 1].
    let b0 = xor(a2, xor(a5, a7));
    let b1 = xor(a3, xor(a6, a0));
    let b2 = xor(a4, xor(a7, a1));
    let b3 = xor(a5, xor(a0, a2));
    let b4 = xor(a6, xor(a1, a3));
    let b5 = xor(a7, xor(a2, a4));
    let b6 = xor(a0, xor(a3, a5));
    let b7 = xor(a1, xor(a4, a6));

    // XOR 0x05, the circulant applied to 0x63, which has lower Hamming
    // weight than XORing 0x63 before it.
    batch.w = [not(b0), b1, not(b2), b3, b4, b5, b6, b7];
}

/// The inverse S-box from the forward one, as
/// <https://www.bearssl.org/constanttime.html#aes> describes: the S-box is
/// `S(x) = A(Inv(x))`, so `InvS(x) = Inv(InvA(x)) = InvA(S(InvA(x)))`.
#[inline(always)]
fn inv_sub_bytes(batch: &mut Batch) {
    sub_bytes_inv_affine(batch);
    sub_bytes(batch);
    sub_bytes_inv_affine(batch);
}

#[inline(always)]
fn shift_rows(batch: &mut Batch) {
    for w in &mut batch.w {
        let row0 = and(*w, ROW0);
        let row1 = and(*w, ROW1);
        let row2 = and(*w, ROW2);
        let row3 = and(*w, ROW3);
        // Rotate the columns in row `r` right by `r`.
        let row1 = or(shift_right::<4>(row1), shift_left::<12>(row1));
        let row2 = or(shift_right::<8>(row2), shift_left::<8>(row2));
        let row3 = or(shift_right::<12>(row3), shift_left::<4>(row3));
        *w = or(or(row0, row1), or(row2, row3));
    }
}

#[inline(always)]
fn inv_shift_rows(batch: &mut Batch) {
    for w in &mut batch.w {
        let row0 = and(*w, ROW0);
        let row1 = and(*w, ROW1);
        let row2 = and(*w, ROW2);
        let row3 = and(*w, ROW3);
        // Rotate the columns in row `r` right by `4 - r`.
        let row1 = or(shift_right::<12>(row1), shift_left::<4>(row1));
        let row2 = or(shift_right::<8>(row2), shift_left::<8>(row2));
        let row3 = or(shift_right::<4>(row3), shift_left::<12>(row3));
        *w = or(or(row0, row1), or(row2, row3));
    }
}

#[inline(always)]
fn mix_columns(batch: &mut Batch) {
    // See https://eprint.iacr.org/2009/129.pdf, section 4.4 and appendix A.
    let [a0, a1, a2, a3, a4, a5, a6, a7] = batch.w;

    let r0 = rotate_rows_down(a0);
    let a0_r0 = xor(a0, r0);
    let r1 = rotate_rows_down(a1);
    let a1_r1 = xor(a1, r1);
    let r2 = rotate_rows_down(a2);
    let a2_r2 = xor(a2, r2);
    let r3 = rotate_rows_down(a3);
    let a3_r3 = xor(a3, r3);
    let r4 = rotate_rows_down(a4);
    let a4_r4 = xor(a4, r4);
    let r5 = rotate_rows_down(a5);
    let a5_r5 = xor(a5, r5);
    let r6 = rotate_rows_down(a6);
    let a6_r6 = xor(a6, r6);
    let r7 = rotate_rows_down(a7);
    let a7_r7 = xor(a7, r7);

    batch.w = [
        xor(xor(a7_r7, r0), rotate_rows_twice(a0_r0)),
        xor(xor(a0_r0, a7_r7), xor(r1, rotate_rows_twice(a1_r1))),
        xor(xor(a1_r1, r2), rotate_rows_twice(a2_r2)),
        xor(xor(a2_r2, a7_r7), xor(r3, rotate_rows_twice(a3_r3))),
        xor(xor(a3_r3, a7_r7), xor(r4, rotate_rows_twice(a4_r4))),
        xor(xor(a4_r4, r5), rotate_rows_twice(a5_r5)),
        xor(xor(a5_r5, r6), rotate_rows_twice(a6_r6)),
        xor(xor(a6_r6, r7), rotate_rows_twice(a7_r7)),
    ];
}

/// InvMixColumns, by bsaes-x86_64's decomposition, credited to Jussi
/// Kivilinna, into a [05 00 04 00] step and then MixColumns:
///
/// ```text
/// | 0e 0b 0d 09 |   | 02 03 01 01 |   | 05 00 04 00 |
/// | 09 0e 0b 0d | = | 01 02 03 01 | x | 00 05 00 04 |
/// | 0d 09 0e 0b |   | 01 01 02 03 |   | 04 00 05 00 |
/// | 0b 0d 09 0e |   | 03 01 01 02 |   | 00 04 00 05 |
/// ```
#[inline(always)]
fn inv_mix_columns(batch: &mut Batch) {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = batch.w;

    // Each byte becomes 05·a_ij ⊕ 04·a_i(j+2) = 04·(a_ij ⊕ a_i(j+2)) ⊕ a_ij,
    // where a_i(j+2) is a rotation of the rows by two, and multiplying by
    // 04 maps bits (b0..b7) to (a6, a6^a7, a0^a7, a1^a6, a2^a6^a7, a3^a7,
    // a4, a5).
    let a0_r0 = xor(a0, rotate_rows_twice(a0));
    let a1_r1 = xor(a1, rotate_rows_twice(a1));
    let a2_r2 = xor(a2, rotate_rows_twice(a2));
    let a3_r3 = xor(a3, rotate_rows_twice(a3));
    let a4_r4 = xor(a4, rotate_rows_twice(a4));
    let a5_r5 = xor(a5, rotate_rows_twice(a5));
    let a6_r6 = xor(a6, rotate_rows_twice(a6));
    let a7_r7 = xor(a7, rotate_rows_twice(a7));

    batch.w = [
        xor(a0, a6_r6),
        xor(a1, xor(a6_r6, a7_r7)),
        xor(a2, xor(a0_r0, a7_r7)),
        xor(a3, xor(a1_r1, a6_r6)),
        xor(xor(a4, a2_r2), xor(a6_r6, a7_r7)),
        xor(a5, xor(a3_r3, a7_r7)),
        xor(a6, a4_r4),
        xor(a7, a5_r5),
    ];

    mix_columns(batch);
}

// Key schedule.

const RCON: [u8; 10] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36];

/// Applies the S-box to each byte of a compact block.
#[inline(always)]
fn sub_block(input: &Compact) -> Compact {
    let mut batch = EMPTY;
    batch.set(input, 0);
    transpose(&mut batch);
    sub_bytes(&mut batch);
    transpose(&mut batch);
    batch.get(0)
}

/// XORs each word of `v` into the words after it, as each round key word
/// is the previous one XORed with the word a key length back. This is
/// reordered from the usual formulation to need no masks.
#[inline(always)]
fn propagate(v: Word) -> Word {
    xor(
        xor(v, shift_left::<4>(v)),
        xor(shift_left::<8>(v), shift_left::<12>(v)),
    )
}

fn setup_key_128(rd_key: &mut [Compact; 15], input: &[u8; 16]) {
    let mut block = compact_block(input);
    rd_key[0] = block;

    for i in 1..=10 {
        let sub = sub_block(&block);
        for (j, (b, s)) in block.iter_mut().zip(sub).enumerate() {
            // Incorporate `rcon` and the transformed word into the first word.
            let w = xor(*b, rcon_slice(RCON[i - 1], j));
            let w = xor(w, shift_right::<12>(rotate_rows_down(s)));
            *b = propagate(w);
        }
        rd_key[i] = block;
    }
}

fn setup_key_192(rd_key: &mut [Compact; 15], input: &[u8; 24]) {
    // Each key schedule iteration produces six words, but each block holds
    // four, so this keeps a sliding window of two blocks, filled to 1.5
    // blocks at a time, and loops every three blocks or two iterations. On
    // entry to the loop, `block1` and the first half of `block2` hold the
    // previous iteration; `block1` is written to `rd_key`, but `block2`,
    // incomplete, is not.
    let (lo, hi) = input.split_at(16);
    let mut block1 = compact_block(lo.try_into().unwrap());
    rd_key[0] = block1;
    let mut half_block = [0u8; 16];
    half_block[..8].copy_from_slice(hi);
    let mut block2 = compact_block(&half_block);

    for i in 0..4 {
        let sub = sub_block(&block2);
        for j in 0..BLOCK_WORDS {
            let (b1, b2) = (&mut block1[j], &mut block2[j]);
            // The first two words of the next iteration, which go in the
            // second half of `block2`, from the first two of the previous,
            // in the first half of `block1`. `rcon` goes in here too, since
            // the shifts match.
            *b2 = or(*b2, shift_left::<8>(xor(*b1, rcon_slice(RCON[2 * i], j))));
            // Incorporate the transformed word and propagate. The previous
            // iteration's last word is the second word of `sub`, which goes
            // into the next iteration's first, the third word of `block2`.
            *b2 = xor(*b2, and(shift_left::<4>(rotate_rows_down(sub[j])), COL2));
            *b2 = xor(*b2, and(shift_left::<4>(*b2), COL3));

            // The remaining four words, which fill `block1`, from the
            // previous iteration's words in the second half of `block1` and
            // the first half of `block2`.
            *b1 = or(shift_right::<8>(*b1), shift_left::<8>(*b2));
            // Incorporate the second word, computed above in `block2`, and
            // propagate.
            *b1 = propagate(xor(*b1, shift_right::<12>(*b2)));
        }

        // Two round keys are done, `block2`'s half of them from the
        // previous iteration.
        rd_key[3 * i + 1] = block2;
        rd_key[3 * i + 2] = block1;

        let sub = sub_block(&block1);
        for j in 0..BLOCK_WORDS {
            let (b1, b2) = (&mut block1[j], &mut block2[j]);
            // The first four words of the next iteration in `block2`, from
            // the previous iteration's in the second half of `block2` and the
            // first half of `block1`.
            *b2 = or(shift_right::<8>(*b2), shift_left::<8>(*b1));
            // Incorporate `rcon` and the transformed word, from the previous
            // iteration's last word, the last word of `sub`, and propagate.
            *b2 = xor(*b2, rcon_slice(RCON[2 * i + 1], j));
            *b2 = propagate(xor(*b2, shift_right::<12>(rotate_rows_down(sub[j]))));

            // The last two words, in the first half of `block1`, from the
            // previous iteration's last two, in its second half. Propagate,
            // then mask off the excess.
            *b1 = shift_right::<8>(*b1);
            *b1 = xor(*b1, shift_right::<12>(*b2));
            *b1 = xor(*b1, shift_left::<4>(*b1));
            *b1 = and(*b1, COL01);
        }

        // `block2` is a whole round key; `block1` completes in the next
        // iteration.
        rd_key[3 * i + 3] = block2;

        // Swap the blocks to restore the invariant.
        (block1, block2) = (block2, block1);
    }
}

fn setup_key_256(rd_key: &mut [Compact; 15], input: &[u8; 32]) {
    // Each key schedule iteration produces two round keys.
    let (lo, hi) = input.split_at(16);
    let mut block1 = compact_block(lo.try_into().unwrap());
    rd_key[0] = block1;
    let mut block2 = compact_block(hi.try_into().unwrap());
    rd_key[1] = block2;

    for i in (2..=14).step_by(2) {
        let sub = sub_block(&block2);
        for (j, (b, s)) in block1.iter_mut().zip(sub).enumerate() {
            // Incorporate `rcon` and the transformed word into the first word.
            let w = xor(*b, rcon_slice(RCON[i / 2 - 1], j));
            *b = propagate(xor(w, shift_right::<12>(rotate_rows_down(s))));
        }
        rd_key[i] = block1;

        if i == 14 {
            break;
        }

        let sub = sub_block(&block1);
        for (b, s) in block2.iter_mut().zip(sub) {
            // Incorporate the transformed word into the first word.
            *b = propagate(xor(*b, shift_right::<12>(s)));
        }
        rd_key[i + 1] = block2;
    }
}

/// An expanded AES-128, AES-192, or AES-256 key: aws-lc's `AES_KEY`, the
/// compact round keys and the round count, which encryption and decryption
/// share. [`Self::schedule`] bitslices it for use.
pub(crate) struct NohwKey {
    rd_key: [Compact; 15],
    rounds: usize,
}

impl NohwKey {
    /// Expands a 16-, 24-, or 32-byte key.
    pub(crate) fn new(key: &[u8]) -> Self {
        let mut rd_key = [[ZERO; BLOCK_WORDS]; 15];
        let rounds = match key.len() {
            16 => {
                setup_key_128(&mut rd_key, key.try_into().unwrap());
                10
            }
            24 => {
                setup_key_192(&mut rd_key, key.try_into().unwrap());
                12
            }
            32 => {
                setup_key_256(&mut rd_key, key.try_into().unwrap());
                14
            }
            _ => unreachable!("callers check the AES key length"),
        };
        Self { rd_key, rounds }
    }

    /// The key's length in bytes, from its 10, 12, or 14 rounds.
    #[cfg(rind_backend = "x86_64")]
    pub(crate) fn key_len(&self) -> usize {
        self.rounds * 4 - 24
    }

    /// The bitsliced round keys, aws-lc's `AES_NOHW_SCHEDULE`: `BATCH_SIZE`
    /// copies of each.
    pub(crate) fn schedule(&self) -> Schedule {
        let mut keys = [EMPTY; 15];
        for (out, round_key) in keys.iter_mut().zip(&self.rd_key[..=self.rounds]) {
            for i in 0..BATCH_SIZE {
                out.set(round_key, i);
            }
            transpose(out);
        }
        Schedule {
            keys,
            rounds: self.rounds,
        }
    }
}

/// x86_64's AES for CPUs without SSSE3 bitslices the round keys again each
/// call, as aws-lc does: holding them bitsliced would take 1.9 KiB, which
/// every `AesKey` would then occupy, on every CPU.
#[cfg(rind_backend = "x86_64")]
impl NohwKey {
    /// Encrypts one block.
    ///
    /// Out of line: the bitsliced round keys take a 1.9 KiB frame, which
    /// would otherwise land on every caller of `AesKey`'s.
    #[must_use]
    #[inline(never)]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        self.schedule().encrypt_block(block)
    }

    /// Decrypts one block in place.
    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        self.schedule().decrypt_block(inout)
    }

    /// XORs counter-mode keystream into whole blocks, as [`Schedule::ctr32`].
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [[u8; 16]]) {
        if !inout.is_empty() {
            self.schedule().ctr32(ivec, inout.as_flattened_mut());
        }
    }

    /// Encrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_encrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        if !blocks.is_empty() {
            self.schedule().cbc_encrypt(iv, blocks);
        }
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        if !blocks.is_empty() {
            self.schedule().cbc_decrypt(iv, blocks);
        }
    }
}

impl Drop for NohwKey {
    fn drop(&mut self) {
        crate::low::zeroise_value(self);
    }
}

impl crate::low::Zeroable for NohwKey {}

/// Bitsliced round keys, which encrypt and decrypt `BATCH_SIZE` blocks a
/// pass. It does not wipe itself: the key types that hold one do.
pub(crate) struct Schedule {
    keys: [Batch; 15],
    rounds: usize,
}

impl crate::low::Zeroable for Schedule {}

impl Schedule {
    /// The key's length in bytes, from its 10, 12, or 14 rounds.
    #[cfg(any(not(rind_backend = "x86_64"), test))]
    pub(crate) fn key_len(&self) -> usize {
        self.rounds * 4 - 24
    }

    #[inline(always)]
    fn encrypt_batch(&self, batch: &mut Batch) {
        let keys = &self.keys[..=self.rounds];
        let (first, rest) = keys.split_first().unwrap();
        let (last, middle) = rest.split_last().unwrap();
        add_round_key(batch, first);
        for round_key in middle {
            sub_bytes(batch);
            shift_rows(batch);
            mix_columns(batch);
            add_round_key(batch, round_key);
        }
        sub_bytes(batch);
        shift_rows(batch);
        add_round_key(batch, last);
    }

    #[inline(always)]
    fn decrypt_batch(&self, batch: &mut Batch) {
        let keys = &self.keys[..=self.rounds];
        let (first, rest) = keys.split_first().unwrap();
        let (last, middle) = rest.split_last().unwrap();
        add_round_key(batch, last);
        inv_shift_rows(batch);
        inv_sub_bytes(batch);
        for round_key in middle.iter().rev() {
            add_round_key(batch, round_key);
            inv_mix_columns(batch);
            inv_shift_rows(batch);
            inv_sub_bytes(batch);
        }
        add_round_key(batch, first);
    }

    /// Encrypts one block.
    #[must_use]
    pub(crate) fn encrypt_block(&self, block: &[u8; 16]) -> [u8; 16] {
        let mut out = [*block];
        let mut batch = to_batch(&out);
        self.encrypt_batch(&mut batch);
        from_batch(&mut out, &batch);
        out[0]
    }

    /// Decrypts one block in place.
    ///
    /// Inlined on the portable backend, with [`Self::cbc_decrypt`]. A 32-bit
    /// build otherwise outlines both, and the extra call is the decrypt
    /// regression.
    #[cfg_attr(rind_backend = "portable", inline)]
    pub(crate) fn decrypt_block(&self, inout: &mut [u8; 16]) {
        let inout = core::slice::from_mut(inout);
        let mut batch = to_batch(inout);
        self.decrypt_batch(&mut batch);
        from_batch(inout, &batch);
    }

    /// XORs counter-mode keystream into `inout`, whose last block may be
    /// partial.
    ///
    /// The counter blocks are `ivec`, then `ivec` with its last four bytes,
    /// a big-endian counter, incremented with 32-bit wrapping.
    pub(crate) fn ctr32(&self, ivec: &[u8; 16], inout: &mut [u8]) {
        let mut ivs = [*ivec; BATCH_SIZE];
        let mut enc_ivs = [[0u8; 16]; BATCH_SIZE];

        let mut ctr = u32::from_be_bytes(ivec[12..].try_into().unwrap());
        for chunk in inout.chunks_mut(16 * BATCH_SIZE) {
            for (i, iv) in (0..).zip(&mut ivs) {
                iv[12..].copy_from_slice(&ctr.wrapping_add(i).to_be_bytes());
            }

            let todo = chunk.len().div_ceil(16);
            let mut batch = to_batch(&ivs[..todo]);
            self.encrypt_batch(&mut batch);
            from_batch(&mut enc_ivs[..todo], &batch);

            for (b, e) in chunk.iter_mut().zip(enc_ivs.as_flattened()) {
                *b ^= e;
            }

            ctr = ctr.wrapping_add(BATCH_SIZE as u32);
        }
    }

    /// Encrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`. CBC encryption is serial, so each block takes a batch of its
    /// own.
    pub(crate) fn cbc_encrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let mut prev = *iv;
        for block in blocks {
            for (b, p) in block.iter_mut().zip(prev) {
                *b ^= p;
            }
            let block = core::slice::from_mut(block);
            let mut batch = to_batch(block);
            self.encrypt_batch(&mut batch);
            from_batch(block, &batch);
            prev = block[0];
        }
    }

    /// Decrypts whole blocks in place in CBC mode, the first chained from
    /// `iv`.
    #[cfg_attr(rind_backend = "portable", inline)]
    pub(crate) fn cbc_decrypt(&self, iv: &[u8; 16], blocks: &mut [[u8; 16]]) {
        let mut prev = *iv;
        for chunk in blocks.chunks_mut(BATCH_SIZE) {
            // Copy the ciphertext, which the next block chains from, before
            // decrypting in place.
            let mut copy = [[0u8; 16]; BATCH_SIZE];
            copy[..chunk.len()].copy_from_slice(chunk);

            let mut batch = to_batch(chunk);
            self.decrypt_batch(&mut batch);
            from_batch(chunk, &batch);

            for (block, ct) in chunk.iter_mut().zip(&copy) {
                for (b, p) in block.iter_mut().zip(prev) {
                    *b ^= p;
                }
                prev = *ct;
            }
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // vpaes is the arm above this one on x86_64, so the two must agree for
    // every key size: on single blocks, and on CTR runs around the batch
    // size and across the counter's 32-bit wrap.
    #[cfg(rind_backend = "x86_64")]
    #[test]
    fn matches_vpaes() {
        use crate::low::x86_64::cpu::HaveSsse3;
        use crate::low::x86_64::vpaes_x86_64::VpaesKey;

        let Some(token) = HaveSsse3::check() else {
            return;
        };
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let key = bytes(key_len, seed);
            let nohw = NohwKey::new(&key);
            let vpaes = VpaesKey::new(&key, token);

            let block: [u8; 16] = bytes(16, seed).try_into().unwrap();
            assert_eq!(
                nohw.encrypt_block(&block),
                vpaes.encrypt_block(&block),
                "{key_len}-byte key, one block"
            );

            for counter in [0, u32::MAX - 3] {
                let mut ivec: [u8; 16] = bytes(16, counter).try_into().unwrap();
                ivec[12..].copy_from_slice(&counter.to_be_bytes());
                for blocks in [0, 1, 7, 8, 9, 17] {
                    let input: Vec<[u8; 16]> = bytes(16 * blocks, seed).as_chunks().0.to_vec();
                    let mut want = input.clone();
                    vpaes.ctr32(&ivec, &mut want);
                    let mut got = input;
                    nohw.ctr32(&ivec, &mut got);
                    assert_eq!(
                        got, want,
                        "{key_len}-byte key, counter {counter}, {blocks} blocks"
                    );
                }
            }
        }
    }

    // FIPS-197 Appendix C.1 to C.3, which hold the circuit to AES itself
    // rather than to another implementation, and decryption inverts them.
    #[test]
    fn fips197() {
        let plaintext = 0x00112233_44556677_8899aabb_ccddeeffu128.to_be_bytes();
        for (key, ciphertext) in [
            (
                &(0..16).collect::<Vec<u8>>(),
                0x69c4e0d8_6a7b0430_d8cdb780_70b4c55au128,
            ),
            (
                &(0..24).collect::<Vec<u8>>(),
                0xdda97ca4_864cdfe0_6eaf70a0_ec0d7191u128,
            ),
            (
                &(0..32).collect::<Vec<u8>>(),
                0x8ea2b7ca_516745bf_eafc4990_4b496089u128,
            ),
        ] {
            let schedule = NohwKey::new(key).schedule();
            assert_eq!(schedule.key_len(), key.len());
            let mut block = schedule.encrypt_block(&plaintext);
            assert_eq!(block, ciphertext.to_be_bytes(), "{}-byte key", key.len());
            schedule.decrypt_block(&mut block);
            assert_eq!(block, plaintext, "{}-byte key", key.len());
        }
    }

    // Counter mode and CBC against the single-block cipher, around the batch
    // size, with partial final blocks, and across the counter's 32-bit wrap,
    // which lands mid-batch and then wraps the batch counter too.
    #[test]
    fn modes_match_blocks() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        let add = |ivec: &[u8; 16], n: u32| {
            let mut out = *ivec;
            let ctr = u32::from_be_bytes(ivec[12..].try_into().unwrap()).wrapping_add(n);
            out[12..].copy_from_slice(&ctr.to_be_bytes());
            out
        };
        for (key_len, seed) in [16, 24, 32].into_iter().zip(1..) {
            let schedule = NohwKey::new(&bytes(key_len, seed)).schedule();
            let iv: [u8; 16] = bytes(16, seed + 7).try_into().unwrap();
            for counter in [0, u32::MAX - 3] {
                let mut ivec = iv;
                ivec[12..].copy_from_slice(&counter.to_be_bytes());
                for len in [
                    0,
                    1,
                    15,
                    16,
                    17,
                    16 * BATCH_SIZE - 1,
                    16 * BATCH_SIZE + 1,
                    300,
                ] {
                    let input = bytes(len, seed);
                    let mut want = input.clone();
                    for (i, chunk) in (0..).zip(want.chunks_mut(16)) {
                        let ks = schedule.encrypt_block(&add(&ivec, i));
                        chunk.iter_mut().zip(ks).for_each(|(b, k)| *b ^= k);
                    }
                    let mut got = input;
                    schedule.ctr32(&ivec, &mut got);
                    assert_eq!(
                        got, want,
                        "{key_len}-byte key, counter {counter}, {len} bytes"
                    );
                }
            }

            for blocks in [0, 1, BATCH_SIZE - 1, BATCH_SIZE, BATCH_SIZE + 1, 17] {
                let pt: Vec<[u8; 16]> = bytes(16 * blocks, seed).as_chunks().0.to_vec();
                let mut ct = pt.clone();
                schedule.cbc_encrypt(&iv, &mut ct);
                let mut prev = iv;
                for (c, p) in ct.iter().zip(&pt) {
                    let mut x = *p;
                    x.iter_mut().zip(prev).for_each(|(b, v)| *b ^= v);
                    assert_eq!(*c, schedule.encrypt_block(&x), "{key_len}-byte key");
                    prev = *c;
                }
                schedule.cbc_decrypt(&iv, &mut ct);
                assert_eq!(ct, pt, "{key_len}-byte key, {blocks} blocks");
            }
        }
    }
}
