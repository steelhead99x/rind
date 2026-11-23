// Copyright (c) 2019, Google Inc.
// SPDX-License-Identifier: ISC

//! GHASH in integer code alone, for x86_64 CPUs without SSSE3 and for
//! AES-GCM from any IV on armv7 without the crypto extension and on the
//! portable backend: aws-lc's `crypto/fipsmodule/modes/gcm_nohw.c` at commit
//! 5ed12cce0fd4453f2f63300d44325ed14f845d6f, in Rust, in its 64-bit
//! configuration on 64-bit targets and its 32-bit one on 32-bit targets.
//!
//! It multiplies carry-less with ordinary integer multiplies of operands
//! masked to every fourth bit, so carries never reach the bits it keeps
//! (<https://bearssl.org/constanttime.html#ghash-for-gcm>), and reduces as
//! <https://crypto.stanford.edu/RealWorldCrypto/slides/gueron.pdf> describes.
//! x86_64's 64-bit `mul` and armv7's `umull` take the same time for every
//! operand, so its timing is independent of the key and data. It is not
//! formally verified: its correctness rests on its use and testing in
//! BoringSSL and aws-lc, and on rind's tests of it against SSSE3, the
//! portable model, Wycheproof, and aws-lc-rs.
//!
//! The portable backend on 32-bit targets multiplies differently, in rind's
//! own arrangement of the same idea ([`polyval_k16`]): Karatsuba three
//! levels down to 27 products of 16-bit halves, each by nine 32-bit `mul`s
//! of operands masked to every third bit, whose whole product fits the low
//! word. riscv32imac then needs no `mulhu`, which a fit of ESP32-C6 board
//! timings puts at about one cycle more than `mul`, and the key's halves
//! are split and masked once, when the key is set. Its timing likewise rests on `mul` taking the
//! same time for every operand.
//!
//! That holds where a 32-bit `mul` is fixed-time: riscv32imac, i686, and
//! Arm cores whose `MUL` is single-cycle. It does not hold where `mul` is a
//! library call (riscv32i without the M extension calls `__mulsi3`, which
//! branches on its operands) or the core has the small, slow multiplier
//! option (Cortex-M0). Only riscv32imac has been measured, and the 64-bit
//! products the old 32-bit path formed had the same dependence on those
//! cores.

use crate::low;

/// A GHASH key as POLYVAL multiplies by it: aws-lc's `u128 Htable[16]`'s
/// first entry, the only one it uses, holding H times x.
pub(crate) struct NohwTable {
    #[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
    hi: u64,
    #[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
    lo: u64,
    /// The same key as [`leaves`] splits it, each leaf masked by [`M0`],
    /// [`M1`], and [`M2`], for [`polyval_k16`].
    #[cfg(all(rind_backend = "portable", target_pointer_width = "32"))]
    leaves: Leaves,
}

impl NohwTable {
    /// Precomputes for the GHASH key `h`, AES's encryption of the zero block.
    pub(crate) fn new(h: &[u8; 16]) -> Self {
        // aws-lc's `gcm_init_nohw`. GHASH is computed as POLYVAL (RFC 8452),
        // which avoids a shift by one in each multiplication, after
        // mulX_POLYVAL of H per its Appendix A.
        let h = u128::from_be_bytes(*h);
        let mut hi = (h >> 64) as u64;
        let mut lo = h as u64;

        let carry = 0u64.wrapping_sub(hi >> 63);
        hi = (hi << 1) | (lo >> 63);
        lo <<= 1;

        // The irreducible polynomial is 1 + x^121 + x^126 + x^127 + x^128, so
        // conditionally add 0xc200...0001.
        lo ^= carry & 1;
        hi ^= carry & 0xc200_0000_0000_0000;
        #[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
        return Self { hi, lo };
        #[cfg(all(rind_backend = "portable", target_pointer_width = "32"))]
        return Self {
            leaves: key_leaves(hi, lo),
        };
    }

    /// Folds whole blocks of `input` into the GHASH state `xi`, held in the
    /// byte order of a block.
    #[cfg(all(rind_backend = "portable", target_pointer_width = "32"))]
    pub(crate) fn ghash(&self, xi: &mut [u8; 16], input: &[[u8; 16]]) {
        let mut x = [
            be_word(xi, 0),
            be_word(xi, 1),
            be_word(xi, 2),
            be_word(xi, 3),
        ];
        polyval_k16(&mut x, input, &self.leaves);
        for (i, w) in x.iter().enumerate() {
            xi[12 - 4 * i..16 - 4 * i].copy_from_slice(&w.to_be_bytes());
        }
    }

    /// Folds whole blocks of `input` into the GHASH state `xi`, held in the
    /// byte order of a block.
    #[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
    pub(crate) fn ghash(&self, xi: &mut [u8; 16], input: &[[u8; 16]]) {
        let x = u128::from_be_bytes(*xi);
        let mut swapped = [x as u64, (x >> 64) as u64];

        for block in input {
            let b = u128::from_be_bytes(*block);
            swapped[0] ^= b as u64;
            swapped[1] ^= (b >> 64) as u64;
            gcm_polyval_nohw(&mut swapped, self);
        }

        *xi = (u128::from(swapped[1]) << 64 | u128::from(swapped[0])).to_be_bytes();
    }
}

impl Drop for NohwTable {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::generic::zeroise::Zeroable for NohwTable {}

#[cfg(all(target_pointer_width = "32", not(rind_backend = "portable")))]
use gcm_mul64_split as gcm_mul64_nohw;
#[cfg(not(target_pointer_width = "32"))]
use gcm_mul64_wide as gcm_mul64_nohw;

/// The carry-less product of `a` and `b`, as its low and high words, by
/// 64-bit multiplies.
#[cfg(any(not(target_pointer_width = "32"), test))]
fn gcm_mul64_wide(a: u64, b: u64) -> (u64, u64) {
    // One term every four bits means the largest term is 64/4 = 16, which
    // barely overflows into the next term. Using one term every five bits
    // would cost 25 multiplications instead of 16. It is faster to mask off
    // the bottom four bits of `a`, giving a largest term of 60/4 = 15, and
    // apply the bottom bits separately.
    let a0 = a & 0x1111_1111_1111_1110;
    let a1 = a & 0x2222_2222_2222_2220;
    let a2 = a & 0x4444_4444_4444_4440;
    let a3 = a & 0x8888_8888_8888_8880;

    let b0 = b & 0x1111_1111_1111_1111;
    let b1 = b & 0x2222_2222_2222_2222;
    let b2 = b & 0x4444_4444_4444_4444;
    let b3 = b & 0x8888_8888_8888_8888;

    let m = |x: u64, y: u64| u128::from(x) * u128::from(y);
    let c0 = m(a0, b0) ^ m(a1, b3) ^ m(a2, b2) ^ m(a3, b1);
    let c1 = m(a0, b1) ^ m(a1, b0) ^ m(a2, b3) ^ m(a3, b2);
    let c2 = m(a0, b2) ^ m(a1, b1) ^ m(a2, b0) ^ m(a3, b3);
    let c3 = m(a0, b3) ^ m(a1, b2) ^ m(a2, b1) ^ m(a3, b0);

    // Multiply the bottom four bits of `a` with `b`.
    let a0_mask = 0u64.wrapping_sub(a & 1);
    let a1_mask = 0u64.wrapping_sub((a >> 1) & 1);
    let a2_mask = 0u64.wrapping_sub((a >> 2) & 1);
    let a3_mask = 0u64.wrapping_sub((a >> 3) & 1);
    let extra = u128::from(a0_mask & b)
        ^ (u128::from(a1_mask & b) << 1)
        ^ (u128::from(a2_mask & b) << 2)
        ^ (u128::from(a3_mask & b) << 3);

    let lo = (c0 as u64 & 0x1111_1111_1111_1111)
        ^ (c1 as u64 & 0x2222_2222_2222_2222)
        ^ (c2 as u64 & 0x4444_4444_4444_4444)
        ^ (c3 as u64 & 0x8888_8888_8888_8888)
        ^ extra as u64;
    let hi = ((c0 >> 64) as u64 & 0x1111_1111_1111_1111)
        ^ ((c1 >> 64) as u64 & 0x2222_2222_2222_2222)
        ^ ((c2 >> 64) as u64 & 0x4444_4444_4444_4444)
        ^ ((c3 >> 64) as u64 & 0x8888_8888_8888_8888)
        ^ (extra >> 64) as u64;
    (lo, hi)
}

/// The carry-less product of `a` and `b`, by 32-bit multiplies, for
/// armv7's portable path. The portable backend on 32-bit targets
/// multiplies by [`polyval_k16`] instead: there, out of line, this took 16
/// `mulhu` a call on riscv32imac, and inlined three times into
/// `gcm_mul64_split`, LLVM issued all 96 multiplies first and spilled.
#[cfg(any(all(target_pointer_width = "32", not(rind_backend = "portable")), test))]
fn gcm_mul32_nohw(a: u32, b: u32) -> u64 {
    // One term every four bits means the largest term is 32/4 = 8, which
    // does not overflow into the next term.
    let a0 = a & 0x1111_1111;
    let a1 = a & 0x2222_2222;
    let a2 = a & 0x4444_4444;
    let a3 = a & 0x8888_8888;

    let b0 = b & 0x1111_1111;
    let b1 = b & 0x2222_2222;
    let b2 = b & 0x4444_4444;
    let b3 = b & 0x8888_8888;

    let m = |x: u32, y: u32| u64::from(x) * u64::from(y);
    let c0 = m(a0, b0) ^ m(a1, b3) ^ m(a2, b2) ^ m(a3, b1);
    let c1 = m(a0, b1) ^ m(a1, b0) ^ m(a2, b3) ^ m(a3, b2);
    let c2 = m(a0, b2) ^ m(a1, b1) ^ m(a2, b0) ^ m(a3, b3);
    let c3 = m(a0, b3) ^ m(a1, b2) ^ m(a2, b1) ^ m(a3, b0);

    (c0 & 0x1111_1111_1111_1111)
        | (c1 & 0x2222_2222_2222_2222)
        | (c2 & 0x4444_4444_4444_4444)
        | (c3 & 0x8888_8888_8888_8888)
}

/// Every third bit of a word, from bit 0; [`M1`] and [`M2`] from bits 1
/// and 2.
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
const M0: u32 = 0x4924_9249;
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
const M1: u32 = M0 << 1;
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
const M2: u32 = M0 << 2;

/// A 128-bit operand's 27 Karatsuba leaves, 16 bits each, the key's held
/// masked by [`M0`], [`M1`], and [`M2`].
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
type Leaves = [[u32; 3]; 27];

/// The 16-bit operands of the 27 carry-less multiplies Karatsuba splits a
/// 128-bit product into, three levels down, from `x`'s words least
/// significant first. Leaf `9i + 3j + k` is half `k` of half `j` of half
/// `i`, where half 0 is the low one, 1 the high one, and 2 their sum.
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
fn leaves(x: [u32; 4]) -> [u32; 27] {
    let mut out = [0u32; 27];
    let h64 = [[x[0], x[1]], [x[2], x[3]], [x[0] ^ x[2], x[1] ^ x[3]]];
    for (i, h) in h64.iter().enumerate() {
        for (j, w) in [h[0], h[1], h[0] ^ h[1]].into_iter().enumerate() {
            out[9 * i + 3 * j] = w & 0xffff;
            out[9 * i + 3 * j + 1] = w >> 16;
            out[9 * i + 3 * j + 2] = (w ^ (w >> 16)) & 0xffff;
        }
    }
    out
}

/// The key `hi x^64 + lo`'s [`Leaves`].
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
fn key_leaves(hi: u64, lo: u64) -> Leaves {
    leaves([lo as u32, (lo >> 32) as u32, hi as u32, (hi >> 32) as u32])
        .map(|y| [y & M0, y & M1, y & M2])
}

/// The carry-less product of 16-bit `x` and the 16-bit `y` split by
/// [`M0`], [`M1`], and [`M2`], by 32-bit multiplies alone.
///
/// Operands masked to every third bit hold at most six terms each, so a
/// product's sum at any bit is at most six: three bits, which never carry
/// into the next bit of the same residue mod 3, the only one kept. Both
/// operands below 2^16 keep the product within 32 bits, so the low-word
/// `mul` gives all of it, with no `mulhu`.
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
#[inline(always)]
fn clmul16(x: u32, y: &[u32; 3]) -> u32 {
    let (x0, x1, x2) = (x & M0, x & M1, x & M2);
    let [y0, y1, y2] = *y;
    let m = |a: u32, b: u32| a.wrapping_mul(b);
    let z0 = m(x0, y0) ^ m(x1, y2) ^ m(x2, y1);
    let z1 = m(x0, y1) ^ m(x1, y0) ^ m(x2, y2);
    let z2 = m(x0, y2) ^ m(x1, y1) ^ m(x2, y0);
    (z0 & M0) | (z1 & M1) | (z2 & M2)
}

/// The carry-less product of `w` and the key's 32-bit operand whose
/// leaves are `h`, as its low and high words.
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
#[inline(always)]
fn kara32(w: u32, h: &[[u32; 3]]) -> (u32, u32) {
    let lo = clmul16(w & 0xffff, &h[0]);
    let hi = clmul16(w >> 16, &h[1]);
    let mid = clmul16((w ^ (w >> 16)) & 0xffff, &h[2]) ^ lo ^ hi;
    (lo ^ (mid << 16), hi ^ (mid >> 16))
}

/// Word `i` of a GHASH block, counting from its least significant end as
/// POLYVAL orders a block's bits.
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
#[inline(always)]
fn be_word(b: &[u8; 16], i: usize) -> u32 {
    u32::from_be_bytes([b[12 - 4 * i], b[13 - 4 * i], b[14 - 4 * i], b[15 - 4 * i]])
}

/// Folds each block of `input` into `x` and multiplies it by the key in
/// POLYVAL's field, by the key's [`Leaves`]: 27 [`clmul16`]s, Karatsuba's
/// sums back up the three levels, and the reduction of `gcm_polyval_nohw`.
///
/// The nine 32-bit products run in a loop, each from memory to memory:
/// unrolled, LLVM issues the 243 multiplies first and spills most of them.
#[cfg(any(all(rind_backend = "portable", target_pointer_width = "32"), test))]
#[inline(never)]
fn polyval_k16(x: &mut [u32; 4], input: &[[u8; 16]], h: &Leaves) {
    let mut p = [(0u32, 0u32); 9];
    for block in input {
        for (i, x) in x.iter_mut().enumerate() {
            *x ^= be_word(block, i);
        }
        // The nine 32-bit operands, as `leaves` splits `x`.
        let (s0, s1) = (x[0] ^ x[2], x[1] ^ x[3]);
        let w = [
            x[0],
            x[1],
            x[0] ^ x[1],
            x[2],
            x[3],
            x[2] ^ x[3],
            s0,
            s1,
            s0 ^ s1,
        ];
        for (i, (p, w)) in p.iter_mut().zip(w).enumerate() {
            *p = kara32(w, &h[3 * i..3 * i + 3]);
        }
        let kara64 = |l: (u32, u32), h: (u32, u32), m: (u32, u32)| {
            let (m0, m1) = (m.0 ^ l.0 ^ h.0, m.1 ^ l.1 ^ h.1);
            let lo = u64::from(l.0) | u64::from(l.1 ^ m0) << 32;
            let hi = u64::from(h.0 ^ m1) | u64::from(h.1) << 32;
            (lo, hi)
        };
        let (r0, mut r1) = kara64(p[0], p[1], p[2]);
        let (mut r2, mut r3) = kara64(p[3], p[4], p[5]);
        let (mut mid0, mut mid1) = kara64(p[6], p[7], p[8]);
        mid0 ^= r0 ^ r2;
        mid1 ^= r1 ^ r3;
        r2 ^= mid1;
        r1 ^= mid0;

        // As `gcm_polyval_nohw` reduces.
        r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);
        r2 ^= r0 ^ (r0 >> 1) ^ (r0 >> 2) ^ (r0 >> 7);
        r2 ^= (r1 << 63) ^ (r1 << 62) ^ (r1 << 57);
        r3 ^= r1 ^ (r1 >> 1) ^ (r1 >> 2) ^ (r1 >> 7);
        *x = [r2 as u32, (r2 >> 32) as u32, r3 as u32, (r3 >> 32) as u32];
    }
}

/// The carry-less product of `a` and `b`, as its low and high words, by
/// Karatsuba over 32-bit halves.
#[cfg(any(all(target_pointer_width = "32", not(rind_backend = "portable")), test))]
fn gcm_mul64_split(a: u64, b: u64) -> (u64, u64) {
    let (a0, a1) = (a as u32, (a >> 32) as u32);
    let (b0, b1) = (b as u32, (b >> 32) as u32);
    let lo = gcm_mul32_nohw(a0, b0);
    let hi = gcm_mul32_nohw(a1, b1);
    let mid = gcm_mul32_nohw(a0 ^ a1, b0 ^ b1) ^ lo ^ hi;
    (lo ^ (mid << 32), hi ^ (mid >> 32))
}

/// Multiplies `xi` by `h` in POLYVAL's field.
#[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
fn gcm_polyval_nohw(xi: &mut [u64; 2], h: &NohwTable) {
    // Karatsuba multiplication. The product of `xi` and `h` is stored in `r0`
    // through `r3`. Note there is no byte or bit reversal because we are
    // evaluating POLYVAL.
    let (r0, mut r1) = gcm_mul64_nohw(xi[0], h.lo);
    let (mut r2, mut r3) = gcm_mul64_nohw(xi[1], h.hi);
    let (mut mid0, mut mid1) = gcm_mul64_nohw(xi[0] ^ xi[1], h.hi ^ h.lo);
    mid0 ^= r0 ^ r2;
    mid1 ^= r1 ^ r3;
    r2 ^= mid1;
    r1 ^= mid0;

    // Now we multiply our 256-bit result by x^-128 and reduce. `r2` and `r3`
    // shift into position and we must multiply `r0` and `r1` by x^-128. We
    // have:
    //
    //       1 = x^121 + x^126 + x^127 + x^128
    //  x^-128 = x^-7 + x^-2 + x^-1 + 1
    //
    // This is the GHASH reduction step, but with bits flowing in reverse.

    // The x^-7, x^-2, and x^-1 terms shift bits past x^0, which would require
    // another reduction step. Instead, we gather the excess bits, incorporate
    // them into `r0` and `r1` and reduce once.
    r1 ^= (r0 << 63) ^ (r0 << 62) ^ (r0 << 57);

    // 1
    r2 ^= r0;
    r3 ^= r1;

    // x^-1
    r2 ^= r0 >> 1;
    r2 ^= r1 << 63;
    r3 ^= r1 >> 1;

    // x^-2
    r2 ^= r0 >> 2;
    r2 ^= r1 << 62;
    r3 ^= r1 >> 2;

    // x^-7
    r2 ^= r0 >> 7;
    r2 ^= r1 << 57;
    r3 ^= r1 >> 7;

    *xi = [r2, r3];
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::generic::ghash as model;
    #[cfg(rind_backend = "x86_64")]
    use crate::low::x86_64::cpu::HaveSsse3;
    #[cfg(rind_backend = "x86_64")]
    use crate::low::x86_64::ghash_ssse3_x86_64::Ssse3Table;

    // Both configurations' products agree, under operands of pseudo-random
    // bits and of all ones, whose products carry furthest between the
    // masked terms.
    #[test]
    fn multiplies_match() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for _ in 0..1000 {
            let (a, b) = (next(), next());
            assert_eq!(gcm_mul64_wide(a, b), gcm_mul64_split(a, b), "{a:x} {b:x}");
        }
        assert_eq!(
            gcm_mul64_wide(u64::MAX, u64::MAX),
            gcm_mul64_split(u64::MAX, u64::MAX)
        );
    }

    // The 32-bit portable multiply against GHASH by the book, on every
    // target, so 64-bit hosts test it too: from pseudo-random and all-ones
    // keys, states, and blocks, whose products carry furthest within a
    // residue class, and for each block count up to three.
    #[test]
    fn k16_matches_model() {
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut next = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for ones in [true, false] {
            for _ in 0..200 {
                let mut word = || if ones { u64::MAX } else { next() };
                let key = (u128::from(word()) << 64 | u128::from(word())).to_be_bytes();
                let start = (u128::from(word()) << 64 | u128::from(word())).to_be_bytes();
                let blocks = [0, 1, 2, 3]
                    .map(|_| (u128::from(word()) << 64 | u128::from(word())).to_be_bytes());

                // `NohwTable::new`'s mulX_POLYVAL of the key.
                let h = u128::from_be_bytes(key);
                let carry = 0u128.wrapping_sub(h >> 127);
                let h = (h << 1) ^ (carry & (0xc2u128 << 120 | 1));
                let leaves = key_leaves((h >> 64) as u64, h as u64);

                for n in 0..=3 {
                    let mut got = [
                        be_word(&start, 0),
                        be_word(&start, 1),
                        be_word(&start, 2),
                        be_word(&start, 3),
                    ];
                    polyval_k16(&mut got, &blocks[..n], &leaves);

                    let mut flat = blocks[..n].concat();
                    for (f, s) in flat.iter_mut().zip(start) {
                        *f ^= s;
                    }
                    let mut want = start;
                    if n > 0 {
                        let table = model::GhashTable::new(u128::from_be_bytes(key));
                        let mut model = model::Ghash::new(&table);
                        model.add(&flat);
                        want = model.into_bytes();
                    }
                    let want = [
                        be_word(&want, 0),
                        be_word(&want, 1),
                        be_word(&want, 2),
                        be_word(&want, 3),
                    ];
                    assert_eq!(got, want, "{n} blocks");
                }
                if ones {
                    break;
                }
            }
        }
    }

    // Under ctgrind, with the key, state, and blocks secret, no branch or
    // memory index of the 32-bit portable multiply or its key setup depends
    // on them.
    #[test]
    fn k16_constant_time() {
        use crate::low::ct::{into_public, into_secret};
        let leaves = key_leaves(into_secret(0x0123_4567_89ab_cdef), into_secret(0x0fed_cba9));
        let mut x = into_secret([1u32, 2, 3, 4]);
        let blocks = into_secret([[0x5au8; 16]; 3]);
        polyval_k16(&mut x, &blocks, &leaves);
        assert_ne!(into_public(x), [0; 4]);
    }

    // On x86_64, the SSSE3 table is the arm above this one, and the model
    // is GHASH by the book, so all three must agree from any state, under
    // keys and inputs of pseudo-random bytes and of all ones, whose products
    // carry furthest between the masked terms.
    #[test]
    fn matches_ssse3_and_model() {
        let bytes = |n: usize, seed: u32| -> Vec<u8> {
            (0..n as u32)
                .map(|i| (i.wrapping_add(seed).wrapping_mul(0x9e3779b9) >> 24) as u8)
                .collect()
        };
        for seed in [0, 1, 2] {
            let pick = |n, s| match seed {
                0 => vec![0xff; n],
                _ => bytes(n, s),
            };
            let key: [u8; 16] = pick(16, seed).try_into().unwrap();
            let start: [u8; 16] = match seed {
                0 => [0; 16],
                _ => bytes(16, seed + 100).try_into().unwrap(),
            };
            let nohw = NohwTable::new(&key);
            #[cfg(rind_backend = "x86_64")]
            let ssse3 = HaveSsse3::check().map(|token| Ssse3Table::new(&key, token));

            let mut xi = start;
            nohw.ghash(&mut xi, &[]);
            assert_eq!(xi, start, "seed {seed}, no blocks");

            for blocks in [1, 2, 3, 8, 17] {
                let input: Vec<[u8; 16]> = pick(16 * blocks, seed + 200).as_chunks().0.to_vec();
                let what = format!("seed {seed}, {blocks} blocks");

                let mut got = start;
                nohw.ghash(&mut got, &input);

                #[cfg(rind_backend = "x86_64")]
                if let Some(ssse3) = &ssse3 {
                    let mut want = start;
                    ssse3.ghash(&mut want, &input);
                    assert_eq!(got, want, "{what}: SSSE3");
                }

                // The model starts from zero, so the state joins the first
                // block.
                let mut flat = input.concat();
                for (f, s) in flat.iter_mut().zip(start) {
                    *f ^= s;
                }
                let table = model::GhashTable::new(u128::from_be_bytes(key));
                let mut model = model::Ghash::new(&table);
                model.add(&flat);
                assert_eq!(got, model.into_bytes(), "{what}: model");
            }
        }
    }
}
