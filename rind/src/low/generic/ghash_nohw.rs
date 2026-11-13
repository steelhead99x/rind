// Copyright (c) 2019, Google Inc.
// SPDX-License-Identifier: ISC

//! GHASH in integer code alone, for x86_64 CPUs without SSSE3 and for
//! AES-GCM from any IV on armv7 without the crypto extension and on the
//! portable backend: aws-lc's `crypto/fipsmodule/modes/gcm_nohw.c` at commit
//! 91c93a8eb860e51482a871a8772cb9b1b310baea, in Rust, in its 64-bit
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

use crate::low;

/// A GHASH key as POLYVAL multiplies by it: aws-lc's `u128 Htable[16]`'s
/// first entry, the only one it uses, holding H times x.
pub(crate) struct NohwTable {
    hi: u64,
    lo: u64,
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
        Self { hi, lo }
    }

    /// Folds whole blocks of `input` into the GHASH state `xi`, held in the
    /// byte order of a block.
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

#[cfg(target_pointer_width = "32")]
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

/// The carry-less product of `a` and `b`, by 32-bit multiplies.
#[cfg(any(
    all(
        target_pointer_width = "32",
        not(all(target_arch = "arm", not(target_has_atomic = "ptr")))
    ),
    test
))]
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

/// ARMv6-M (Arm without CAS atomics, in cfg terms) has no `umull`, so each
/// 32x32->64 multiply above is a call to `__aeabi_lmul`. This takes the same
/// product with `muls` alone, as BearSSL's `ghash_ctmul32` does: the low word
/// by multiplies truncated to 32 bits, which carries never cross downwards,
/// and the high word as the low word of the product of the bit-reversed
/// operands, reversed. Cortex-M0+ `muls` takes the same time for every
/// operand.
#[cfg(any(all(target_arch = "arm", not(target_has_atomic = "ptr")), test))]
fn gcm_mul32_rev(a: u32, b: u32) -> u64 {
    fn low(a: u32, b: u32) -> u32 {
        let a0 = a & 0x1111_1111;
        let a1 = a & 0x2222_2222;
        let a2 = a & 0x4444_4444;
        let a3 = a & 0x8888_8888;

        let b0 = b & 0x1111_1111;
        let b1 = b & 0x2222_2222;
        let b2 = b & 0x4444_4444;
        let b3 = b & 0x8888_8888;

        let m = u32::wrapping_mul;
        let c0 = m(a0, b0) ^ m(a1, b3) ^ m(a2, b2) ^ m(a3, b1);
        let c1 = m(a0, b1) ^ m(a1, b0) ^ m(a2, b3) ^ m(a3, b2);
        let c2 = m(a0, b2) ^ m(a1, b1) ^ m(a2, b0) ^ m(a3, b3);
        let c3 = m(a0, b3) ^ m(a1, b2) ^ m(a2, b1) ^ m(a3, b0);

        (c0 & 0x1111_1111) | (c1 & 0x2222_2222) | (c2 & 0x4444_4444) | (c3 & 0x8888_8888)
    }
    // The 63-bit product's bits 31 to 62, reversed.
    let hi = low(a.reverse_bits(), b.reverse_bits()).reverse_bits() >> 1;
    u64::from(low(a, b)) | u64::from(hi) << 32
}

#[cfg(all(target_arch = "arm", not(target_has_atomic = "ptr")))]
use gcm_mul32_rev as gcm_mul32_nohw;

/// The carry-less product of `a` and `b`, as its low and high words, by
/// Karatsuba over 32-bit halves.
#[cfg(any(target_pointer_width = "32", test))]
fn gcm_mul64_split(a: u64, b: u64) -> (u64, u64) {
    let (a0, a1) = (a as u32, (a >> 32) as u32);
    let (b0, b1) = (b as u32, (b >> 32) as u32);
    let lo = gcm_mul32_nohw(a0, b0);
    let hi = gcm_mul32_nohw(a1, b1);
    let mid = gcm_mul32_nohw(a0 ^ a1, b0 ^ b1) ^ lo ^ hi;
    (lo ^ (mid << 32), hi ^ (mid >> 32))
}

/// Multiplies `xi` by `h` in POLYVAL's field.
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

    // ARMv6-M's 32-bit product agrees with the widening one.
    #[test]
    fn mul32_rev_matches() {
        let mut x = 0x2545_f491_4f6c_dd1du64;
        for _ in 0..10_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let (a, b) = (x as u32, (x >> 32) as u32);
            assert_eq!(gcm_mul32_rev(a, b), gcm_mul32_nohw(a, b), "{a:x} {b:x}");
        }
        for (a, b) in [
            (u32::MAX, u32::MAX),
            (0, u32::MAX),
            (1, 1),
            (1 << 31, 1 << 31),
        ] {
            assert_eq!(gcm_mul32_rev(a, b), gcm_mul32_nohw(a, b), "{a:x} {b:x}");
        }
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
