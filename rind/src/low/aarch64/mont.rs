// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Montgomery multiplication modulo an RSA modulus or prime.
//!
//! From two words, aws-lc's `bn_mul_mont`, which picks its own squaring or
//! 4x routine by the width as aws-lc does. On a Neoverse-N2, a wide
//! multiplier, it measured faster than s2n-bignum's generic routines in
//! every width class it branches on: 1.15x at 17 and 33 words, 1.6x at 20,
//! and twice as fast at 24, 48, 64, 96, and 128. It was also faster there
//! than s2n-bignum's Karatsuba routines at 16 and 32 words.
//!
//! On a narrow multiplier the comparison reverses. At 16 and 32 words,
//! RSA-2048's prime and modulus, this runs s2n-bignum's Karatsuba product
//! and its 8n reduction, which is what aws-lc runs on a core outside its
//! wide allowlist (Neoverse V1, V2, V3, and Apple). This crate also keeps
//! `bn_mul_mont` on Neoverse N2, Cobalt 100, and any core Linux does not
//! identify as Cortex-A72, Cortex-A76, or Neoverse N1. The generic
//! routines run only below two words.

/// `z = x * y / 2^(64k) mod m`, for `x` and `y` below `m`, where `k` is the
/// length of each and `n0` is `-m^-1 mod 2^64`.
pub(crate) fn mont_mul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    assert!(z.len() == m.len() && x.len() == m.len() && y.len() == m.len());
    match m.len() {
        16 | 32 if !super::cpu::wide_multiplier() => karatsuba_mul(z, x, y, m, n0),
        k if k >= 2 => mul_mont(z, x, y, m, n0),
        _ => super::bignum_montmul::bignum_montmul(z, x, y, m),
    }
}

/// `z = x^2 / 2^(64k) mod m`, for `x` below `m`, where `k` is the length of
/// each and `n0` is `-m^-1 mod 2^64`.
pub(crate) fn mont_sqr(z: &mut [u64], x: &[u64], m: &[u64], n0: u64) {
    assert!(z.len() == m.len() && x.len() == m.len());
    match m.len() {
        16 | 32 if !super::cpu::wide_multiplier() => karatsuba_sqr(z, x, m, n0),
        k if k >= 2 => mul_mont(z, x, x, m, n0),
        _ => super::bignum_montsqr::bignum_montsqr(z, x, m),
    }
}

/// `mont_mul` for 16 or 32 words on a narrow multiplier.
fn karatsuba_mul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    if m.len() == 16 {
        let mut product = [0; 32];
        super::bignum_kmul_16_32::bignum_kmul_16_32(&mut product, x, y, &mut [0; 32]);
        redc_8n(z, &mut product, m, n0);
    } else {
        let mut product = [0; 64];
        super::bignum_kmul_32_64::bignum_kmul_32_64(&mut product, x, y, &mut [0; 96]);
        redc_8n(z, &mut product, m, n0);
    }
}

/// `mont_sqr` for 16 or 32 words on a narrow multiplier.
fn karatsuba_sqr(z: &mut [u64], x: &[u64], m: &[u64], n0: u64) {
    if m.len() == 16 {
        let mut product = [0; 32];
        super::bignum_ksqr_16_32::bignum_ksqr_16_32(&mut product, x, &mut [0; 24]);
        redc_8n(z, &mut product, m, n0);
    } else {
        let mut product = [0; 64];
        super::bignum_ksqr_32_64::bignum_ksqr_32_64(&mut product, x, &mut [0; 72]);
        redc_8n(z, &mut product, m, n0);
    }
}

/// Reduces the `2k`-word `product` into the `k`-word `z`, fully, modulo `m`.
fn redc_8n(z: &mut [u64], product: &mut [u64], m: &[u64], n0: u64) {
    let carry = super::bignum_emontredc_8n::bignum_emontredc_8n(product, m, n0);
    let (_, reduced) = product.split_at(m.len());
    let ge = carry | (1 - super::bignum_cmp_lt::bignum_cmp_lt(reduced, m));
    super::bignum_optsub::bignum_optsub(z, reduced, m, ge);
}

/// `mont_mul` for any width from two words. It squares by its own routine
/// when `x` and `y` are the same slice and the width is a multiple of eight.
fn mul_mont(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    let k = m.len();
    assert!(k >= 2 && z.len() == k && x.len() == k && y.len() == k);
    // SAFETY: `z`, `x`, `y`, and `m` are each `k` words, as `bn_mul_mont`
    // reads and writes for such a `k`, and it reads `n0` as one word.
    unsafe {
        asm_call!(unsafe extern "C" bn_mul_mont(z.as_mut_ptr(), x.as_ptr(), y.as_ptr(), m.as_ptr(), &n0, k))
    };
}

/// Returns 1, which tells aws-lc's C it ran.
#[unsafe(naked)]
unsafe extern "C" fn bn_mul_mont(
    rp: *mut u64,
    ap: *const u64,
    bp: *const u64,
    np: *const u64,
    n0: *const u64,
    num: usize,
) -> i32 {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(include_str!("aws_lc/bn_mul_mont.linux.s"));
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(include_str!("aws_lc/bn_mul_mont.apple.s"));
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::super::{bignum_montmul, bignum_negmodinv};
    use super::*;
    use crate::test::bignum::{below, div_r, mod_mul_vectors, modulus};

    /// `bn_mul_mont`'s product of `x` and `y`, and its square of `x`.
    fn mul_and_sqr(x: &[u64], y: &[u64], m: &[u64]) -> [Vec<u64>; 2] {
        let mut n0 = [0];
        bignum_negmodinv::bignum_negmodinv(&mut n0, &m[..1]);
        let (mut mul, mut sqr) = (vec![0; m.len()], vec![0; m.len()]);
        mul_mont(&mut mul, x, y, m, n0[0]);
        mul_mont(&mut sqr, x, x, m, n0[0]);
        if matches!(m.len(), 16 | 32) {
            let (mut kmul, mut ksqr) = (vec![0; m.len()], vec![0; m.len()]);
            karatsuba_mul(&mut kmul, x, y, m, n0[0]);
            karatsuba_sqr(&mut ksqr, x, m, n0[0]);
            assert_eq!((mul.clone(), sqr.clone()), (kmul, ksqr));
        }
        [mul, sqr]
    }

    /// A modulus of a width taking each of `bn_mul_mont`'s paths, and two
    /// values below it.
    fn operands() -> impl Strategy<Value = (Vec<u64>, Vec<u64>, Vec<u64>)> {
        const WIDTHS: &[usize] = &[
            2, 3, 5, 8, 9, 12, 16, 17, 18, 24, 32, 33, 36, 48, 64, 96, 128,
        ];
        prop::sample::select(WIDTHS)
            .prop_flat_map(|k| modulus(64, k))
            .prop_flat_map(|m| (Just(m.clone()), below(64, m.clone()), below(64, m)))
    }

    proptest! {
        // Every other test runs only the routine each width picks, so here
        // aws-lc's are checked against s2n-bignum's generic
        // `bignum_montmul`, multiplying and squaring.
        #[test]
        fn matches_generic((m, x, y) in operands()) {
            let (mut mul, mut sqr) = (vec![0; m.len()], vec![0; m.len()]);
            bignum_montmul::bignum_montmul(&mut mul, &x, &y, &m);
            bignum_montmul::bignum_montmul(&mut sqr, &x, &x, &m);
            prop_assert_eq!(mul_and_sqr(&x, &y, &m), [mul, sqr]);
        }
    }

    #[test]
    fn aws_lc_mod_mul() {
        let mut ran = 0;
        for v in mod_mul_vectors().iter().filter(|v| v.m.len() >= 2) {
            let want = div_r(&v.want, &v.m);
            let [mul, sqr] = mul_and_sqr(&v.a, &v.b, &v.m);
            assert_eq!(mul, want, "{}", v.at);
            if v.a == v.b {
                assert_eq!(sqr, want, "squaring, {}", v.at);
            }
            ran += 1;
        }
        assert!(ran > 0);
    }
}
