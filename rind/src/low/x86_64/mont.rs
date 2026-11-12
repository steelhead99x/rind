// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Montgomery multiplication modulo an RSA modulus or prime, by the fastest
//! routine for its width in words, as measured against each other:
//!
//! - With BMI2 and ADX, s2n-bignum's Karatsuba routines and its 8n
//!   reduction for 16 and 32 words.
//! - Otherwise, from eight words, aws-lc's `bn_mul4x_mont` for a multiple of
//!   four, and its `bn_sqr8x_mont` for squaring a multiple of eight; each
//!   runs its `mulx`, `adcx`, and `adox` variant with BMI2 and ADX.
//! - Otherwise, aws-lc's `bn_mul_mont_nohw`.
//!
//! These are what aws-lc's `bn_mul_mont` picks, but for the Karatsuba
//! routines, which multiply faster than `bn_mulx4x_mont` and square level
//! with `bn_sqr8x_mont`. The aws-lc routines measured 1.1 to 3 times as fast
//! as s2n-bignum's generic `bignum_montmul` and `bignum_montsqr`, and
//! `bignum_montmul` runs only below two words, which `bn_mul_mont_nohw` does
//! not take.

use core::mem::MaybeUninit;

use super::cpu::HaveBmi2Adx;

/// `z = x * y / 2^(64k) mod m`, for `x` and `y` below `m`, where `k` is the
/// length of each and `n0` is `-m^-1 mod 2^64`.
pub(crate) fn mont_mul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    assert!(z.len() == m.len() && x.len() == m.len() && y.len() == m.len());
    match (HaveBmi2Adx::check(), m.len()) {
        (Some(_), 16 | 32) => karatsuba_mul(z, x, y, m, n0),
        (adx, k) if k >= 8 && k.is_multiple_of(4) => mul4x(z, x, y, m, n0, adx),
        (_, k) if k >= 2 => nohw(z, x, y, m, n0),
        _ => super::bignum_montmul::bignum_montmul(z, x, y, m),
    }
}

/// `z = x^2 / 2^(64k) mod m`, for `x` below `m`, where `k` is the length of
/// each and `n0` is `-m^-1 mod 2^64`.
pub(crate) fn mont_sqr(z: &mut [u64], x: &[u64], m: &[u64], n0: u64) {
    assert!(z.len() == m.len() && x.len() == m.len());
    match (HaveBmi2Adx::check(), m.len()) {
        (Some(_), 16 | 32) => karatsuba_sqr(z, x, m, n0),
        (adx, k) if k >= 8 && k.is_multiple_of(8) => sqr8x(z, x, m, n0, adx),
        (adx, k) if k >= 8 && k.is_multiple_of(4) => mul4x(z, x, x, m, n0, adx),
        (_, k) if k >= 2 => nohw(z, x, x, m, n0),
        _ => super::bignum_montmul::bignum_montmul(z, x, x, m),
    }
}

/// `mont_mul` for 16 or 32 words, with BMI2 and ADX.
fn karatsuba_mul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    if m.len() == 16 {
        let mut product = [0; 32];
        super::bignum_kmul_16_32::bignum_kmul_16_32(
            &mut product,
            x,
            y,
            &mut [MaybeUninit::uninit(); 32],
        );
        redc_8n(z, &mut product, m, n0);
    } else {
        let mut product = [0; 64];
        super::bignum_kmul_32_64::bignum_kmul_32_64(
            &mut product,
            x,
            y,
            &mut [MaybeUninit::uninit(); 96],
        );
        redc_8n(z, &mut product, m, n0);
    }
}

/// `mont_sqr` for 16 or 32 words, with BMI2 and ADX.
fn karatsuba_sqr(z: &mut [u64], x: &[u64], m: &[u64], n0: u64) {
    if m.len() == 16 {
        let mut product = [0; 32];
        super::bignum_ksqr_16_32::bignum_ksqr_16_32(
            &mut product,
            x,
            &mut [MaybeUninit::uninit(); 24],
        );
        redc_8n(z, &mut product, m, n0);
    } else {
        let mut product = [0; 64];
        super::bignum_ksqr_32_64::bignum_ksqr_32_64(
            &mut product,
            x,
            &mut [MaybeUninit::uninit(); 72],
        );
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

/// `mont_mul` for a multiple of four words from eight, by `mulx`, `adcx`,
/// and `adox` given the proof of BMI2 and ADX.
fn mul4x(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64, adx: Option<HaveBmi2Adx>) {
    let k = m.len();
    assert!(k >= 8 && k.is_multiple_of(4) && z.len() == k && x.len() == k && y.len() == k);
    let (z, x, y, m) = (z.as_mut_ptr(), x.as_ptr(), y.as_ptr(), m.as_ptr());
    // SAFETY: `z`, `x`, `y`, and `m` are each `k` words, as each routine
    // reads and writes for such a `k`, and each reads `n0` as one word. The
    // token proves the CPU has the BMI2 and ADX `bn_mulx4x_mont` runs.
    unsafe {
        match adx {
            Some(_) => asm_call!(unsafe extern "sysv64" bn_mulx4x_mont(z, x, y, m, &n0, k)),
            None => asm_call!(unsafe extern "sysv64" bn_mul4x_mont(z, x, y, m, &n0, k)),
        }
    };
}

/// `mont_sqr` for a multiple of eight words, by `mulx`, `adcx`, and `adox`
/// given the proof of BMI2 and ADX.
fn sqr8x(z: &mut [u64], x: &[u64], m: &[u64], n0: u64, adx: Option<HaveBmi2Adx>) {
    let k = m.len();
    assert!(k >= 8 && k.is_multiple_of(8) && z.len() == k && x.len() == k);
    let mulx = adx.is_some().into();
    // SAFETY: `z`, `x`, and `m` are each `k` words, as `bn_sqr8x_mont` reads
    // and writes for such a `k`, and it reads `n0` as one word. It runs
    // `mulx`, `adcx`, and `adox` only if `mulx_adx_capable` is nonzero,
    // which the token proves the CPU has.
    unsafe {
        asm_call!(unsafe extern "sysv64" bn_sqr8x_mont(z.as_mut_ptr(), x.as_ptr(), mulx, m.as_ptr(), &n0, k))
    };
}

/// `mont_mul` for any width from two words.
fn nohw(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64], n0: u64) {
    let k = m.len();
    assert!(k >= 2 && z.len() == k && x.len() == k && y.len() == k);
    // SAFETY: `z`, `x`, `y`, and `m` are each `k` words, as
    // `bn_mul_mont_nohw` reads and writes for such a `k`, and it reads `n0`
    // as one word.
    unsafe {
        asm_call!(unsafe extern "sysv64" bn_mul_mont_nohw(z.as_mut_ptr(), x.as_ptr(), y.as_ptr(), m.as_ptr(), &n0, k))
    };
}

// The routines take the System V ABI on every OS, since their text is
// aws-lc's ELF and Mach-O flavors, which read their arguments from its
// registers. Each returns 1, which tells aws-lc's C it ran.

#[unsafe(naked)]
unsafe extern "sysv64" fn bn_mul4x_mont(
    rp: *mut u64,
    ap: *const u64,
    bp: *const u64,
    np: *const u64,
    n0: *const u64,
    num: usize,
) -> i32 {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_mul4x_mont.linux.s"),
        options(att_syntax)
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_mul4x_mont.apple.s"),
        options(att_syntax)
    );
}

/// Squares by `bn_sqrx8x_internal` if `mulx_adx_capable` is nonzero, and
/// otherwise by `bn_sqr8x_internal`.
#[unsafe(naked)]
unsafe extern "sysv64" fn bn_sqr8x_mont(
    rp: *mut u64,
    ap: *const u64,
    mulx_adx_capable: u64,
    np: *const u64,
    n0: *const u64,
    num: usize,
) -> i32 {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_sqr8x_mont.linux.s"),
        bn_sqr8x_internal = sym bn_sqr8x_internal,
        bn_sqrx8x_internal = sym bn_sqrx8x_internal,
        options(att_syntax)
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_sqr8x_mont.apple.s"),
        bn_sqr8x_internal = sym bn_sqr8x_internal,
        bn_sqrx8x_internal = sym bn_sqrx8x_internal,
        options(att_syntax)
    );
}

/// `bn_sqr8x_mont`'s squaring and reduction, which takes its arguments in
/// registers and a stack frame of that routine's making, so only it and
/// `bn_power5` call this.
#[unsafe(naked)]
pub(super) unsafe extern "sysv64" fn bn_sqr8x_internal() {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_sqr8x_internal.linux.s"),
        options(att_syntax)
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_sqr8x_internal.apple.s"),
        options(att_syntax)
    );
}

/// `bn_sqr8x_internal` by `mulx`, `adcx`, and `adox`, which only
/// `bn_sqr8x_mont` and `bn_powerx5` call, likewise.
#[unsafe(naked)]
pub(super) unsafe extern "sysv64" fn bn_sqrx8x_internal() {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_sqrx8x_internal.linux.s"),
        options(att_syntax)
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_sqrx8x_internal.apple.s"),
        options(att_syntax)
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn bn_mulx4x_mont(
    rp: *mut u64,
    ap: *const u64,
    bp: *const u64,
    np: *const u64,
    n0: *const u64,
    num: usize,
) -> i32 {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_mulx4x_mont.linux.s"),
        options(att_syntax)
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_mulx4x_mont.apple.s"),
        options(att_syntax)
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn bn_mul_mont_nohw(
    rp: *mut u64,
    ap: *const u64,
    bp: *const u64,
    np: *const u64,
    n0: *const u64,
    num: usize,
) -> i32 {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_mul_mont_nohw.linux.s"),
        options(att_syntax)
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/bn_mul_mont_nohw.apple.s"),
        options(att_syntax)
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::super::{bignum_montmul, bignum_mul, bignum_negmodinv};
    use super::*;
    use crate::test::bignum::{below, div_r, mod_mul_vectors, modulus, radix_words};

    /// Each aws-lc routine's `x * y / 2^(64k) mod m`, for `k` words each,
    /// with and without `mulx` where the CPU has BMI2 and ADX, and the
    /// Karatsuba routine's there: every one that takes the width, not only
    /// the one this CPU picks.
    fn products(x: &[u64], y: &[u64], m: &[u64]) -> Vec<(&'static str, Vec<u64>)> {
        let (k, adx, n0) = (m.len(), HaveBmi2Adx::check(), n0(m));
        let mut out = Vec::new();
        let mut run = |name, f: &dyn Fn(&mut [u64])| {
            let mut z = vec![0; k];
            f(&mut z);
            out.push((name, z));
        };
        if k >= 2 {
            run("nohw", &|z| nohw(z, x, y, m, n0));
        }
        if k >= 8 && k.is_multiple_of(4) {
            run("mul4x", &|z| mul4x(z, x, y, m, n0, None));
            if adx.is_some() {
                run("mulx4x", &|z| mul4x(z, x, y, m, n0, adx));
            }
        }
        if let (Some(_), 16 | 32) = (adx, k) {
            run("karatsuba_mul", &|z| karatsuba_mul(z, x, y, m, n0));
        }
        out
    }

    /// [`products`] of `x` by itself, and each squaring routine's.
    fn squares(x: &[u64], m: &[u64]) -> Vec<(&'static str, Vec<u64>)> {
        let (k, adx, n0) = (m.len(), HaveBmi2Adx::check(), n0(m));
        let mut out = products(x, x, m);
        let mut run = |name, f: &dyn Fn(&mut [u64])| {
            let mut z = vec![0; k];
            f(&mut z);
            out.push((name, z));
        };
        if k >= 8 && k.is_multiple_of(8) {
            run("sqr8x", &|z| sqr8x(z, x, m, n0, None));
            if adx.is_some() {
                run("sqrx8x", &|z| sqr8x(z, x, m, n0, adx));
            }
        }
        if let (Some(_), 16 | 32) = (adx, k) {
            run("karatsuba_sqr", &|z| karatsuba_sqr(z, x, m, n0));
        }
        out
    }

    /// `-m^-1 mod 2^64`.
    fn n0(m: &[u64]) -> u64 {
        let mut n0 = [0];
        bignum_negmodinv::bignum_negmodinv(&mut n0, &m[..1]);
        n0[0]
    }

    /// A modulus of a width some routine takes, and two values below it:
    /// of edge limbs, or the product of odd `r` and `s` with their top bits
    /// set, whose Montgomery product reaches `m` before the final
    /// subtraction.
    fn operands() -> impl Strategy<Value = (Vec<u64>, Vec<u64>, Vec<u64>)> {
        const WIDTHS: &[usize] = &[2, 3, 5, 8, 9, 12, 16, 17, 18, 24, 32, 33, 36, 48, 64];
        prop::sample::select(WIDTHS).prop_flat_map(|k| {
            let edges = modulus(64, k)
                .prop_flat_map(|m| (Just(m.clone()), below(64, m.clone()), below(64, m)));
            let product =
                (radix_words(64, k / 2), radix_words(64, k - k / 2)).prop_map(|(r, s)| {
                    let [r, s] = [r, s].map(|mut v| {
                        v[0] |= 1;
                        *v.last_mut().unwrap() |= 1 << 63;
                        v
                    });
                    let mut m = vec![0; r.len() + s.len()];
                    bignum_mul::bignum_mul(&mut m, &r, &s);
                    let [r, s] = [r, s].map(|mut v| {
                        v.resize(m.len(), 0);
                        v
                    });
                    (m, r, s)
                });
            prop_oneof![3 => edges, 1 => product]
        })
    }

    proptest! {
        // Every other test runs only the routines this CPU picks, so here
        // each is checked against s2n-bignum's generic `bignum_montmul`.
        #[test]
        fn matches_generic((m, x, y) in operands()) {
            let mut want = vec![0; m.len()];
            bignum_montmul::bignum_montmul(&mut want, &x, &y, &m);
            for (name, got) in products(&x, &y, &m) {
                prop_assert_eq!(&got, &want, "{}", name);
            }
            bignum_montmul::bignum_montmul(&mut want, &x, &x, &m);
            for (name, got) in squares(&x, &m) {
                prop_assert_eq!(&got, &want, "{} squaring", name);
            }
        }
    }

    #[test]
    fn aws_lc_mod_mul() {
        let mut ran = 0;
        for v in mod_mul_vectors() {
            let want = div_r(&v.want, &v.m);
            let got = match v.a == v.b {
                true => squares(&v.a, &v.m),
                false => products(&v.a, &v.b, &v.m),
            };
            for (name, got) in got {
                assert_eq!(got, want, "{name}, {}", v.at);
                ran += 1;
            }
        }
        assert!(ran > 0);
    }
}
