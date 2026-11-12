// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The steps of P-256's generator multiplication, using aws-lc's
//! `p256-x86_64-asm` routines, which aws-lc's `ecp_nistz256_point_mul_base`
//! runs over its 7-bit generator table.
//!
//! The assembly is aws-lc's, imported by `admin/import-aws-lc`. The row scan
//! reads all 64 points of a row and masks off all but one, and the mixed
//! addition selects its special cases with masks, so neither branches on or
//! indexes by its inputs. Neither is formally verified: their correctness
//! rests on their use and testing in OpenSSL, BoringSSL, and aws-lc, and on
//! rind's tests of them against s2n-bignum's verified arithmetic,
//! Wycheproof, and aws-lc-rs.

use super::cpu::{HaveAvx2, HaveBmi2Adx};

/// One row of the generator table: 64 affine points with Montgomery
/// coordinates, `x` then `y`, each 4 little-endian words. The scans load it
/// with `movdqa` and `vmovdqa`.
#[repr(C, align(64))]
pub(crate) struct P256GeneratorRow(pub(crate) [u64; 512]);

impl core::ops::Deref for P256GeneratorRow {
    type Target = [u64; 512];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Writes `row`'s point `index - 1` to `out`, or zeros for an `index` of 0 or
/// above 64, reading every point.
///
/// `index` is secret, so not even a debug build asserts on it.
pub(crate) fn p256_select_w7(out: &mut [u64; 8], row: &P256GeneratorRow, index: u8) {
    // SAFETY: `out` is one writable point and `row` 64 readable points, as
    // aligned as the routines load them. The AVX2 routine runs only where the
    // token proves AVX2, and the other needs only SSE2.
    unsafe {
        match HaveAvx2::check() {
            Some(_) => {
                asm_call!(unsafe extern "sysv64" ecp_nistz256_avx2_select_w7(out, row, index.into()))
            }
            None => {
                asm_call!(unsafe extern "sysv64" ecp_nistz256_select_w7(out, row, index.into()))
            }
        }
    }
}

/// Adds the affine `p2` to the Jacobian `p1`, both in Montgomery form.
///
/// Either may be infinity: `p1` with a zero `z`, `p2` as all zeros. They must
/// not be the same point, which this does not double.
pub(crate) fn p256_point_add_affine(p1: &mut [u64; 12], p2: &[u64; 8]) {
    let p1 = core::ptr::from_mut(p1);
    // SAFETY: `p1` is one readable and writable Jacobian point, which the
    // routines read in full before writing, as aws-lc's in-place calls rely
    // on, and `p2` one readable affine point; the routines load them
    // unaligned. The BMI2 and ADX routine runs only where the token proves
    // both, and the other needs only SSE2.
    unsafe {
        match HaveBmi2Adx::check() {
            Some(_) => asm_call!(unsafe extern "sysv64" ecp_nistz256_point_add_affinex(p1, p1, p2)),
            None => asm_call!(unsafe extern "sysv64" ecp_nistz256_point_add_affine(p1, p1, p2)),
        }
    }
}

/// aws-lc's `.Lpoly`, the field prime, as the multiplications load it.
#[repr(C, align(16))]
struct Poly([u64; 4]);

/// aws-lc's `.LOne`, `.LTwo`, and `.LThree`, the scans' counters, as aligned
/// as the AVX2 scan loads them.
#[repr(C, align(32))]
struct One([u32; 24]);

/// aws-lc's `.LONE_mont`, one in Montgomery form, which the addition masks
/// with `pand`. It runs on through `.Lord` and `.LordK`, which the import
/// keeps but these routines never read.
#[repr(C, align(16))]
struct OneMont([u64; 9]);

static POLY: Poly = Poly(include!("aws_lc/p256-x86_64-asm.poly.rs"));
static ONE: One = One(include!("aws_lc/p256-x86_64-asm.One.rs"));
static ONE_MONT: OneMont = OneMont(include!("aws_lc/p256-x86_64-asm.ONE_mont.rs"));

/// Defines a naked function running an imported routine, which reaches its
/// tables and helpers through the `sym` operands listed. Each takes the System
/// V ABI on every OS, since its text is aws-lc's ELF and Mach-O flavors.
macro_rules! p256_routine {
    ($name:ident($($arg:ident: $ty:ty),*) { $($op:ident = $sym:ident),* }) => {
        #[unsafe(naked)]
        unsafe extern "sysv64" fn $name($($arg: $ty),*) {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".linux.s"))
                $(, $op = sym $sym)*,
                options(att_syntax),
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("aws_lc/", stringify!($name), ".apple.s"))
                $(, $op = sym $sym)*,
                options(att_syntax),
            );
        }
    };
}

p256_routine!(ecp_nistz256_select_w7(out: *mut [u64; 8], row: *const P256GeneratorRow, index: u32) {
    One = ONE
});
p256_routine!(ecp_nistz256_avx2_select_w7(out: *mut [u64; 8], row: *const P256GeneratorRow, index: u32) {
    One = ONE
});
p256_routine!(ecp_nistz256_point_add_affine(r: *mut [u64; 12], a: *const [u64; 12], b: *const [u64; 8]) {
    ONE_mont = ONE_MONT,
    ecp_nistz256_mul_montq = ecp_nistz256_mul_montq,
    ecp_nistz256_sqr_montq = ecp_nistz256_sqr_montq,
    ecp_nistz256_sub_fromq = ecp_nistz256_sub_fromq,
    ecp_nistz256_subq = ecp_nistz256_subq
});
p256_routine!(ecp_nistz256_point_add_affinex(r: *mut [u64; 12], a: *const [u64; 12], b: *const [u64; 8]) {
    ONE_mont = ONE_MONT,
    ecp_nistz256_mul_montx = ecp_nistz256_mul_montx,
    ecp_nistz256_sqr_montx = ecp_nistz256_sqr_montx,
    ecp_nistz256_sub_fromx = ecp_nistz256_sub_fromx,
    ecp_nistz256_subx = ecp_nistz256_subx
});

// The routines' helpers, which pass their arguments in registers of their
// own choosing rather than by the C ABI, so only the routines call them.
p256_routine!(ecp_nistz256_mul_montq() { poly = POLY });
p256_routine!(ecp_nistz256_sqr_montq() { poly = POLY });
p256_routine!(ecp_nistz256_sub_fromq() {});
p256_routine!(ecp_nistz256_subq() {});
p256_routine!(ecp_nistz256_mul_montx() { poly = POLY });
p256_routine!(ecp_nistz256_sqr_montx() { poly = POLY });
p256_routine!(ecp_nistz256_sub_fromx() {});
p256_routine!(ecp_nistz256_subx() {});

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::super::adx_mux::tests::Rng;
    use super::*;
    use crate::low::generic::limb64::p256;
    use crate::test::bignum::below;

    // aws-lc's point additions whose `B` or `A` is affine, which rind's
    // routine takes, but for the same point twice, which it does not double.
    // The sums are checked against the affine results through fiat-crypto's
    // field arithmetic, for whichever twin this CPU picks.
    #[test]
    fn aws_lc_point_add_affine() {
        use fiat_crypto::p256_64::{
            fiat_p256_montgomery_domain_field_element as Fe, fiat_p256_mul, fiat_p256_square,
        };

        let one = Fe(include!("aws_lc/p256-x86_64-asm.ONE_mont.rs")[..4]
            .try_into()
            .unwrap());
        let mul = |a: &Fe, b: &Fe| {
            let mut out = Fe([0; 4]);
            fiat_p256_mul(&mut out, a, b);
            out
        };
        let mut ran = 0;
        for test in
            crate::test::file_test::tests("aws-lc/crypto/fipsmodule/ec/p256-nistz_tests.txt")
        {
            if test.str("Test") != "PointAdd" {
                continue;
            }
            let fe = |name: &str| {
                let bytes = test.bytes(name);
                Fe(core::array::from_fn(|i| {
                    u64::from_be_bytes(bytes[24 - 8 * i..][..8].try_into().unwrap())
                }))
            };
            let point = |p: &str| {
                [
                    fe(&format!("{p}.X")),
                    fe(&format!("{p}.Y")),
                    fe(&format!("{p}.Z")),
                ]
            };
            let (result_x, result_y) = (fe("Result.X"), fe("Result.Y"));
            for (jacobian, affine) in [(point("A"), point("B")), (point("B"), point("A"))] {
                let affine_xy = match affine[2].0 {
                    z if z == one.0 => [affine[0].0, affine[1].0].concat(),
                    [0, 0, 0, 0] => vec![0; 8],
                    _ => continue,
                };
                if jacobian[2].0 == one.0
                    && jacobian[..2]
                        .iter()
                        .map(|f| f.0)
                        .eq(affine[..2].iter().map(|f| f.0))
                    && affine_xy != [0; 8]
                {
                    continue;
                }
                let mut p1: [u64; 12] = [jacobian[0].0, jacobian[1].0, jacobian[2].0]
                    .concat()
                    .try_into()
                    .unwrap();
                p256_point_add_affine(&mut p1, &affine_xy.try_into().unwrap());
                let (x, y, z) = (
                    Fe(p1[..4].try_into().unwrap()),
                    Fe(p1[4..8].try_into().unwrap()),
                    Fe(p1[8..].try_into().unwrap()),
                );
                if result_x.0 == [0; 4] && result_y.0 == [0; 4] {
                    assert_eq!(z.0, [0; 4], "{test}");
                } else {
                    // An all-zero output would pass the coordinate checks below.
                    assert_ne!(z.0, [0; 4], "{test}");
                    let mut z2 = Fe([0; 4]);
                    fiat_p256_square(&mut z2, &z);
                    assert_eq!(x.0, mul(&result_x, &z2).0, "{test}");
                    assert_eq!(y.0, mul(&result_y, &mul(&z2, &z)).0, "{test}");
                }
                ran += 1;
            }
        }
        assert!(ran > 0);
    }

    // The other tests run only the twin this CPU picks, so each pair is
    // checked against each other here, where the CPU runs both, and the
    // mixed addition against s2n-bignum's verified one.
    #[test]
    fn twins_agree() {
        let mut rng = Rng(0x243f_6a88_85a3_08d3);
        let mut row = P256GeneratorRow([0; 512]);
        for word in row.0.iter_mut() {
            *word = rng.next();
        }

        if HaveAvx2::check().is_some() {
            for index in 0..=255 {
                let (mut sse2, mut avx2) = ([1; 8], [1; 8]);
                // SAFETY: as in `p256_select_w7`, on a CPU with AVX2.
                unsafe {
                    asm_call!(unsafe extern "sysv64" ecp_nistz256_select_w7(&mut sse2, &row, index));
                    asm_call!(unsafe extern "sysv64" ecp_nistz256_avx2_select_w7(&mut avx2, &row, index));
                }
                assert_eq!(sse2, avx2);
                let want = match index {
                    0 | 65.. => [0; 8],
                    i => row.0[(i as usize - 1) * 8..][..8].try_into().unwrap(),
                };
                assert_eq!(sse2, want);
            }
        }

        if HaveBmi2Adx::check().is_some() {
            // The addition is straight-line field arithmetic, so off-curve
            // points exercise it as well as real ones, and a zero `z` or
            // `p2` its infinity cases.
            for i in 0..256 {
                let mut p1: [u64; 12] = rng.field(255);
                let mut p2: [u64; 8] = rng.field(255);
                match i % 8 {
                    0 => p1[8..].fill(0),
                    1 => p2.fill(0),
                    _ => {}
                }
                let (mut mulq, mut mulx) = ([0; 12], [0; 12]);
                // SAFETY: as in `p256_point_add_affine`, on a CPU with BMI2
                // and ADX.
                unsafe {
                    asm_call!(unsafe extern "sysv64" ecp_nistz256_point_add_affine(&mut mulq, &p1, &p2));
                    asm_call!(unsafe extern "sysv64" ecp_nistz256_point_add_affinex(&mut mulx, &p1, &p2));
                }
                assert_eq!(mulq, mulx);
            }
        }

        // `p1` is not at infinity, which s2n-bignum's addition requires.
        for _ in 0..256 {
            let mut p1: [u64; 12] = rng.field(255);
            let p2: [u64; 8] = rng.field(255);
            p1[8] |= 1;
            let mut s2n = [0; 12];
            super::super::adx_mux::p256_montjmixadd(&mut s2n, &p1, &p2);
            p256_point_add_affine(&mut p1, &p2);
            assert_eq!(p1, s2n);
        }
    }

    /// A field element of edge limbs below the prime, `p - 1` and its
    /// neighbours among them.
    fn fe() -> impl Strategy<Value = [u64; 4]> {
        below(64, POLY.0.to_vec()).prop_map(|x| x.try_into().unwrap())
    }

    /// A Jacobian `p1` and an affine `p2` of edge coordinates, and each case
    /// the addition masks or meets: either at infinity, and `p1` as `p2`
    /// or its negation, scaled by its `z`.
    fn points() -> impl Strategy<Value = ([u64; 12], [u64; 8])> {
        ([fe(), fe(), fe()], [fe(), fe()], 0..6u8).prop_map(|([x1, y1, z], [x2, y2], case)| {
            let mul = |a: &[u64; 4], b: &[u64; 4]| {
                let mut out = [0; 4];
                p256::bignum_montmul_p256(&mut out, a, b);
                out
            };
            let (x1, y1) = match case {
                2 | 3 => {
                    let z2 = mul(&z, &z);
                    let y = mul(&y2, &mul(&z2, &z));
                    let mut neg = [0; 4];
                    p256::bignum_neg_p256(&mut neg, &y);
                    (mul(&x2, &z2), if case == 2 { y } else { neg })
                }
                _ => (x1, y1),
            };
            let z = if case == 0 { [0; 4] } else { z };
            let p2 = if case == 1 { [[0; 4]; 2] } else { [x2, y2] };
            (
                [x1, y1, z].concat().try_into().unwrap(),
                p2.concat().try_into().unwrap(),
            )
        })
    }

    proptest! {
        // Each twin the CPU runs against the portable addition, which takes
        // the same formulas, but for `p2` at infinity, which it does not
        // take and which leaves `p1` as it is.
        #[test]
        fn point_add_affine_edges((p1, p2) in points()) {
            let mut want = p1;
            if p2 != [0; 8] {
                p256::p256_montjmixadd(&mut want, &p1, &p2);
            }
            let mut got = [0; 12];
            // SAFETY: as in `p256_point_add_affine`, which needs only SSE2.
            unsafe { ecp_nistz256_point_add_affine(&mut got, &p1, &p2) };
            prop_assert_eq!(got, want);
            if HaveBmi2Adx::check().is_some() {
                // SAFETY: as above, on a CPU with BMI2 and ADX.
                unsafe { ecp_nistz256_point_add_affinex(&mut got, &p1, &p2) };
                prop_assert_eq!(got, want, "mulx");
            }
        }
    }
}
