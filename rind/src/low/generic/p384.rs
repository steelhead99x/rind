// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The s2n-bignum routines `mid::p384` uses, with their contracts, over
//! the parent module's limbs: `p384_mul`'s Montgomery multiplication and
//! squaring, and fiat-crypto's P-384 field and group order arithmetic for
//! the rest.
//!
//! fiat-crypto proves each operation correct, and emits it as straight-line
//! code with no secret-dependent branch or index.  The rest composes those: the point formulas repeat s2n-bignum's operation
//! sequences, so results match it word for word; inversion is Fermat's
//! little theorem, raising to a public exponent by a fixed sequence of
//! squarings and multiplications; and range reduction is one
//! conditional subtraction, as every input is below 2^384, which is less
//! than twice either modulus.
//!
//! Arithmetic on secrets wraps: the bounds rule out overflow, and a debug
//! build's overflow check would branch on secret values.

pub(super) use super::fiat_p384::fiat_p384_montgomery_domain_field_element as Fe;
pub(super) use super::fiat_p384_scalar::fiat_p384_scalar_montgomery_domain_field_element as Fs;
use super::p384_mul::{fe_mul, fe_sqr, fs_mul, fs_sqr};
use super::{Limb, Wide, fiat_p384 as fp, fiat_p384_scalar as fs};

/// Limbs in a field element.
const LIMBS: usize = (384 / Limb::BITS) as usize;

/// z := x * y / 2^384 mod p_384
pub(crate) fn bignum_montmul_p384(z: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]) {
    *z = join(&fe_mul(&fe(x), &fe(y)).0);
}

/// z := x^2 / 2^384 mod p_384
pub(crate) fn bignum_montsqr_p384(z: &mut [u64; 6], x: &[u64; 6]) {
    *z = join(&fe_sqr(&fe(x)).0);
}

/// z := (x + y) mod p_384, assuming x and y reduced
pub(crate) fn bignum_add_p384(z: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]) {
    *z = join(&fe_add(&fe(x), &fe(y)).0);
}

/// z := (-x) mod p_384, assuming x reduced
pub(crate) fn bignum_neg_p384(z: &mut [u64; 6], x: &[u64; 6]) {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p384_opp(&mut r, &fe(x));
    *z = join(&r.0);
}

/// z := (2^384 * x) mod p_384
pub(crate) fn bignum_tomont_p384(z: &mut [u64; 6], x: &[u64; 6]) {
    *z = join(&fe_to_mont(&reduce(split(x), &split(&P))).0);
}

/// z := (x / 2^384) mod p_384, assuming x reduced
pub(crate) fn bignum_demont_p384(z: &mut [u64; 6], x: &[u64; 6]) {
    let mut r = fp::fiat_p384_non_montgomery_domain_field_element([0; LIMBS]);
    fp::fiat_p384_from_montgomery(&mut r, &fe(x));
    *z = join(&r.0);
}

/// z := x^-1 mod p_384, or zero if x is zero mod p_384
pub(crate) fn bignum_inv_p384(z: &mut [u64; 6], x: &[u64; 6]) {
    let x = fe_to_mont(&reduce(split(x), &split(&P)));
    bignum_demont_p384(z, &join(&fe_invert(&x).0));
}

/// Viewing table as rows of 12 words width, copy the 12 words at
/// table[index - 1] into z.  If `index` is zero or past the last row,
/// `z` is set to zero (ie, the affine point at infinity).
pub(crate) fn bignum_aff_point_select_p384(z: &mut [u64; 12], table: &[u64], index: u8) {
    row_select(z, table, index);
}

/// Viewing table as rows of 18 words width, copy the 18 words at
/// table[index - 1] into z.  If `index` is zero or past the last row,
/// `z` is set to zero (ie, a jacobian point at infinity).
pub(crate) fn bignum_jac_point_select_p384(z: &mut [u64; 18], table: &[u64], index: u8) {
    row_select(z, table, index);
}

fn row_select<const N: usize>(z: &mut [u64; N], table: &[u64], index: u8) {
    *z = [0; N];
    let (rows, _) = table.as_chunks::<N>();
    for (i, row) in (1u64..).zip(rows) {
        let mask = !mask_nonzero(i ^ u64::from(index));
        for (z, w) in z.iter_mut().zip(row) {
            *z |= w & mask;
        }
    }
}

/// p3 := p1 + p2, as Jacobian points over p_384 with Montgomery coordinates.
///
/// A point with a zero z is the point at infinity.  The result is
/// unspecified when p1 and p2 are the same point.
pub(crate) fn p384_montjadd(p3: &mut [u64; 18], p1: &[u64; 18], p2: &[u64; 18]) {
    let [x1, y1, z1] = coords(p1);
    let [x2, y2, z2] = coords(p2);

    let z1sq = fe_sqr(&z1);
    let z2sq = fe_sqr(&z2);
    let y1a = fe_mul(&z2sq, &fe_mul(&z2, &y1));
    let y2a = fe_mul(&z1sq, &fe_mul(&z1, &y2));
    let x1a = fe_mul(&z2sq, &x1);
    let x2a = fe_mul(&z1sq, &x2);

    let xd = fe_sub(&x2a, &x1a);
    let yd = fe_sub(&y2a, &y1a);
    let zz = fe_sqr(&xd);
    let ww = fe_sqr(&yd);
    let zzx1 = fe_mul(&zz, &x1a);
    let zzx2 = fe_mul(&zz, &x2a);

    let x3 = fe_sub(&fe_sub(&ww, &zzx1), &zzx2);
    let t1 = fe_mul(&fe_sub(&zzx2, &zzx1), &y1a);
    let y3 = fe_sub(&fe_mul(&yd, &fe_sub(&zzx1, &x3)), &t1);
    let z3 = fe_mul(&fe_mul(&xd, &z1), &z2);

    // An input at infinity makes the result the other input.
    let z1_nonzero = nonzero(&z1);
    let z2_nonzero = nonzero(&z2);
    let pick = |p1: &Fe, p2: &Fe, sum: &Fe| {
        let if_z1_nonzero = select(z2_nonzero, p1, sum);
        let if_z1_zero = select(z2_nonzero, sum, p2);
        select(z1_nonzero, &if_z1_zero, &if_z1_nonzero)
    };
    *p3 = point(
        &pick(&x1, &x2, &x3),
        &pick(&y1, &y2, &y3),
        &pick(&z1, &z2, &z3),
    );
}

/// p3 := p1 + p2, for a Jacobian p1 and an affine p2 (whose z is
/// implicitly one), over p_384 with Montgomery coordinates.
///
/// A p1 with a zero z is the point at infinity; p2 cannot be.  The result
/// is unspecified when p1 and p2 are the same point.
pub(crate) fn p384_montjmixadd(p3: &mut [u64; 18], p1: &[u64; 18], p2: &[u64; 12]) {
    let [x1, y1, z1] = coords(p1);
    let (xy2, _) = p2.as_chunks::<6>();
    let (x2, y2) = (fe(&xy2[0]), fe(&xy2[1]));

    let z1sq = fe_sqr(&z1);
    let y2a = fe_mul(&z1sq, &fe_mul(&z1, &y2));
    let x2a = fe_mul(&z1sq, &x2);

    let xd = fe_sub(&x2a, &x1);
    let yd = fe_sub(&y2a, &y1);
    let zz = fe_sqr(&xd);
    let ww = fe_sqr(&yd);
    let zzx1 = fe_mul(&zz, &x1);
    let zzx2 = fe_mul(&zz, &x2a);

    let x3 = fe_sub(&fe_sub(&ww, &zzx1), &zzx2);
    let t1 = fe_mul(&fe_sub(&zzx2, &zzx1), &y1);
    let y3 = fe_sub(&fe_mul(&yd, &fe_sub(&zzx1, &x3)), &t1);
    let z3 = fe_mul(&xd, &z1);

    // p1 at infinity makes the result p2, with a z of one.
    let mut one = Fe([0; LIMBS]);
    fp::fiat_p384_set_one(&mut one);
    let z1_nonzero = nonzero(&z1);
    *p3 = point(
        &select(z1_nonzero, &x2, &x3),
        &select(z1_nonzero, &y2, &y3),
        &select(z1_nonzero, &one, &z3),
    );
}

/// p3 := 2 * p1, as a Jacobian point over p_384 with Montgomery coordinates.
pub(crate) fn p384_montjdouble(p3: &mut [u64; 18], p1: &[u64; 18]) {
    let [x, y, z] = coords(p1);

    let z2 = fe_sqr(&z);
    let y2 = fe_sqr(&y);
    // x^2 - z^4, which is (x + z^2) * (x - z^2)
    let x2p = fe_mul(&fe_add(&x, &z2), &fe_sub(&x, &z2));
    let x4p = fe_sqr(&x2p);
    let xy2 = fe_mul(&x, &y2);
    let y4 = fe_sqr(&y2);

    // 12 * xy2 - 9 * x4p
    let xy2_4 = fe_double(&fe_double(&xy2));
    let x4p_8 = fe_double(&fe_double(&fe_double(&x4p)));
    let d = fe_sub(&fe_add(&xy2_4, &fe_double(&xy2_4)), &fe_add(&x4p_8, &x4p));

    // (y + z)^2 - z^2 - y^2, which is 2 * y * z
    let z3 = fe_sub(&fe_sub(&fe_sqr(&fe_add(&y, &z)), &z2), &y2);
    let x3 = fe_sub(&xy2_4, &d);
    let dx2 = fe_mul(&d, &x2p);
    let y4_8 = fe_double(&fe_double(&fe_double(&y4)));
    let y3 = fe_sub(&fe_add(&fe_double(&dx2), &dx2), &y4_8);

    *p3 = point(&x3, &y3, &z3);
}

/// z := x mod n_384
pub(crate) fn bignum_mod_n384(z: &mut [u64; 6], x: &[u64; 6]) {
    *z = join(&reduce(split(x), &split(&N)));
}

// The routines below take the modulus, as s2n-bignum's are generic over
// it.  `mid::p384` passes only n_384, the one modulus this backend has
// verified arithmetic for, so any other is refused.

/// z := x * y / 2^384 mod m, for m = n_384
pub(crate) fn bignum_montmul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    let r = fs_mul(&fs(x), &fs(y));
    z.copy_from_slice(&join(&r.0));
}

/// z := x / 2^384 mod m, for m = n_384, assuming x reduced
pub(crate) fn bignum_demont(z: &mut [u64], x: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    let mut r = fs::fiat_p384_scalar_non_montgomery_domain_field_element([0; LIMBS]);
    fs::fiat_p384_scalar_from_montgomery(&mut r, &fs(x));
    z.copy_from_slice(&join(&r.0));
}

/// z := (x + y) mod m, for m = n_384, assuming x and y reduced
pub(crate) fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    let mut r = Fs([0; LIMBS]);
    fs::fiat_p384_scalar_add(&mut r, &fs(x), &fs(y));
    z.copy_from_slice(&join(&r.0));
}

/// z := a^-1 mod b, for b = n_384, or zero if a is zero mod n_384
///
/// `_t` is s2n-bignum's scratch space, which this does not need.
pub(crate) fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], _t: &mut [u64]) {
    assert_eq!(b, N);
    let a = reduce(split(a.try_into().unwrap()), &split(&N));
    let mut a_mont = Fs([0; LIMBS]);
    fs::fiat_p384_scalar_to_montgomery(
        &mut a_mont,
        &fs::fiat_p384_scalar_non_montgomery_domain_field_element(a),
    );
    let r = fs_pow(&a_mont, &N_MINUS_2);
    bignum_demont(z, &join(&r.0), b);
}

/// z := 2^768 mod m, for m = n_384
// Checks the constant against s2n-bignum, which armv7 lacks.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
pub(crate) fn bignum_montifier(z: &mut [u64], m: &[u64], _t: &mut [u64]) {
    assert_eq!(m, N);
    // to_montgomery multiplies by 2^384, so this is 2^384 * (2^384 mod n).
    let mut one = Fs([0; LIMBS]);
    fs::fiat_p384_scalar_set_one(&mut one);
    let mut r = Fs([0; LIMBS]);
    fs::fiat_p384_scalar_to_montgomery(
        &mut r,
        &fs::fiat_p384_scalar_non_montgomery_domain_field_element(one.0),
    );
    z.copy_from_slice(&join(&r.0));
}

/// z := x_if_p if p is nonzero, else y_if_not_p
pub(crate) fn bignum_mux(p: u64, z: &mut [u64], x_if_p: &[u64], y_if_not_p: &[u64]) {
    let mask = mask_nonzero(p);
    for ((z, x), y) in z.iter_mut().zip(x_if_p).zip(y_if_not_p) {
        *z = (x & mask) | (y & !mask);
    }
}

/// `x^(p - 2)`, which is `x^-1` for a nonzero `x`, by an addition chain
/// of 385 squarings and 14 multiplications.
fn fe_invert(x: &Fe) -> Fe {
    let sqr_n = |x: &Fe, n: usize| (0..n).fold(*x, |acc, _| fe_sqr(&acc));

    // x_k is x^(2^k - 1), whose exponent is k one bits.
    let x2 = fe_mul(&fe_sqr(x), x);
    let x3 = fe_mul(&fe_sqr(&x2), x);
    let x6 = fe_mul(&sqr_n(&x3, 3), &x3);
    let x12 = fe_mul(&sqr_n(&x6, 6), &x6);
    let x15 = fe_mul(&sqr_n(&x12, 3), &x3);
    let x30 = fe_mul(&sqr_n(&x15, 15), &x15);
    let x32 = fe_mul(&sqr_n(&x30, 2), &x2);
    let x60 = fe_mul(&sqr_n(&x30, 30), &x30);
    let x120 = fe_mul(&sqr_n(&x60, 60), &x60);
    let x240 = fe_mul(&sqr_n(&x120, 120), &x120);
    let x255 = fe_mul(&sqr_n(&x240, 15), &x15);

    // p - 2 is, from the top: 255 ones, a zero, 32 ones, 64 zeros, 30
    // ones, a zero, and a one.
    let r = fe_mul(&sqr_n(&x255, 33), &x32);
    let r = fe_mul(&sqr_n(&r, 94), &x30);
    fe_mul(&sqr_n(&r, 2), x)
}

/// `x^e` mod n_384 for a public exponent `e`, by a fixed 4-bit window.
///
/// The exponent picks the table entries, so it must not be secret.
fn fs_pow(x: &Fs, e: &[u64; 6]) -> Fs {
    let mut one = Fs([0; LIMBS]);
    fs::fiat_p384_scalar_set_one(&mut one);
    let mut table = [one; 16];
    for i in 1..table.len() {
        table[i] = fs_mul(&table[i - 1], x);
    }

    let mut acc = one;
    for word in e.iter().rev() {
        for shift in (0..64).step_by(4).rev() {
            for _ in 0..4 {
                acc = fs_sqr(&acc);
            }
            acc = fs_mul(&acc, &table[((word >> shift) & 0xf) as usize]);
        }
    }
    acc
}

/// `x - m` if that does not borrow, else `x`.
///
/// This fully reduces any `x < 2 * m`.
pub(super) fn reduce(x: [Limb; LIMBS], m: &[Limb; LIMBS]) -> [Limb; LIMBS] {
    subtract_if_above(&x, 0, m)
}

fn fe(x: &[u64; 6]) -> Fe {
    Fe(split(x))
}

fn fs(x: &[u64]) -> Fs {
    Fs(split(x.try_into().unwrap()))
}

fn fe_add(x: &Fe, y: &Fe) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p384_add(&mut r, x, y);
    r
}

fn fe_double(x: &Fe) -> Fe {
    fe_add(x, x)
}

fn fe_sub(x: &Fe, y: &Fe) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p384_sub(&mut r, x, y);
    r
}

fn fe_to_mont(x: &[Limb; LIMBS]) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p384_to_montgomery(
        &mut r,
        &fp::fiat_p384_non_montgomery_domain_field_element(*x),
    );
    r
}

/// `x + 2^384 top - m` if that is not negative, else `x`, for `x + 2^384
/// top` below 2m.
pub(super) fn subtract_if_above(x: &[Limb; LIMBS], top: Limb, m: &[Limb; LIMBS]) -> [Limb; LIMBS] {
    let (diff, borrow) = sub(x, m);
    let mut r = [0; LIMBS];
    fp::fiat_p384_selectznz(&mut r, opaque(borrow & !(top as u8)), &diff, x);
    r
}

/// `x - y` and its borrow out.
fn sub(x: &[Limb; LIMBS], y: &[Limb; LIMBS]) -> ([Limb; LIMBS], u8) {
    let mut diff = [0; LIMBS];
    let mut borrow = 0;
    for ((d, x), y) in diff.iter_mut().zip(x).zip(y) {
        let t = Wide::from(*x)
            .wrapping_sub(Wide::from(*y))
            .wrapping_sub(borrow);
        *d = t as Limb;
        borrow = t >> (Wide::BITS - 1);
    }
    (diff, borrow as u8)
}

/// 1 if `x` is nonzero, else 0.
fn nonzero(x: &Fe) -> u8 {
    let mut any = 0;
    fp::fiat_p384_nonzero(&mut any, &x.0);
    opaque(((any | any.wrapping_neg()) >> (Limb::BITS - 1)) as u8)
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select(flag: u8, if_zero: &Fe, if_nonzero: &Fe) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p384_selectznz(&mut r.0, flag, &if_zero.0, &if_nonzero.0);
    r
}

/// All ones if `x` is nonzero, else zero.
fn mask_nonzero(x: u64) -> u64 {
    opaque(((x | x.wrapping_neg()) >> 63).wrapping_neg())
}

/// Hides that `x` is a flag or mask, so the optimiser cannot turn the
/// arithmetic selecting with it into a secret-dependent branch or cmov.
fn opaque<T>(x: T) -> T {
    core::hint::black_box(x)
}

fn coords(p: &[u64; 18]) -> [Fe; 3] {
    let (words, _) = p.as_chunks::<6>();
    [fe(&words[0]), fe(&words[1]), fe(&words[2])]
}

fn point(x: &Fe, y: &Fe, z: &Fe) -> [u64; 18] {
    let mut r = [0u64; 18];
    let (words, _) = r.as_chunks_mut::<6>();
    words[0] = join(&x.0);
    words[1] = join(&y.0);
    words[2] = join(&z.0);
    r
}

/// `x`'s limbs, low first.
pub(super) fn split(x: &[u64; 6]) -> [Limb; LIMBS] {
    core::array::from_fn(|i| (x[i * 6 / LIMBS] >> (Limb::BITS as usize * i % 64)) as Limb)
}

/// The words of `x`'s limbs, low first.
fn join(x: &[Limb; LIMBS]) -> [u64; 6] {
    let mut r = [0u64; 6];
    for (i, limb) in x.iter().enumerate() {
        r[i * 6 / LIMBS] |= u64::from(*limb) << (Limb::BITS as usize * i % 64);
    }
    r
}

/// p_384, as little-endian words.
pub(super) const P: [u64; 6] = [
    0x0000_0000_ffff_ffff,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

/// n_384, the group order, as little-endian words.
pub(crate) const N: [u64; 6] = [
    0xecec_196a_ccc5_2973,
    0x581a_0db2_48b0_a77a,
    0xc763_4d81_f437_2ddf,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

const N_MINUS_2: [u64; 6] = [
    0xecec_196a_ccc5_2971,
    0x581a_0db2_48b0_a77a,
    0xc763_4d81_f437_2ddf,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

/// Checks each routine word for word against s2n-bignum's.
///
/// Inputs that are secret in `mid::p384` are marked secret, so under
/// `admin/ctgrind` these also check each routine is constant time in them.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::low;
    use crate::low::ct::{into_public, into_secret};

    /// Any 384-bit value, biased towards the moduli's edges.
    fn raw() -> impl Strategy<Value = [u64; 6]> {
        prop_oneof![
            8 => any::<[u64; 6]>(),
            1 => prop_oneof![
                Just([0; 6]),
                Just([1, 0, 0, 0, 0, 0]),
                Just(add_small(P, -1)),
                Just(P),
                Just(add_small(P, 1)),
                Just(add_small(N, -1)),
                Just(N),
                Just(add_small(N, 1)),
                Just([u64::MAX; 6]),
            ],
        ]
    }

    /// A field element below p, including 0, 1, and p - 1.
    fn field() -> impl Strategy<Value = [u64; 6]> {
        prop_oneof![
            8 => any::<[u64; 6]>().prop_map(|x| {
                let mut r = [0; 6];
                low::bignum_tomont_p384(&mut r, &x);
                r
            }),
            1 => prop_oneof![
                Just([0; 6]),
                Just([1, 0, 0, 0, 0, 0]),
                Just(add_small(P, -1)),
            ],
        ]
    }

    /// `x + d`, for a low word that neither carries nor borrows.
    fn add_small(mut x: [u64; 6], d: i64) -> [u64; 6] {
        x[0] = x[0].checked_add_signed(d).unwrap();
        x
    }

    /// A scalar below n, including 0, 1, and n - 1.
    fn scalar() -> impl Strategy<Value = [u64; 6]> {
        raw().prop_map(|x| {
            let mut r = [0; 6];
            low::bignum_mod_n384(&mut r, &x);
            r
        })
    }

    /// A Jacobian point: a multiple of G with a random z, or infinity.
    fn point() -> impl Strategy<Value = [u64; 18]> {
        let multiple = (0..64u32, field()).prop_map(|(doublings, lambda)| {
            let mut p = GENERATOR;
            for _ in 0..doublings {
                let q = p;
                low::p384_montjdouble(&mut p, &q);
            }
            rescale(&p, &lambda)
        });
        let infinity = (field(), field()).prop_map(|(x, y)| {
            let mut p = [0; 18];
            p[..6].copy_from_slice(&x);
            p[6..12].copy_from_slice(&y);
            p
        });
        prop_oneof![9 => multiple, 1 => infinity]
    }

    /// (x * l^2, y * l^3, z * l), the same point unless l is zero.
    fn rescale(p: &[u64; 18], lambda: &[u64; 6]) -> [u64; 18] {
        let mut l2 = [0; 6];
        low::bignum_montsqr_p384(&mut l2, lambda);
        let mut l3 = [0; 6];
        low::bignum_montmul_p384(&mut l3, &l2, lambda);
        let mut r = [0; 18];
        let (out, _) = r.as_chunks_mut::<6>();
        let (coords, _) = p.as_chunks::<6>();
        low::bignum_montmul_p384(&mut out[0], &coords[0], &l2);
        low::bignum_montmul_p384(&mut out[1], &coords[1], &l3);
        low::bignum_montmul_p384(&mut out[2], &coords[2], lambda);
        r
    }

    /// (x / z^2, y / z^3), or `None` at infinity.
    fn affine(p: &[u64; 18]) -> Option<[u64; 12]> {
        let (coords, _) = p.as_chunks::<6>();
        if coords[2] == [0; 6] {
            return None;
        }
        // bignum_inv_p384 works outside the Montgomery domain.
        let (mut z, mut z_inv) = ([0; 6], [0; 6]);
        low::bignum_demont_p384(&mut z, &coords[2]);
        low::bignum_inv_p384(&mut z_inv, &z);
        low::bignum_tomont_p384(&mut z, &z_inv);
        let (mut z2, mut z3) = ([0; 6], [0; 6]);
        low::bignum_montsqr_p384(&mut z2, &z);
        low::bignum_montmul_p384(&mut z3, &z2, &z);
        let mut r = [0; 12];
        let (out, _) = r.as_chunks_mut::<6>();
        low::bignum_montmul_p384(&mut out[0], &coords[0], &z2);
        low::bignum_montmul_p384(&mut out[1], &coords[1], &z3);
        Some(r)
    }

    proptest! {
        #[test]
        fn field_ops(x in field(), y in field()) {
            let (sx, sy) = (into_secret(x), into_secret(y));
            let (mut ours, mut theirs) = ([0; 6], [0; 6]);

            bignum_montmul_p384(&mut ours, &sx, &sy);
            low::bignum_montmul_p384(&mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_montsqr_p384(&mut ours, &sx);
            low::bignum_montsqr_p384(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_add_p384(&mut ours, &sx, &sy);
            low::bignum_add_p384(&mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_neg_p384(&mut ours, &sx);
            low::bignum_neg_p384(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_demont_p384(&mut ours, &sx);
            low::bignum_demont_p384(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn field_unreduced_ops(x in raw()) {
            let sx = into_secret(x);
            let (mut ours, mut theirs) = ([0; 6], [0; 6]);

            bignum_tomont_p384(&mut ours, &sx);
            low::bignum_tomont_p384(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_inv_p384(&mut ours, &sx);
            low::bignum_inv_p384(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_add(p in point(), q in point(), lambda in field()) {
            // The sum, a doubling (unspecified, but the formulas agree), and an
            // inverse, whose sum is infinity.
            let mut neg = p;
            low::bignum_neg_p384(&mut neg.as_chunks_mut::<6>().0[1], &p.as_chunks::<6>().0[1]);
            for q in [q, p, rescale(&p, &lambda), neg] {
                let (sp, sq) = (into_secret(p), into_secret(q));
                let (mut ours, mut theirs) = ([0; 18], [0; 18]);
                p384_montjadd(&mut ours, &sp, &sq);
                low::p384_montjadd(&mut theirs, &p, &q);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }

        #[test]
        fn point_mixadd(p in point(), q in point(), lambda in field()) {
            // The sum, a doubling, and an inverse, as for `point_add`.  An
            // affine q cannot be infinity.
            let Some(q) = affine(&q) else { return Ok(()) };
            let mut same = [0; 18];
            same[..12].copy_from_slice(&q);
            same[12..].copy_from_slice(&GENERATOR[12..]);
            let same = rescale(&same, &lambda);
            let mut neg = same;
            low::bignum_neg_p384(&mut neg.as_chunks_mut::<6>().0[1], &same.as_chunks::<6>().0[1]);
            for p in [p, same, neg] {
                let (sp, sq) = (into_secret(p), into_secret(q));
                let (mut ours, mut theirs) = ([0; 18], [0; 18]);
                p384_montjmixadd(&mut ours, &sp, &sq);
                low::p384_montjmixadd(&mut theirs, &p, &q);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }

        #[test]
        fn point_double(p in point()) {
            let sp = into_secret(p);
            let (mut ours, mut theirs) = ([0; 18], [0; 18]);
            p384_montjdouble(&mut ours, &sp);
            low::p384_montjdouble(&mut theirs, &p);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_select(table in prop::collection::vec(any::<u64>(), 288), index: u8) {
            let index = index % 20;
            // Only armv7 selects Jacobian points, so check against the table.
            let mut ours = [0; 18];
            bignum_jac_point_select_p384(&mut ours, &table, into_secret(index));
            let theirs = match index {
                1..=16 => table.as_chunks::<18>().0[usize::from(index) - 1],
                _ => [0; 18],
            };
            prop_assert_eq!(into_public(ours), theirs);

            let (mut ours, mut theirs) = ([0; 12], [0; 12]);
            bignum_aff_point_select_p384(&mut ours, &table[..192], into_secret(index));
            low::bignum_aff_point_select_p384(&mut theirs, &table[..192], index);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn scalar_ops(x in scalar(), y in scalar(), raw in raw()) {
            let (sx, sy, sraw) = (into_secret(x), into_secret(y), into_secret(raw));
            let (mut ours, mut theirs) = ([0; 6], [0; 6]);

            bignum_mod_n384(&mut ours, &sraw);
            low::bignum_mod_n384(&mut theirs, &raw);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_montmul(&mut ours, &sx, &sy, &N);
            low::bignum_montmul(&mut theirs, &x, &y, &N);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_demont(&mut ours, &sx, &N);
            low::bignum_demont(&mut theirs, &x, &N);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_modadd(&mut ours, &sx, &sy, &N);
            low::bignum_modadd(&mut theirs, &x, &y, &N);
            prop_assert_eq!(into_public(ours), theirs);

            // s2n-bignum leaves the inverse of zero unspecified.
            if x != [0; 6] {
                bignum_modinv(&mut ours, &sx, &N, &mut [0; 18]);
                low::bignum_modinv(&mut theirs, &x, &N, &mut [0; 18]);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }

        #[test]
        fn mux(p in prop_oneof![Just(0), Just(1), Just(u64::MAX), any::<u64>()], x: [u64; 6], y: [u64; 6]) {
            let (mut ours, mut theirs) = ([0; 6], [0; 6]);
            bignum_mux(into_secret(p), &mut ours, &x, &y);
            low::bignum_mux(p, &mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);
        }
    }

    #[test]
    fn montifier() {
        let (mut ours, mut theirs) = ([0; 6], [0; 6]);
        bignum_montifier(&mut ours, &N, &mut [0; 6]);
        low::bignum_montifier(&mut theirs, &N, &mut [0; 6]);
        assert_eq!(ours, theirs);
    }

    // Only the top bit set is where an exclusive or of `x` and `-x` would
    // drop it.
    #[test]
    fn nonzero_at_the_top_bit() {
        let mut x = Fe([0; LIMBS]);
        assert_eq!(nonzero(&x), 0);
        x.0[LIMBS - 1] = 1 << (Limb::BITS - 1);
        assert_eq!(nonzero(&x), 1);
        assert_eq!(mask_nonzero(0), 0);
        assert_eq!(mask_nonzero(1 << 63), u64::MAX);
    }

    #[test]
    #[should_panic]
    fn other_modulus_refused() {
        bignum_modadd(&mut [0; 6], &[1; 6], &[1; 6], &P);
    }

    /// G, with Montgomery coordinates and z = 1.
    const GENERATOR: [u64; 18] = [
        0x3dd0_7566_49c0_b528,
        0x20e3_78e2_a0d6_ce38,
        0x879c_3afc_541b_4d6e,
        0x6454_8684_59a3_0eff,
        0x812f_f723_614e_de2b,
        0x4d3a_adc2_299e_1513,
        0x2304_3dad_4b03_a4fe,
        0xa1bf_a8bf_7bb4_a9ac,
        0x8bad_e756_2e83_b050,
        0xc6c3_5219_68f4_ffd9,
        0xdd80_0226_3969_a840,
        0x2b78_abc2_5a15_c5e9,
        0xffff_ffff_0000_0001,
        0x0000_0000_ffff_ffff,
        0x0000_0000_0000_0001,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
        0x0000_0000_0000_0000,
    ];
}
