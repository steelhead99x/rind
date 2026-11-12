// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The s2n-bignum routines `mid::p256` uses, with their contracts, over
//! the parent module's limbs: `p256_mul`'s Montgomery multiplication and
//! squaring, and fiat-crypto's P-256 field and group order arithmetic for
//! the rest.
//!
//! fiat-crypto proves each operation correct, and emits it as straight-line
//! code with no secret-dependent branch or index.  fiat-crypto cannot
//! generate an unsaturated P-256, as it does P-521: its bounds checks fail
//! at every 32-bit limb count from 9 to 16.  The rest composes those: the point formulas repeat s2n-bignum's operation
//! sequences, and every coordinate is fully reduced, so results match it
//! word for word; inversion is Fermat's little theorem, raising to a public
//! exponent by a fixed sequence of squarings and multiplications; range
//! reduction is one conditional subtraction, as every input is below 2^256,
//! which is less than twice either modulus; base point multiplication is
//! s2n-bignum's `p256_scalarmulbase` algorithm over the same table; and
//! variable point multiplication is by Booth-recoded 5-bit windows, after
//! negating a scalar above n / 2 so that no addition doubles.
//!
//! Arithmetic on secrets wraps: the bounds rule out overflow, and a debug
//! build's overflow check would branch on secret values.

pub(super) use super::fiat_p256::fiat_p256_montgomery_domain_field_element as Fe;
pub(super) use super::fiat_p256_scalar::fiat_p256_scalar_montgomery_domain_field_element as Fs;
use super::p256_mul::{fe_mul, fe_sqr, fs_mul, fs_sqr};
use super::{Limb, Wide, fiat_p256 as fp, fiat_p256_scalar as fs};

/// Limbs in a field element.
const LIMBS: usize = (256 / Limb::BITS) as usize;

/// z := x * y / 2^256 mod p_256
pub(crate) fn bignum_montmul_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    *z = join(&fe_mul(&fe(x), &fe(y)).0);
}

/// z := x^2 / 2^256 mod p_256
pub(crate) fn bignum_montsqr_p256(z: &mut [u64; 4], x: &[u64; 4]) {
    *z = join(&fe_sqr(&fe(x)).0);
}

/// z := (x + y) mod p_256, assuming x and y reduced
pub(crate) fn bignum_add_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    *z = join(&fe_add(&fe(x), &fe(y)).0);
}

/// z := (-x) mod p_256, assuming x reduced
pub(crate) fn bignum_neg_p256(z: &mut [u64; 4], x: &[u64; 4]) {
    *z = join(&fe_opp(&fe(x)).0);
}

/// z := (2^256 * x) mod p_256
pub(crate) fn bignum_tomont_p256(z: &mut [u64; 4], x: &[u64; 4]) {
    *z = join(&fe_to_mont(&reduce(split(x), &split(&P))).0);
}

/// z := (x / 2^256) mod p_256, assuming x reduced
pub(crate) fn bignum_demont_p256(z: &mut [u64; 4], x: &[u64; 4]) {
    *z = join(&fe_from_mont(&fe(x)));
}

/// z := x^-1 mod p_256, or zero if x is zero mod p_256
pub(crate) fn bignum_inv_p256(z: &mut [u64; 4], x: &[u64; 4]) {
    let x = fe_to_mont(&reduce(split(x), &split(&P)));
    *z = join(&fe_from_mont(&fe_invert(&x)));
}

/// p3 := p1 + p2, as Jacobian points over p_256 with Montgomery coordinates.
///
/// A point with a zero z is the point at infinity.  The result is
/// unspecified when p1 and p2 are the same point.
pub(crate) fn p256_montjadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12]) {
    *p3 = point(&jadd(&coords(p1), &coords(p2)));
}

/// p3 := p1 + p2, for a Jacobian p1 and an affine p2 (whose z is
/// implicitly one), over p_256 with Montgomery coordinates.
///
/// A p1 with a zero z is the point at infinity; p2 cannot be.  The result
/// is unspecified when p1 and p2 are the same point.
pub(crate) fn p256_montjmixadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 8]) {
    let (xy2, _) = p2.as_chunks::<4>();
    *p3 = point(&jmixadd(&coords(p1), &[fe(&xy2[0]), fe(&xy2[1])]));
}

/// p3 := 2 * p1, as a Jacobian point over p_256 with Montgomery coordinates.
pub(crate) fn p256_montjdouble(p3: &mut [u64; 12], p1: &[u64; 12]) {
    *p3 = point(&jdouble(&coords(p1)));
}

/// res := scalar * P, for the Jacobian point P = `point` with Montgomery
/// coordinates.  A result at infinity has a zero z.
pub(crate) fn p256_montjscalarmul(res: &mut [u64; 12], scalar: &[u64; 4], point_in: &[u64; 12]) {
    let mut k = [0; 4];
    bignum_mod_n256(&mut k, scalar);
    let mut p = coords(point_in);

    // Above n / 2, use n - k and -P, so that k is below n / 2.  Before each
    // addition, the accumulator is 32m P and the table point d P for the
    // value m of the windows above and a digit d of at most 16, and 32m + d,
    // the value of the windows so far, is below n / 2.  So they are equal
    // only if 32m + d is 2d, when m is zero and the accumulator is at
    // infinity, which `jadd` selects around, and opposite only if 32m + d
    // is zero, which leaves the accumulator at infinity too.  A zero digit
    // looks up a zero z, infinity, so its sum is the accumulator.
    let (neg_k, _) = sub(&split(&N), &split(&k));
    let (_, above_half) = sub(&split(&HALF_N), &split(&k));
    let above_half = opaque(above_half);
    let k = join(&select_words(above_half, &split(&k), &neg_k));
    p[1] = select(above_half, &p[1], &fe_opp(&p[1]));

    let mut table = [p; 16];
    for i in 1..table.len() {
        table[i] = match i % 2 {
            1 => jdouble(&table[i / 2]),
            _ => jadd(&table[i - 1], &table[0]),
        };
    }
    let lookup = |digit: u8, sign: u8| {
        let mut r = [Fe([0; LIMBS]); 3];
        for (i, entry) in (1u8..).zip(&table) {
            let hit = 1u8.wrapping_sub(nonzero_u8(i ^ digit));
            for (r, e) in r.iter_mut().zip(entry) {
                *r = select(hit, r, e);
            }
        }
        r[1] = select(sign, &r[1], &fe_opp(&r[1]));
        r
    };

    let mut windows = booth_w5(&k);
    let (digit, _) = windows.next().unwrap();
    let mut acc = lookup(digit, 0);
    for (digit, sign) in windows {
        for _ in 0..5 {
            acc = jdouble(&acc);
        }
        acc = jadd(&acc, &lookup(digit, sign));
    }

    // A P at infinity leaves z zero throughout.
    *res = point(&acc);
}

/// res := scalar * P, as affine coordinates outside the Montgomery domain,
/// where `table` holds P's multiples in Montgomery-affine form: row i holds
/// 2^(6i) j P for j from 1 to 32.  A result at infinity is (0, 0).
///
/// This is s2n-bignum's `p256_scalarmulbase` with a block size of 6.  Each
/// 6-bit window, plus the carry from the one below, picks a row entry,
/// negated above 32 with a carry into the next.  The accumulator then sums
/// the windows below, a smaller integer than the entry in magnitude, so
/// neither equals the other.
pub(crate) fn p256_scalarmulbase(res: &mut [u64; 8], scalar: &[u64; 4], table: &[[u64; 256]; 43]) {
    let mut k = [0; 4];
    bignum_mod_n256(&mut k, scalar);

    let mut acc = [Fe([0; LIMBS]); 3];
    let mut carry = 0u8;
    for (i, row) in table.iter().enumerate() {
        // Window i spans bits 6i to 6i + 5, within a 64-bit word or across
        // two, and the last only to bit 255.
        let bit = 6 * i;
        let (word, shift) = (bit / 64, bit % 64);
        let mut window = k[word] >> shift;
        if shift > 58 && word < 3 {
            window |= k[word + 1] << (64 - shift);
        }
        let bf = ((window & 0x3f) as u8).wrapping_add(carry);
        // bf is at most 64; above 32, add 64 - bf negated and carry 64.
        carry = opaque(32u8.wrapping_sub(bf) >> 7);
        let digit = select_u8(carry, bf, 64u8.wrapping_sub(bf));

        let mut entry = [0; 8];
        row_select(&mut entry, row, digit);
        let (xy, _) = entry.as_chunks::<4>();
        let (x, y) = (fe(&xy[0]), fe(&xy[1]));
        let y = select(carry, &y, &fe_opp(&y));

        // The mixed addition cannot add infinity, so a zero digit keeps the
        // accumulator.
        let sum = jmixadd(&acc, &[x, y]);
        acc = select_point(nonzero_u8(digit), &acc, &sum);
    }

    let [x, y, z] = acc;
    let z_inv = fe_invert(&z);
    let z2_inv = fe_sqr(&z_inv);
    let x = fe_mul(&x, &z2_inv);
    let y = fe_mul(&y, &fe_mul(&z2_inv, &z_inv));
    res[..4].copy_from_slice(&join(&fe_from_mont(&x)));
    res[4..].copy_from_slice(&join(&fe_from_mont(&y)));
}

/// z := x mod n_256
pub(crate) fn bignum_mod_n256(z: &mut [u64; 4], x: &[u64; 4]) {
    *z = join(&reduce(split(x), &split(&N)));
}

// The routines below take the modulus, as s2n-bignum's are generic over
// it.  `mid::p256` passes only n_256, the one modulus of this length that
// this backend has verified arithmetic for, so any other is refused.

/// z := x * y / 2^256 mod m, for m = n_256
pub(crate) fn bignum_montmul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    let r = fs_mul(&fs(x), &fs(y));
    z.copy_from_slice(&join(&r.0));
}

/// z := x / 2^256 mod m, for m = n_256, assuming x reduced
pub(crate) fn bignum_demont(z: &mut [u64], x: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    let mut r = fs::fiat_p256_scalar_non_montgomery_domain_field_element([0; LIMBS]);
    fs::fiat_p256_scalar_from_montgomery(&mut r, &fs(x));
    z.copy_from_slice(&join(&r.0));
}

/// z := (x + y) mod m, for m = n_256, assuming x and y reduced
pub(crate) fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    let mut r = Fs([0; LIMBS]);
    fs::fiat_p256_scalar_add(&mut r, &fs(x), &fs(y));
    z.copy_from_slice(&join(&r.0));
}

/// z := a^-1 mod b, for b = n_256, or zero if a is zero mod n_256
///
/// `_t` is s2n-bignum's scratch space, which this does not need.
pub(crate) fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], _t: &mut [u64]) {
    assert_eq!(b, N);
    let a = reduce(split(a.try_into().unwrap()), &split(&N));
    let mut a_mont = Fs([0; LIMBS]);
    fs::fiat_p256_scalar_to_montgomery(
        &mut a_mont,
        &fs::fiat_p256_scalar_non_montgomery_domain_field_element(a),
    );
    let r = fs_invert(&a_mont);
    bignum_demont(z, &join(&r.0), b);
}

/// z := 2^512 mod m, for m = n_256
// Checks the constant against s2n-bignum, which armv7 lacks.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
pub(crate) fn bignum_montifier(z: &mut [u64], m: &[u64], _t: &mut [u64]) {
    assert_eq!(m, N);
    // to_montgomery multiplies by 2^256, so this is 2^256 * (2^256 mod n).
    let mut one = Fs([0; LIMBS]);
    fs::fiat_p256_scalar_set_one(&mut one);
    let mut r = Fs([0; LIMBS]);
    fs::fiat_p256_scalar_to_montgomery(
        &mut r,
        &fs::fiat_p256_scalar_non_montgomery_domain_field_element(one.0),
    );
    z.copy_from_slice(&join(&r.0));
}

/// The point formulas of s2n-bignum's `p256_montjadd`.
fn jadd(p1: &[Fe; 3], p2: &[Fe; 3]) -> [Fe; 3] {
    let [x1, y1, z1] = p1;
    let [x2, y2, z2] = p2;

    let z1sq = fe_sqr(z1);
    let z2sq = fe_sqr(z2);
    let y1a = fe_mul(&z2sq, &fe_mul(z2, y1));
    let y2a = fe_mul(&z1sq, &fe_mul(z1, y2));
    let x1a = fe_mul(&z2sq, x1);
    let x2a = fe_mul(&z1sq, x2);

    let xd = fe_sub(&x2a, &x1a);
    let yd = fe_sub(&y2a, &y1a);
    let zz = fe_sqr(&xd);
    let ww = fe_sqr(&yd);
    let zzx1 = fe_mul(&zz, &x1a);
    let zzx2 = fe_mul(&zz, &x2a);

    let x3 = fe_sub(&fe_sub(&ww, &zzx1), &zzx2);
    let t1 = fe_mul(&fe_sub(&zzx2, &zzx1), &y1a);
    let y3 = fe_sub(&fe_mul(&yd, &fe_sub(&zzx1, &x3)), &t1);
    let z3 = fe_mul(&fe_mul(&xd, z1), z2);

    // An input at infinity makes the result the other input.
    let z1_nonzero = nonzero(z1);
    let z2_nonzero = nonzero(z2);
    let pick = |p1: &Fe, p2: &Fe, sum: &Fe| {
        let if_z1_nonzero = select(z2_nonzero, p1, sum);
        let if_z1_zero = select(z2_nonzero, sum, p2);
        select(z1_nonzero, &if_z1_zero, &if_z1_nonzero)
    };
    [pick(x1, x2, &x3), pick(y1, y2, &y3), pick(z1, z2, &z3)]
}

/// The point formulas of s2n-bignum's `p256_montjmixadd`.
fn jmixadd(p1: &[Fe; 3], p2: &[Fe; 2]) -> [Fe; 3] {
    let [x1, y1, z1] = p1;
    let [x2, y2] = p2;

    let z1sq = fe_sqr(z1);
    let y2a = fe_mul(&z1sq, &fe_mul(z1, y2));
    let x2a = fe_mul(&z1sq, x2);

    let xd = fe_sub(&x2a, x1);
    let yd = fe_sub(&y2a, y1);
    let zz = fe_sqr(&xd);
    let ww = fe_sqr(&yd);
    let zzx1 = fe_mul(&zz, x1);
    let zzx2 = fe_mul(&zz, &x2a);

    let x3 = fe_sub(&fe_sub(&ww, &zzx1), &zzx2);
    let t1 = fe_mul(&fe_sub(&zzx2, &zzx1), y1);
    let y3 = fe_sub(&fe_mul(&yd, &fe_sub(&zzx1, &x3)), &t1);
    let z3 = fe_mul(&xd, z1);

    // p1 at infinity makes the result p2, with a z of one.
    let mut one = Fe([0; LIMBS]);
    fp::fiat_p256_set_one(&mut one);
    let z1_nonzero = nonzero(z1);
    [
        select(z1_nonzero, x2, &x3),
        select(z1_nonzero, y2, &y3),
        select(z1_nonzero, &one, &z3),
    ]
}

/// The point formulas of s2n-bignum's `p256_montjdouble`.
fn jdouble(p1: &[Fe; 3]) -> [Fe; 3] {
    let [x, y, z] = p1;

    let z2 = fe_sqr(z);
    let y2 = fe_sqr(y);
    // x^2 - z^4, which is (x + z^2) * (x - z^2)
    let x2p = fe_mul(&fe_add(x, &z2), &fe_sub(x, &z2));
    let x4p = fe_sqr(&x2p);
    let xy2 = fe_mul(x, &y2);
    let y4 = fe_sqr(&y2);

    // 12 * xy2 - 9 * x4p
    let xy2_4 = fe_double(&fe_double(&xy2));
    let x4p_8 = fe_double(&fe_double(&fe_double(&x4p)));
    let d = fe_sub(&fe_add(&xy2_4, &fe_double(&xy2_4)), &fe_add(&x4p_8, &x4p));

    // (y + z)^2 - z^2 - y^2, which is 2 * y * z
    let z3 = fe_sub(&fe_sub(&fe_sqr(&fe_add(y, z)), &z2), &y2);
    let x3 = fe_sub(&xy2_4, &d);
    let dx2 = fe_mul(&d, &x2p);
    let y4_8 = fe_double(&fe_double(&fe_double(&y4)));
    let y3 = fe_sub(&fe_add(&fe_double(&dx2), &dx2), &y4_8);

    [x3, y3, z3]
}

/// The 52 Booth-recoded 5-bit windows of `k`, highest first, each a digit
/// and its sign, as `mid::p256`'s.
fn booth_w5(k: &[u64; 4]) -> impl Iterator<Item = (u8, u8)> {
    let mut bytes = [0u8; 33];
    for (chunk, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(k) {
        *chunk = word.to_le_bytes();
    }
    (0..=51).rev().map(move |w: usize| {
        let value = match w {
            0 => (bytes[0] << 1) & 0x3f,
            _ => {
                let bit = 5 * w - 1;
                let pair = u16::from(bytes[bit / 8]) | (u16::from(bytes[bit / 8 + 1]) << 8);
                (pair >> (bit % 8)) as u8 & 0x3f
            }
        };
        let sign = !((value >> 5).wrapping_sub(1));
        let d = 63u8.wrapping_sub(value);
        let d = (d & sign) | (value & !sign);
        ((d >> 1).wrapping_add(d & 1), sign & 1)
    })
}

/// `x^(p - 2)`, which is `x^-1` for a nonzero `x`, by an addition chain
/// of 255 squarings and 12 multiplications.
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

    // p - 2 is, from the top: 32 ones, 31 zeros, a one, 96 zeros, 94 ones,
    // a zero, and a one.
    let r = fe_mul(&sqr_n(&x32, 32), x);
    let r = fe_mul(&sqr_n(&r, 128), &x32);
    let r = fe_mul(&sqr_n(&r, 32), &x32);
    let r = fe_mul(&sqr_n(&r, 30), &x30);
    fe_mul(&sqr_n(&r, 2), x)
}

/// `x^(n - 2)`, which is `x^-1` for a nonzero `x`, by 252 squarings and 51
/// multiplications: runs of ones for the top half of `n - 2`, and a fixed
/// 4-bit window, none of whose digits is zero, for the bottom half.
fn fs_invert(x: &Fs) -> Fs {
    let sqr_n = |x: &Fs, n: usize| (0..n).fold(*x, |acc, _| fs_sqr(&acc));

    // table[i] is x^(i + 1).
    let mut table = [*x; 15];
    for i in 1..table.len() {
        table[i] = fs_mul(&table[i - 1], x);
    }

    // x_k is x^(2^k - 1), whose exponent is k one bits.
    let x4 = table[14];
    let x8 = fs_mul(&sqr_n(&x4, 4), &x4);
    let x16 = fs_mul(&sqr_n(&x8, 8), &x8);
    let x32 = fs_mul(&sqr_n(&x16, 16), &x16);

    // The top half of n - 2 is 32 ones, 32 zeros, and 64 ones.
    let r = fs_mul(&sqr_n(&x32, 64), &x32);
    let mut r = fs_mul(&sqr_n(&r, 32), &x32);
    for word in N_MINUS_2[..2].iter().rev() {
        for shift in (0..64).step_by(4).rev() {
            let digit = (word >> shift) & 0xf;
            r = fs_mul(&sqr_n(&r, 4), &table[digit as usize - 1]);
        }
    }
    r
}

/// Viewing table as rows of N words, copy the row at table[index - 1]
/// into z, or zero if `index` is zero or past the last row.
fn row_select<const N: usize>(z: &mut [u64; N], table: &[u64], index: u8) {
    *z = [0; N];
    let (rows, _) = table.as_chunks::<N>();
    for (i, row) in (1u8..).zip(rows) {
        let mask = u64::from(nonzero_u8(i ^ index)).wrapping_sub(1);
        for (z, w) in z.iter_mut().zip(row) {
            *z |= w & mask;
        }
    }
}

/// `x - m` if that does not borrow, else `x`.
///
/// This fully reduces any `x < 2 * m`.
pub(super) fn reduce(x: [Limb; LIMBS], m: &[Limb; LIMBS]) -> [Limb; LIMBS] {
    let (diff, borrow) = sub(&x, m);
    select_words(opaque(borrow), &diff, &x)
}

/// `x - y` and its borrow out.
pub(super) fn sub(x: &[Limb; LIMBS], y: &[Limb; LIMBS]) -> ([Limb; LIMBS], u8) {
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

/// `if_nonzero` if `flag` is 1, else `if_zero`.
pub(super) fn select_words(
    flag: u8,
    if_zero: &[Limb; LIMBS],
    if_nonzero: &[Limb; LIMBS],
) -> [Limb; LIMBS] {
    let mut r = [0; LIMBS];
    fp::fiat_p256_selectznz(&mut r, flag, if_zero, if_nonzero);
    r
}

fn fe(x: &[u64; 4]) -> Fe {
    Fe(split(x))
}

fn fs(x: &[u64]) -> Fs {
    Fs(split(x.try_into().unwrap()))
}

fn fe_add(x: &Fe, y: &Fe) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p256_add(&mut r, x, y);
    r
}

fn fe_double(x: &Fe) -> Fe {
    fe_add(x, x)
}

fn fe_sub(x: &Fe, y: &Fe) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p256_sub(&mut r, x, y);
    r
}

fn fe_opp(x: &Fe) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p256_opp(&mut r, x);
    r
}

fn fe_to_mont(x: &[Limb; LIMBS]) -> Fe {
    let mut r = Fe([0; LIMBS]);
    fp::fiat_p256_to_montgomery(
        &mut r,
        &fp::fiat_p256_non_montgomery_domain_field_element(*x),
    );
    r
}

fn fe_from_mont(x: &Fe) -> [Limb; LIMBS] {
    let mut r = fp::fiat_p256_non_montgomery_domain_field_element([0; LIMBS]);
    fp::fiat_p256_from_montgomery(&mut r, x);
    r.0
}

/// 1 if `x` is nonzero, else 0.
fn nonzero(x: &Fe) -> u8 {
    let mut any = 0;
    fp::fiat_p256_nonzero(&mut any, &x.0);
    opaque(((any | any.wrapping_neg()) >> (Limb::BITS - 1)) as u8)
}

/// 1 if `x` is nonzero, else 0.
fn nonzero_u8(x: u8) -> u8 {
    opaque((x | x.wrapping_neg()) >> 7)
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select(flag: u8, if_zero: &Fe, if_nonzero: &Fe) -> Fe {
    Fe(select_words(flag, &if_zero.0, &if_nonzero.0))
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select_point(flag: u8, if_zero: &[Fe; 3], if_nonzero: &[Fe; 3]) -> [Fe; 3] {
    [0, 1, 2].map(|i| select(flag, &if_zero[i], &if_nonzero[i]))
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select_u8(flag: u8, if_zero: u8, if_nonzero: u8) -> u8 {
    let mask = flag.wrapping_neg();
    (if_nonzero & mask) | (if_zero & !mask)
}

/// Hides that `x` is a flag or mask, so the optimiser cannot turn the
/// arithmetic selecting with it into a secret-dependent branch or cmov.
pub(super) fn opaque<T>(x: T) -> T {
    core::hint::black_box(x)
}

fn coords(p: &[u64; 12]) -> [Fe; 3] {
    let (words, _) = p.as_chunks::<4>();
    [fe(&words[0]), fe(&words[1]), fe(&words[2])]
}

fn point(p: &[Fe; 3]) -> [u64; 12] {
    let mut r = [0u64; 12];
    let (words, _) = r.as_chunks_mut::<4>();
    for (w, c) in words.iter_mut().zip(p) {
        *w = join(&c.0);
    }
    r
}

/// `x`'s limbs, low first.
pub(super) fn split(x: &[u64; 4]) -> [Limb; LIMBS] {
    core::array::from_fn(|i| (x[i * 4 / LIMBS] >> (Limb::BITS as usize * i % 64)) as Limb)
}

/// The words of `x`'s limbs, low first.
fn join(x: &[Limb; LIMBS]) -> [u64; 4] {
    let mut r = [0u64; 4];
    for (i, limb) in x.iter().enumerate() {
        r[i * 4 / LIMBS] |= u64::from(*limb) << (Limb::BITS as usize * i % 64);
    }
    r
}

/// p_256, as little-endian words.
pub(super) const P: [u64; 4] = [
    0xffff_ffff_ffff_ffff,
    0x0000_0000_ffff_ffff,
    0x0000_0000_0000_0000,
    0xffff_ffff_0000_0001,
];

/// n_256, the group order, as little-endian words.
pub(crate) const N: [u64; 4] = [
    0xf3b9_cac2_fc63_2551,
    0xbce6_faad_a717_9e84,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_0000_0000,
];

const N_MINUS_2: [u64; 4] = [
    0xf3b9_cac2_fc63_254f,
    0xbce6_faad_a717_9e84,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_0000_0000,
];

/// (n - 1) / 2: a k above it is above n / 2.
const HALF_N: [u64; 4] = [
    0x79dc_e561_7e31_92a8,
    0xde73_7d56_d38b_cf42,
    0x7fff_ffff_ffff_ffff,
    0x7fff_ffff_8000_0000,
];

/// Checks each routine word for word against s2n-bignum's, and each
/// scalar multiplication point for point.
///
/// Inputs that are secret in `mid::p256` are marked secret, so under
/// `admin/ctgrind` these also check each routine is constant time in them.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::low;
    use crate::low::ct::{into_public, into_secret};

    /// Any 256-bit value, biased towards the moduli's edges.
    fn raw() -> impl Strategy<Value = [u64; 4]> {
        prop_oneof![
            8 => any::<[u64; 4]>(),
            1 => prop_oneof![
                Just([0; 4]),
                Just([1, 0, 0, 0]),
                Just(add_small(P, -1)),
                Just(P),
                // p + 1, whose low word carries.
                Just([0, P[1] + 1, P[2], P[3]]),
                Just(add_small(N, -1)),
                Just(N),
                Just(add_small(N, 1)),
                Just(HALF_N),
                Just(add_small(HALF_N, 1)),
                Just([u64::MAX; 4]),
            ],
        ]
    }

    /// A field element below p, including 0, 1, and p - 1.
    fn field() -> impl Strategy<Value = [u64; 4]> {
        prop_oneof![
            8 => any::<[u64; 4]>().prop_map(|x| {
                let mut r = [0; 4];
                low::bignum_tomont_p256(&mut r, &x);
                r
            }),
            1 => prop_oneof![
                Just([0; 4]),
                Just([1, 0, 0, 0]),
                Just(add_small(P, -1)),
            ],
        ]
    }

    /// `x + d`, for a low word that neither carries nor borrows.
    fn add_small(mut x: [u64; 4], d: i64) -> [u64; 4] {
        x[0] = x[0].checked_add_signed(d).unwrap();
        x
    }

    /// A scalar below n, including 0, 1, and n - 1.
    fn scalar() -> impl Strategy<Value = [u64; 4]> {
        raw().prop_map(|x| {
            let mut r = [0; 4];
            low::bignum_mod_n256(&mut r, &x);
            r
        })
    }

    /// A Jacobian point: a multiple of G with a random z, or infinity.
    fn point() -> impl Strategy<Value = [u64; 12]> {
        let multiple = (0..64u32, field()).prop_map(|(doublings, lambda)| {
            let mut p = GENERATOR;
            for _ in 0..doublings {
                let q = p;
                low::p256_montjdouble(&mut p, &q);
            }
            rescale(&p, &lambda)
        });
        let infinity = (field(), field()).prop_map(|(x, y)| {
            let mut p = [0; 12];
            p[..4].copy_from_slice(&x);
            p[4..8].copy_from_slice(&y);
            p
        });
        prop_oneof![9 => multiple, 1 => infinity]
    }

    /// (x * l^2, y * l^3, z * l), the same point unless l is zero.
    fn rescale(p: &[u64; 12], lambda: &[u64; 4]) -> [u64; 12] {
        let mut l2 = [0; 4];
        low::bignum_montsqr_p256(&mut l2, lambda);
        let mut l3 = [0; 4];
        low::bignum_montmul_p256(&mut l3, &l2, lambda);
        let mut r = [0; 12];
        let (out, _) = r.as_chunks_mut::<4>();
        let (coords, _) = p.as_chunks::<4>();
        low::bignum_montmul_p256(&mut out[0], &coords[0], &l2);
        low::bignum_montmul_p256(&mut out[1], &coords[1], &l3);
        low::bignum_montmul_p256(&mut out[2], &coords[2], lambda);
        r
    }

    /// (x / z^2, y / z^3), or `None` at infinity.
    fn affine(p: &[u64; 12]) -> Option<[u64; 8]> {
        let (coords, _) = p.as_chunks::<4>();
        if coords[2] == [0; 4] {
            return None;
        }
        // bignum_inv_p256 works outside the Montgomery domain.
        let (mut z, mut z_inv) = ([0; 4], [0; 4]);
        low::bignum_demont_p256(&mut z, &coords[2]);
        low::bignum_inv_p256(&mut z_inv, &z);
        low::bignum_tomont_p256(&mut z, &z_inv);
        let (mut z2, mut z3) = ([0; 4], [0; 4]);
        low::bignum_montsqr_p256(&mut z2, &z);
        low::bignum_montmul_p256(&mut z3, &z2, &z);
        let mut r = [0; 8];
        let (out, _) = r.as_chunks_mut::<4>();
        low::bignum_montmul_p256(&mut out[0], &coords[0], &z2);
        low::bignum_montmul_p256(&mut out[1], &coords[1], &z3);
        Some(r)
    }

    /// (x / z^2, y / z^3) outside the Montgomery domain, or (0, 0) at
    /// infinity, as `p256_scalarmul` returns a point.
    fn plain_affine(p: &[u64; 12]) -> [u64; 8] {
        let mut r = [0; 8];
        if let Some(xy) = affine(p) {
            let (out, _) = r.as_chunks_mut::<4>();
            let (xy, _) = xy.as_chunks::<4>();
            low::bignum_demont_p256(&mut out[0], &xy[0]);
            low::bignum_demont_p256(&mut out[1], &xy[1]);
        }
        r
    }

    /// `scalar * point` by s2n-bignum, as `plain_affine` gives it, by its
    /// affine `p256_scalarmul`, which cannot take infinity.
    fn s2n_multiply(scalar: &[u64; 4], point: &[u64; 12]) -> [u64; 8] {
        let mut r = [0; 8];
        if affine(point).is_some() {
            low::p256_scalarmul(&mut r, scalar, &plain_affine(point));
        }
        r
    }

    /// `p256_scalarmulbase`'s table for G: row i holds 2^(6i) j G for j
    /// from 1 to 32, Montgomery-affine.
    fn generator_table() -> Box<[[u64; 256]; 43]> {
        let mut table = Box::new([[0; 256]; 43]);
        let mut base = GENERATOR;
        for row in table.iter_mut() {
            let mut multiple = base;
            for (j, entry) in (1..).zip(row.as_chunks_mut::<8>().0) {
                *entry = affine(&multiple).unwrap();
                // The addition cannot double, so 2 * base needs its own.
                let sum = multiple;
                match j {
                    1 => low::p256_montjdouble(&mut multiple, &sum),
                    _ => low::p256_montjadd(&mut multiple, &sum, &base),
                }
            }
            for _ in 0..6 {
                let b = base;
                low::p256_montjdouble(&mut base, &b);
            }
        }
        table
    }

    proptest! {
        #[test]
        fn field_ops(x in field(), y in field()) {
            let (sx, sy) = (into_secret(x), into_secret(y));
            let (mut ours, mut theirs) = ([0; 4], [0; 4]);

            bignum_montmul_p256(&mut ours, &sx, &sy);
            low::bignum_montmul_p256(&mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_montsqr_p256(&mut ours, &sx);
            low::bignum_montsqr_p256(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_add_p256(&mut ours, &sx, &sy);
            low::bignum_add_p256(&mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_neg_p256(&mut ours, &sx);
            low::bignum_neg_p256(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_demont_p256(&mut ours, &sx);
            low::bignum_demont_p256(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn field_unreduced_ops(x in raw()) {
            let sx = into_secret(x);
            let (mut ours, mut theirs) = ([0; 4], [0; 4]);

            bignum_tomont_p256(&mut ours, &sx);
            low::bignum_tomont_p256(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_inv_p256(&mut ours, &sx);
            low::bignum_inv_p256(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_add(p in point(), q in point(), lambda in field()) {
            // The sum, a doubling (unspecified, but the formulas agree), and an
            // inverse, whose sum is infinity.
            let mut neg = p;
            low::bignum_neg_p256(&mut neg.as_chunks_mut::<4>().0[1], &p.as_chunks::<4>().0[1]);
            for q in [q, p, rescale(&p, &lambda), neg] {
                let (sp, sq) = (into_secret(p), into_secret(q));
                let (mut ours, mut theirs) = ([0; 12], [0; 12]);
                p256_montjadd(&mut ours, &sp, &sq);
                low::p256_montjadd(&mut theirs, &p, &q);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }

        #[test]
        fn point_mixadd(p in point(), q in point(), lambda in field()) {
            // The sum, a doubling, and an inverse, as for `point_add`.  An
            // affine q cannot be infinity.
            let Some(q) = affine(&q) else { return Ok(()) };
            let mut same = [0; 12];
            same[..8].copy_from_slice(&q);
            same[8..].copy_from_slice(&GENERATOR[8..]);
            let same = rescale(&same, &lambda);
            let mut neg = same;
            low::bignum_neg_p256(&mut neg.as_chunks_mut::<4>().0[1], &same.as_chunks::<4>().0[1]);
            for p in [p, same, neg] {
                let (sp, sq) = (into_secret(p), into_secret(q));
                let (mut ours, mut theirs) = ([0; 12], [0; 12]);
                p256_montjmixadd(&mut ours, &sp, &sq);
                low::p256_montjmixadd(&mut theirs, &p, &q);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }

        #[test]
        fn point_double(p in point()) {
            let sp = into_secret(p);
            let (mut ours, mut theirs) = ([0; 12], [0; 12]);
            p256_montjdouble(&mut ours, &sp);
            low::p256_montjdouble(&mut theirs, &p);
            prop_assert_eq!(into_public(ours), theirs);
        }
    }

    // Each case scalar-multiplies or inverts, which is slow in a debug build.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn scalar_multiply(k in raw(), p in point()) {
            let mut ours = [0; 12];
            p256_montjscalarmul(&mut ours, &into_secret(k), &into_secret(p));
            let ours = into_public(ours);
            prop_assert_eq!(plain_affine(&ours), s2n_multiply(&k, &p));
        }

        #[test]
        fn scalar_ops(x in scalar(), y in scalar(), raw in raw()) {
            let (sx, sy, sraw) = (into_secret(x), into_secret(y), into_secret(raw));
            let (mut ours, mut theirs) = ([0; 4], [0; 4]);

            bignum_mod_n256(&mut ours, &sraw);
            low::bignum_mod_n256(&mut theirs, &raw);
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
            if x != [0; 4] {
                bignum_modinv(&mut ours, &sx, &N, &mut [0; 12]);
                low::bignum_modinv(&mut theirs, &x, &N, &mut [0; 12]);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }
    }

    #[test]
    fn scalar_multiply_edges() {
        // Zero, n, and either side of n / 2, where the scalar is negated.
        for k in [
            [0; 4],
            N,
            HALF_N,
            add_small(HALF_N, 1),
            add_small(N, -1),
            [1, 0, 0, 0],
        ] {
            let mut ours = [0; 12];
            p256_montjscalarmul(&mut ours, &k, &GENERATOR);
            assert_eq!(plain_affine(&ours), s2n_multiply(&k, &GENERATOR), "{k:x?}");
        }
    }

    #[test]
    fn base_multiply() {
        // Every window value at every position, with and without the carry
        // from below: k's 6-bit windows run through 0 to 63, shifted along,
        // plus the edges.
        let table = generator_table();
        let mut scalars = vec![[0; 4], [1, 0, 0, 0], add_small(N, -1), N, [u64::MAX; 4]];
        for v in 0..64u64 {
            let mut k = [0u64; 4];
            for i in 0..43 {
                let bit = 6 * i;
                k[bit / 64] |= ((v + i as u64) & 0x3f) << (bit % 64);
                if bit % 64 > 58 && bit / 64 < 3 {
                    k[bit / 64 + 1] |= ((v + i as u64) & 0x3f) >> (64 - bit % 64);
                }
            }
            scalars.push(k);
        }
        // x86_64 has no s2n-bignum `p256_scalarmulbase`, so this checks
        // against its variable point multiplication of G.
        for k in scalars {
            let mut ours = [0; 8];
            p256_scalarmulbase(&mut ours, &into_secret(k), &table);
            assert_eq!(into_public(ours), s2n_multiply(&k, &GENERATOR), "{k:x?}");
        }
    }

    #[test]
    fn montifier() {
        let (mut ours, mut theirs) = ([0; 4], [0; 4]);
        bignum_montifier(&mut ours, &N, &mut [0; 4]);
        low::bignum_montifier(&mut theirs, &N, &mut [0; 4]);
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
        assert_eq!((nonzero_u8(0), nonzero_u8(1), nonzero_u8(0x80)), (0, 1, 1));
    }

    #[test]
    #[should_panic]
    fn other_modulus_refused() {
        bignum_modadd(&mut [0; 4], &[1; 4], &[1; 4], &P);
    }

    /// G, with Montgomery coordinates and z = 1.
    const GENERATOR: [u64; 12] = [
        0x79e7_30d4_18a9_143c,
        0x75ba_95fc_5fed_b601,
        0x79fb_732b_7762_2510,
        0x1890_5f76_a537_55c6,
        0xddf2_5357_ce95_560a,
        0x8b4a_b8e4_ba19_e45c,
        0xd2e8_8688_dd21_f325,
        0x8571_ff18_2588_5d85,
        0x0000_0000_0000_0001,
        0xffff_ffff_0000_0000,
        0xffff_ffff_ffff_ffff,
        0x0000_0000_ffff_fffe,
    ];
}
