// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The s2n-bignum routines `mid::p521` uses, with their contracts, over
//! fiat-crypto's P-521 field arithmetic on the parent module's limbs, and
//! rind's arithmetic mod the group order, plus the public twin
//! multiplication that `mid::p521` composes from them on other backends.
//!
//! fiat-crypto proves each field operation correct, and emits it as
//! straight-line code with no secret-dependent branch or index.  Mod n,
//! rind multiplies by Montgomery's method, limb by limb over 576 bits
//! (CIOS), in loops whose bounds and indices are public: the fiat-crypto
//! crate has no arithmetic mod n, and for 32-bit limbs, the 17-limb output
//! fiat-crypto's generator gives overflows rustc's stack in debug builds,
//! and its 9-word one, in 64-bit words, measured 5x slower on armv7.  The rest
//! composes those: the point formulas repeat s2n-bignum's,
//! and every coordinate is fully reduced, so results match it word for
//! word; inversion is Fermat's little theorem, raising to a public exponent
//! by a fixed sequence of squarings and multiplications; reduction mod n
//! folds the bits above 2^521 into 2^521 mod n, which is below 2^260, then
//! subtracts n at most once; and scalar multiplication is by Booth-recoded
//! 5-bit windows, after negating a scalar above n / 2 so that no addition
//! doubles.
//!
//! Arithmetic on secrets wraps: the bounds rule out overflow, and a debug
//! build's overflow check would branch on secret values.

use super::fiat_p521::fiat_p521_loose_field_element as Loose;
use super::fiat_p521::fiat_p521_tight_field_element as Fe;
use super::{Limb, Wide, fiat_p521 as fp};

/// fiat-crypto's limbs in a field element, which are not all full.
const FE_LIMBS: usize = size_of::<Fe>() / size_of::<Limb>();

/// Limbs in a value mod n, which take 576 bits.
const LIMBS: usize = (576 / Limb::BITS) as usize;

/// z := (x * y) mod p_521, assuming x and y reduced
pub(crate) fn bignum_mul_p521(z: &mut [u64; 9], x: &[u64; 9], y: &[u64; 9]) {
    *z = words(&fe_mul(&fe(x), &fe(y)));
}

/// z := (x^2) mod p_521, assuming x reduced
pub(crate) fn bignum_sqr_p521(z: &mut [u64; 9], x: &[u64; 9]) {
    *z = words(&fe_sqr(&fe(x)));
}

/// z := (x + y) mod p_521, assuming x and y reduced
pub(crate) fn bignum_add_p521(z: &mut [u64; 9], x: &[u64; 9], y: &[u64; 9]) {
    *z = words(&fe_add(&fe(x), &fe(y)));
}

/// z := (-x) mod p_521, assuming x reduced
pub(crate) fn bignum_neg_p521(z: &mut [u64; 9], x: &[u64; 9]) {
    *z = words(&fe_opp(&fe(x)));
}

/// z := x^-1 mod p_521, for any x coprime to p_521, reduced or not
pub(crate) fn bignum_inv_p521(z: &mut [u64; 9], x: &[u64; 9]) {
    // 2^521 is 1 mod p, so x is its low 521 bits plus the rest.
    let mut low = *x;
    low[8] &= 0x1ff;
    let high = [x[8] >> 9, 0, 0, 0, 0, 0, 0, 0, 0];
    *z = words(&fe_invert(&fe_add(&fe(&low), &fe(&high))));
}

/// z := x mod n_521
pub(crate) fn bignum_mod_n521(z: &mut [u64; 9], x: &[u64; 9]) {
    // x is high * 2^521 + low, and 2^521 is n + C, so x is low + high * C
    // mod n, which is below 2^521 + 2^55 * 2^259, so below 2n.
    let high = x[8] >> 9;
    let mut r = *x;
    r[8] &= 0x1ff;
    let mut r: [Limb; LIMBS] = split(&r);
    let c: [Limb; (320 / Limb::BITS) as usize] = split(&C);
    // high * C, a limb of high at a time, each a product that a limb and
    // carry cannot overflow.
    for shift in 0..(64 / Limb::BITS) as usize {
        let part = (high >> (Limb::BITS as usize * shift)) as Limb;
        let mut carry = 0;
        for (i, r) in r.iter_mut().enumerate().skip(shift) {
            let t = mul_add(*r, part, c.get(i - shift).copied().unwrap_or(0), carry);
            *r = t as Limb;
            carry = t >> Limb::BITS;
        }
    }

    *z = join(&subtract_n_if_above(&r));
}

/// Viewing table as rows of 18 words width, copy the 18 words at
/// table[index - 1] into z.  If `index` is zero or past the last row,
/// `z` is set to zero (ie, the affine point at infinity).
pub(crate) fn bignum_aff_point_select_p521(z: &mut [u64; 18], table: &[u64], index: u8) {
    row_select(z, table, index);
}

fn row_select<const W: usize>(z: &mut [u64; W], table: &[u64], index: u8) {
    *z = [0; W];
    let (rows, _) = table.as_chunks::<W>();
    for (i, row) in (1u64..).zip(rows) {
        let mask = !mask_nonzero(i ^ u64::from(index));
        for (z, w) in z.iter_mut().zip(row) {
            *z |= w & mask;
        }
    }
}

/// p3 := p1 + p2, as Jacobian points over p_521.
///
/// Both z must be nonzero, and p1 and p2 neither the same point nor
/// opposites.
pub(crate) fn p521_jadd(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 27]) {
    *p3 = point(&jadd(&coords(p1), &coords(p2)));
}

/// p3 := p1 + p2, for a Jacobian p1 and an affine p2 (whose z is
/// implicitly one), over p_521.
///
/// p1's z must be nonzero, and p1 and p2 neither the same point nor
/// opposites.
pub(crate) fn p521_jmixadd(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 18]) {
    let (xy2, _) = p2.as_chunks::<9>();
    *p3 = point(&jmixadd(&coords(p1), &fe(&xy2[0]), &fe(&xy2[1])));
}

/// p3 := 2 * p1, as a Jacobian point over p_521, whose z must be nonzero.
pub(crate) fn p521_jdouble(p3: &mut [u64; 27], p1: &[u64; 27]) {
    *p3 = point(&jdouble(&coords(p1)));
}

/// res := scalar * point, as Jacobian points over p_521, for a `point` on
/// the curve.  The result is at infinity, with a zero z, if `point` is or
/// `scalar` is a multiple of n.
///
/// This matches s2n-bignum's in the point it represents, not its words.
pub(crate) fn p521_jscalarmul(res: &mut [u64; 27], scalar: &[u64; 9], point_in: &[u64; 27]) {
    let mut k = [0; 9];
    bignum_mod_n521(&mut k, scalar);
    let mut p = coords(point_in);
    let point_at_infinity = 1u8.wrapping_sub(nonzero(&p[2]));

    // Above n / 2, use n - k and -P, so that k is below n / 2.  Before each
    // addition, the accumulator is 32m P and the table point d P for the
    // value m of the windows above and a digit d of at most 16, and 32m + d,
    // the value of the windows so far, is below n / 2.  So they are equal
    // only if 32m + d is 2d, when m is zero and the accumulator is at
    // infinity, which is selected around, and opposite only if 32m + d is
    // zero, which leaves the accumulator at infinity too.
    let (neg_k, _) = sub(&split(&N), &split(&k));
    let (_, above_half) = sub(&split(&HALF_N), &split(&k));
    let above_half = opaque(above_half as u8);
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
        let mut r = [Fe([0; FE_LIMBS]); 3];
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
        // Doubling keeps a zero z zero.
        for _ in 0..5 {
            acc = jdouble(&acc);
        }
        let term = lookup(digit, sign);
        let sum = jadd(&acc, &term);
        let at_infinity = 1u8.wrapping_sub(nonzero(&acc[2]));
        let sum = select_point(at_infinity, &sum, &term);
        acc = select_point(nonzero_u8(digit), &acc, &sum);
    }

    let infinity = [Fe([0; FE_LIMBS]); 3];
    *res = point(&select_point(point_at_infinity, &acc, &infinity));
}

/// The 105 Booth-recoded 5-bit windows of `k`, highest first, each a digit
/// and its sign, as `mid::p521`'s.
fn booth_w5(k: &[u64; 9]) -> impl Iterator<Item = (u8, u8)> {
    let mut bytes = [0u8; 73];
    for (chunk, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(k) {
        *chunk = word.to_le_bytes();
    }
    (0..=104).rev().map(move |w: usize| {
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

/// The point formulas of s2n-bignum's `p521_jadd`.
fn jadd([x1, y1, z1]: &[Fe; 3], [x2, y2, z2]: &[Fe; 3]) -> [Fe; 3] {
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
    [x3, y3, z3]
}

/// The point formulas of s2n-bignum's `p521_jmixadd`.
fn jmixadd(p1: &[Fe; 3], x2: &Fe, y2: &Fe) -> [Fe; 3] {
    jmixadd_finish(p1, &jmixadd_start(p1, x2, y2))
}

/// The first steps of [`jmixadd`]: p2's x scaled to p1's z, and the
/// differences of the points' x's and y's there, both zero when the points
/// are equal and the x's alone when they are opposite.
struct MixAddStart {
    x2a: Fe,
    xd: Fe,
    yd: Fe,
}

fn jmixadd_start([x1, y1, z1]: &[Fe; 3], x2: &Fe, y2: &Fe) -> MixAddStart {
    let z1sq = fe_sqr(z1);
    let y2a = fe_mul(&z1sq, &fe_mul(z1, y2));
    let x2a = fe_mul(&z1sq, x2);
    MixAddStart {
        xd: fe_sub(&x2a, x1),
        yd: fe_sub(&y2a, y1),
        x2a,
    }
}

fn jmixadd_finish([x1, y1, z1]: &[Fe; 3], MixAddStart { x2a, xd, yd }: &MixAddStart) -> [Fe; 3] {
    let zz = fe_sqr(xd);
    let ww = fe_sqr(yd);
    let zzx1 = fe_mul(&zz, x1);
    let zzx2 = fe_mul(&zz, x2a);

    let x3 = fe_sub(&fe_sub(&ww, &zzx1), &zzx2);
    let t1 = fe_mul(&fe_sub(&zzx2, &zzx1), y1);
    let y3 = fe_sub(&fe_mul(yd, &fe_sub(&zzx1, &x3)), &t1);
    let z3 = fe_mul(xd, z1);
    [x3, y3, z3]
}

/// A public scalar's NAF digits, low first, and the odd multiples of its
/// point they pick: digit d picks `odd_multiples[|d| / 2]`, negated when d
/// is negative.
pub(crate) struct Naf<'a> {
    pub(crate) digits: &'a [i8; 522],
    /// Affine points, x then y, at most 16.
    pub(crate) odd_multiples: &'a [[u64; 18]],
}

/// res := g * G + p * P, for public scalars g and p given as NAFs over
/// odd multiples of G and P, as `mid::p521` composes it from s2n-bignum's
/// point routines on the other backends.
///
/// This keeps the coordinates in fiat-crypto's limbs throughout, sparing
/// a conversion of each at every doubling and addition.  Any sum is
/// handled: the accumulator at infinity, equal to the point added, which
/// doubles, or opposite it, which gives infinity, with a zero z.
pub(crate) fn p521_public_twin_multiply(res: &mut [u64; 27], g: &Naf<'_>, p: &Naf<'_>) {
    let table = |naf: &Naf<'_>| {
        let mut table = [[Fe([0; FE_LIMBS]); 2]; 16];
        for (entry, point) in table.iter_mut().zip(naf.odd_multiples) {
            let (xy, _) = point.as_chunks::<9>();
            *entry = [fe(&xy[0]), fe(&xy[1])];
        }
        table
    };
    let (g_table, p_table) = (table(g), table(p));
    let one = fe(&ONE);

    // `None` at infinity.
    let mut acc: Option<[Fe; 3]> = None;
    for i in (0..522).rev() {
        acc = acc.map(|acc| jdouble(&acc));
        for (digit, table) in [(p.digits[i], &p_table), (g.digits[i], &g_table)] {
            if digit == 0 {
                continue;
            }
            let [x, mut y] = table[usize::from(digit.unsigned_abs() / 2)];
            if digit < 0 {
                y = fe_opp(&y);
            }
            acc = match acc {
                None => Some([x, y, one]),
                Some(acc) => {
                    let start = jmixadd_start(&acc, &x, &y);
                    if !public_is_zero(&start.xd) {
                        Some(jmixadd_finish(&acc, &start))
                    } else if public_is_zero(&start.yd) {
                        Some(jdouble(&acc))
                    } else {
                        None
                    }
                }
            };
        }
    }

    *res = match acc {
        Some(acc) => point(&acc),
        None => [0; 27],
    };
}

/// Whether `x` is zero mod p, for a public `x`.
fn public_is_zero(x: &Fe) -> bool {
    words(x) == [0; 9]
}

/// The point formulas of s2n-bignum's `p521_jdouble`.
fn jdouble([x, y, z]: &[Fe; 3]) -> [Fe; 3] {
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

// The routines below take the modulus, as s2n-bignum's are generic over
// it.  `mid::p521` passes only n_521, which `low::generic::order` routes
// here, so any other is refused.

/// z := x * y / 2^576 mod m, for m = n_521, assuming x and y reduced
pub(crate) fn bignum_montmul(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    z.copy_from_slice(&join(&mont_mul(&split(&scalar(x)), &split(&scalar(y)))));
}

/// z := x / 2^576 mod m, for m = n_521, assuming x reduced
pub(crate) fn bignum_demont(z: &mut [u64], x: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    z.copy_from_slice(&join(&mont_mul(&split(&scalar(x)), &split(&ONE))));
}

/// z := (x + y) mod m, for m = n_521, assuming x and y reduced
pub(crate) fn bignum_modadd(z: &mut [u64], x: &[u64], y: &[u64], m: &[u64]) {
    assert_eq!(m, N);
    // Below 2n < 2^576, so the sum never carries out.
    let (sum, _) = add(&split(&scalar(x)), &split(&scalar(y)));
    z.copy_from_slice(&join(&subtract_n_if_above(&sum)));
}

/// z := a^-1 mod b, for b = n_521, or zero if a is zero mod n_521
///
/// `_t` is s2n-bignum's scratch space, which this does not need.
pub(crate) fn bignum_modinv(z: &mut [u64], a: &[u64], b: &[u64], _t: &mut [u64]) {
    assert_eq!(b, N);
    let mut a_reduced = [0; 9];
    bignum_mod_n521(&mut a_reduced, &scalar(a));
    let a_mont = mont_mul(&split(&a_reduced), &split(&MM));
    let r = mont_pow(&a_mont, &N_MINUS_2);
    z.copy_from_slice(&join(&mont_mul(&r, &split(&ONE))));
}

/// z := 2^1152 mod m, for m = n_521
// Checks the constant against s2n-bignum, which armv7 lacks.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
pub(crate) fn bignum_montifier(z: &mut [u64], m: &[u64], _t: &mut [u64]) {
    assert_eq!(m, N);
    z.copy_from_slice(&MM);
}

/// `x^(p - 2)`, which is `x^-1` for a nonzero `x`, by an addition chain
/// of 520 squarings and 13 multiplications.
fn fe_invert(x: &Fe) -> Fe {
    let sqr_n = |x: &Fe, n: usize| (0..n).fold(*x, |acc, _| fe_sqr(&acc));

    // x_k is x^(2^k - 1), whose exponent is k one bits.
    let x2 = fe_mul(&fe_sqr(x), x);
    let x3 = fe_mul(&fe_sqr(&x2), x);
    let x4 = fe_mul(&sqr_n(&x2, 2), &x2);
    let x7 = fe_mul(&sqr_n(&x4, 3), &x3);
    let x8 = fe_mul(&sqr_n(&x4, 4), &x4);
    let x16 = fe_mul(&sqr_n(&x8, 8), &x8);
    let x32 = fe_mul(&sqr_n(&x16, 16), &x16);
    let x64 = fe_mul(&sqr_n(&x32, 32), &x32);
    let x128 = fe_mul(&sqr_n(&x64, 64), &x64);
    let x256 = fe_mul(&sqr_n(&x128, 128), &x128);
    let x512 = fe_mul(&sqr_n(&x256, 256), &x256);
    let x519 = fe_mul(&sqr_n(&x512, 7), &x7);

    // p - 2 is 519 ones, a zero, and a one.
    fe_mul(&sqr_n(&x519, 2), x)
}

/// `x^e` mod n_521, in the Montgomery domain, for a public exponent `e`,
/// by a fixed 4-bit window starting at `e`'s top window.
///
/// The exponent picks the table entries, so it must not be secret.
fn mont_pow(x: &[Limb; LIMBS], e: &[u64; 9]) -> [Limb; LIMBS] {
    let one = mont_mul(&split(&ONE), &split(&MM));
    let mut table = [one; 16];
    for i in 1..table.len() {
        table[i] = mont_mul(&table[i - 1], x);
    }

    let window = |bit: usize| ((e[bit / 64] >> (bit % 64)) & 0xf) as usize;
    let mut acc = one;
    for bit in (0..576)
        .step_by(4)
        .rev()
        .skip_while(|&bit| window(bit) == 0)
    {
        for _ in 0..4 {
            acc = mont_mul(&acc, &acc);
        }
        acc = mont_mul(&acc, &table[window(bit)]);
    }
    acc
}

/// `x * y / 2^576 mod n`, for `x` and `y` below n, by Montgomery's method
/// with the multiplication and reduction interleaved limb by limb (CIOS).
///
/// Each step adds `x * y[i]`, then the multiple of n that zeroes the low
/// limb, and drops it.  The running value stays below 2n, so the limbs and
/// the two above them hold it, and one subtraction of n reduces it.
fn mont_mul(x: &[Limb; LIMBS], y: &[Limb; LIMBS]) -> [Limb; LIMBS] {
    let n: [Limb; LIMBS] = split(&N);
    let mut t = [0; LIMBS + 2];
    for yi in y {
        let mut carry = 0;
        for (t, x) in t.iter_mut().zip(x) {
            let s = mul_add(*t, *x, *yi, carry);
            *t = s as Limb;
            carry = s >> Limb::BITS;
        }
        let s = Wide::from(t[LIMBS]).wrapping_add(carry);
        t[LIMBS] = s as Limb;
        t[LIMBS + 1] = (s >> Limb::BITS) as Limb;

        let m = t[0].wrapping_mul(N_INV_NEG);
        let mut carry = mul_add(t[0], m, n[0], 0) >> Limb::BITS;
        for j in 1..LIMBS {
            let s = mul_add(t[j], m, n[j], carry);
            t[j - 1] = s as Limb;
            carry = s >> Limb::BITS;
        }
        let s = Wide::from(t[LIMBS]).wrapping_add(carry);
        t[LIMBS - 1] = s as Limb;
        t[LIMBS] = t[LIMBS + 1].wrapping_add((s >> Limb::BITS) as Limb);
        t[LIMBS + 1] = 0;
    }
    // Below 2n < 2^576, so t[LIMBS] is zero.
    subtract_n_if_above(&t[..LIMBS].try_into().unwrap())
}

/// `x - n` if `x` is at least n, else `x`, for `x` below 2n.
fn subtract_n_if_above(x: &[Limb; LIMBS]) -> [Limb; LIMBS] {
    let (diff, borrow) = sub(x, &split(&N));
    select_words(opaque(borrow as u8), &diff, x)
}

/// `a + b * c + carry`, which at most fills two limbs.
fn mul_add(a: Limb, b: Limb, c: Limb, carry: Wide) -> Wide {
    Wide::from(a)
        .wrapping_add(Wide::from(b).wrapping_mul(Wide::from(c)))
        .wrapping_add(carry)
}

/// `x + y`, and the carry out.
fn add(x: &[Limb; LIMBS], y: &[Limb; LIMBS]) -> ([Limb; LIMBS], Limb) {
    let mut carry = 0;
    let r = core::array::from_fn(|i| {
        let s = Wide::from(x[i])
            .wrapping_add(Wide::from(y[i]))
            .wrapping_add(carry);
        carry = s >> Limb::BITS;
        s as Limb
    });
    (r, carry as Limb)
}

/// `x - y`, and 1 if it borrowed.
fn sub(x: &[Limb; LIMBS], y: &[Limb; LIMBS]) -> ([Limb; LIMBS], Limb) {
    let mut borrow = 0;
    let r = core::array::from_fn(|i| {
        let d = Wide::from(x[i])
            .wrapping_sub(Wide::from(y[i]))
            .wrapping_sub(borrow);
        borrow = d >> (Wide::BITS - 1);
        d as Limb
    });
    (r, borrow as Limb)
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select_words(flag: u8, if_zero: &[Limb; LIMBS], if_nonzero: &[Limb; LIMBS]) -> [Limb; LIMBS] {
    let mask = Limb::from(flag).wrapping_neg();
    core::array::from_fn(|i| (if_nonzero[i] & mask) | (if_zero[i] & !mask))
}

fn scalar(x: &[u64]) -> [u64; 9] {
    x.try_into().unwrap()
}

/// The limbs of `x`, low first.
fn split<const N: usize, const W: usize>(x: &[u64; N]) -> [Limb; W] {
    let per_word = (64 / Limb::BITS) as usize;
    core::array::from_fn(|i| {
        x.get(i / per_word)
            .map_or(0, |w| (w >> (Limb::BITS as usize * (i % per_word))) as Limb)
    })
}

/// The 64-bit words of a value mod n's limbs, low first.
fn join(x: &[Limb; LIMBS]) -> [u64; 9] {
    let mut r = [0u64; 9];
    for (i, limb) in x.iter().enumerate() {
        r[i * 9 / LIMBS] |= u64::from(*limb) << (Limb::BITS as usize * i % 64);
    }
    r
}

/// The bit at which fiat-crypto's limb `i` starts: limbs split 521 bits
/// as evenly as they can, the wider first, as its `eval` lists them.
const fn offset(i: usize) -> usize {
    (521 * i).div_ceil(FE_LIMBS)
}

/// The field element of `x`, a value below 2^521, by cutting its words at
/// the limbs' offsets: every limb is then within its width, so within
/// fiat-crypto's tight bounds.
///
/// This and [`words`] convert by shifts rather than through
/// fiat-crypto's byte encoding, which costs a third of a field
/// multiplication a round trip, and every routine here converts each
/// operand and result.
fn fe(x: &[u64; 9]) -> Fe {
    Fe(core::array::from_fn(|i| {
        let (start, width) = (offset(i), offset(i + 1) - offset(i));
        let (word, shift) = (start / 64, start % 64);
        let mut v = x[word] >> shift;
        if shift + width > 64 {
            v |= x[word + 1] << (64 - shift);
        }
        (v & ((1 << width) - 1)) as Limb
    }))
}

/// The words of `x`, fully reduced.
///
/// A tight limb reaches one past its width, so the value can reach p and
/// above.  As `fiat_p521_to_bytes` does, this subtracts p, limb by limb
/// with the borrow carried, then adds p back if that borrowed out, which
/// leaves each limb within its width; then it packs the limbs into words.
fn words(x: &Fe) -> [u64; 9] {
    // Each limb of p is all ones across its width.
    let mask = |i: usize| -> Limb { (1 << (offset(i + 1) - offset(i))) - 1 };
    let mut borrow: Wide = 0;
    let mut r: [Limb; FE_LIMBS] = core::array::from_fn(|i| {
        let d = Wide::from(x.0[i])
            .wrapping_sub(Wide::from(mask(i)))
            .wrapping_sub(borrow);
        borrow = d >> (Wide::BITS - 1);
        d as Limb & mask(i)
    });
    let add_back = Limb::from(opaque(borrow as u8)).wrapping_neg();
    let mut carry: Limb = 0;
    for (i, r) in r.iter_mut().enumerate() {
        let s = r.wrapping_add(mask(i) & add_back).wrapping_add(carry);
        carry = s >> (offset(i + 1) - offset(i));
        *r = s & mask(i);
    }

    let mut z = [0u64; 9];
    for (i, limb) in r.iter().enumerate() {
        let (word, shift) = (offset(i) / 64, offset(i) % 64);
        let v = u64::from(*limb);
        z[word] |= v << shift;
        if shift + (offset(i + 1) - offset(i)) > 64 {
            z[word + 1] |= v >> (64 - shift);
        }
    }
    z
}

fn relax(x: &Fe) -> Loose {
    let mut r = Loose([0; FE_LIMBS]);
    fp::fiat_p521_relax(&mut r, x);
    r
}

fn carry(x: &Loose) -> Fe {
    let mut r = Fe([0; FE_LIMBS]);
    fp::fiat_p521_carry(&mut r, x);
    r
}

fn fe_mul(x: &Fe, y: &Fe) -> Fe {
    let mut r = Fe([0; FE_LIMBS]);
    fp::fiat_p521_carry_mul(&mut r, &relax(x), &relax(y));
    r
}

fn fe_sqr(x: &Fe) -> Fe {
    let mut r = Fe([0; FE_LIMBS]);
    fp::fiat_p521_carry_square(&mut r, &relax(x));
    r
}

fn fe_add(x: &Fe, y: &Fe) -> Fe {
    let mut r = Loose([0; FE_LIMBS]);
    fp::fiat_p521_add(&mut r, x, y);
    carry(&r)
}

fn fe_double(x: &Fe) -> Fe {
    fe_add(x, x)
}

fn fe_sub(x: &Fe, y: &Fe) -> Fe {
    let mut r = Loose([0; FE_LIMBS]);
    fp::fiat_p521_sub(&mut r, x, y);
    carry(&r)
}

fn fe_opp(x: &Fe) -> Fe {
    let mut r = Loose([0; FE_LIMBS]);
    fp::fiat_p521_opp(&mut r, x);
    carry(&r)
}

/// 1 if `x` is nonzero mod p, else 0.
fn nonzero(x: &Fe) -> u8 {
    let any = words(x).iter().fold(0, |acc, w| acc | w);
    opaque(((any | any.wrapping_neg()) >> 63) as u8)
}

/// 1 if `x` is nonzero, else 0.
fn nonzero_u8(x: u8) -> u8 {
    opaque(((u32::from(x) | u32::from(x).wrapping_neg()) >> 31) as u8)
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select(flag: u8, if_zero: &Fe, if_nonzero: &Fe) -> Fe {
    let mut r = Fe([0; FE_LIMBS]);
    fp::fiat_p521_selectznz(&mut r.0, flag, &if_zero.0, &if_nonzero.0);
    r
}

/// `if_nonzero` if `flag` is 1, else `if_zero`.
fn select_point(flag: u8, if_zero: &[Fe; 3], if_nonzero: &[Fe; 3]) -> [Fe; 3] {
    core::array::from_fn(|i| select(flag, &if_zero[i], &if_nonzero[i]))
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

fn coords(p: &[u64; 27]) -> [Fe; 3] {
    let (words, _) = p.as_chunks::<9>();
    [fe(&words[0]), fe(&words[1]), fe(&words[2])]
}

fn point(p: &[Fe; 3]) -> [u64; 27] {
    let mut r = [0u64; 27];
    let (out, _) = r.as_chunks_mut::<9>();
    for (out, coord) in out.iter_mut().zip(p) {
        *out = words(coord);
    }
    r
}

/// n_521, the group order, as little-endian words.
pub(crate) const N: [u64; 9] = [
    0xbb6f_b71e_9138_6409,
    0x3bb5_c9b8_899c_47ae,
    0x7fcc_0148_f709_a5d0,
    0x5186_8783_bf2f_966b,
    0xffff_ffff_ffff_fffa,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x0000_0000_0000_01ff,
];

const N_MINUS_2: [u64; 9] = [
    0xbb6f_b71e_9138_6407,
    0x3bb5_c9b8_899c_47ae,
    0x7fcc_0148_f709_a5d0,
    0x5186_8783_bf2f_966b,
    0xffff_ffff_ffff_fffa,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x0000_0000_0000_01ff,
];

/// (n_521 - 1) / 2
const HALF_N: [u64; 9] = [
    0x5db7_db8f_489c_3204,
    0x1dda_e4dc_44ce_23d7,
    0xbfe6_00a4_7b84_d2e8,
    0x28c3_43c1_df97_cb35,
    0xffff_ffff_ffff_fffd,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x0000_0000_0000_00ff,
];

/// 1, as little-endian words.
const ONE: [u64; 9] = [1, 0, 0, 0, 0, 0, 0, 0, 0];

/// 2^1152 mod n_521, the Montgomery factor squared.
const MM: [u64; 9] = [
    0x137c_d04d_cf15_dd04,
    0xf707_badc_e554_7ea3,
    0x12a7_8d38_7945_73ff,
    0xd372_1ef5_57f7_5e06,
    0xdd6e_23d8_2e49_c7db,
    0xcff3_d142_b775_6e3e,
    0x5bcc_6d61_a8e5_67bc,
    0x2d8e_03d1_492d_0d45,
    0x0000_0000_0000_003d,
];

/// -n_521^-1 mod 2^b, for b bits a limb: correct to 5 bits, then Newton's
/// iteration doubles that each time.
const N_INV_NEG: Limb = {
    let n = N[0] as Limb;
    let mut inv = n.wrapping_mul(3) ^ 2;
    let mut i = 0;
    while i < 4 {
        inv = inv.wrapping_mul(Limb::wrapping_sub(2, n.wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
};

/// 2^521 - n_521, as little-endian words.
const C: [u64; 5] = [
    0x4490_48e1_6ec7_9bf7,
    0xc44a_3647_7663_b851,
    0x8033_feb7_08f6_5a2f,
    0xae79_787c_40d0_6994,
    0x0000_0000_0000_0005,
];

/// Checks each routine against s2n-bignum's: word for word, except the
/// scalar multiplication, by the point it represents.
///
/// Inputs that are secret in `mid::p521` are marked secret, so under
/// `admin/ctgrind` these also check each routine is constant time in them.
#[cfg(all(test, any(rind_backend = "x86_64", rind_backend = "aarch64")))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::low;
    use crate::low::ct::{into_public, into_secret};

    const P: [u64; 9] = [
        u64::MAX,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        u64::MAX,
        0x1ff,
    ];

    /// Any 576-bit value, biased towards the moduli's edges.
    fn raw() -> impl Strategy<Value = [u64; 9]> {
        prop_oneof![
            8 => any::<[u64; 9]>(),
            1 => prop_oneof![
                Just([0; 9]),
                Just([1, 0, 0, 0, 0, 0, 0, 0, 0]),
                Just(add_small(P, -1)),
                Just(P),
                Just(add_small(N, -1)),
                Just(N),
                Just(add_small(N, 1)),
                Just(HALF_N),
                Just(add_small(HALF_N, 1)),
                Just([u64::MAX; 9]),
            ],
        ]
    }

    /// `x + d`, for a low word that neither carries nor borrows.
    fn add_small(mut x: [u64; 9], d: i64) -> [u64; 9] {
        x[0] = x[0].checked_add_signed(d).unwrap();
        x
    }

    /// A field element below p, including 0, 1, and p - 1.
    fn field() -> impl Strategy<Value = [u64; 9]> {
        prop_oneof![
            8 => any::<[u64; 9]>().prop_map(|mut x| {
                x[8] &= 0x1ff;
                if x == P { [0; 9] } else { x }
            }),
            1 => prop_oneof![
                Just([0; 9]),
                Just([1, 0, 0, 0, 0, 0, 0, 0, 0]),
                Just(add_small(P, -1)),
            ],
        ]
    }

    /// A scalar below n, including 0, 1, and n - 1.
    fn scalar() -> impl Strategy<Value = [u64; 9]> {
        raw().prop_map(|x| {
            let mut r = [0; 9];
            low::bignum_mod_n521(&mut r, &x);
            r
        })
    }

    /// A Jacobian point: a multiple of G with a random nonzero z.
    fn point() -> impl Strategy<Value = [u64; 27]> {
        (0..64u32, field()).prop_map(|(doublings, lambda)| {
            let mut p = GENERATOR;
            for _ in 0..doublings {
                let q = p;
                low::p521_jdouble(&mut p, &q);
            }
            let lambda = if lambda == [0; 9] {
                [1, 0, 0, 0, 0, 0, 0, 0, 0]
            } else {
                lambda
            };
            rescale(&p, &lambda)
        })
    }

    /// (x * l^2, y * l^3, z * l), the same point for a nonzero l.
    fn rescale(p: &[u64; 27], lambda: &[u64; 9]) -> [u64; 27] {
        let mut l2 = [0; 9];
        low::bignum_sqr_p521(&mut l2, lambda);
        let mut l3 = [0; 9];
        low::bignum_mul_p521(&mut l3, &l2, lambda);
        let mut r = [0; 27];
        let (out, _) = r.as_chunks_mut::<9>();
        let (coords, _) = p.as_chunks::<9>();
        low::bignum_mul_p521(&mut out[0], &coords[0], &l2);
        low::bignum_mul_p521(&mut out[1], &coords[1], &l3);
        low::bignum_mul_p521(&mut out[2], &coords[2], lambda);
        r
    }

    /// (x / z^2, y / z^3), or `None` at infinity.
    fn affine(p: &[u64; 27]) -> Option<[u64; 18]> {
        let (coords, _) = p.as_chunks::<9>();
        if coords[2] == [0; 9] {
            return None;
        }
        let mut z = [0; 9];
        low::bignum_inv_p521(&mut z, &coords[2]);
        let (mut z2, mut z3) = ([0; 9], [0; 9]);
        low::bignum_sqr_p521(&mut z2, &z);
        low::bignum_mul_p521(&mut z3, &z2, &z);
        let mut r = [0; 18];
        let (out, _) = r.as_chunks_mut::<9>();
        low::bignum_mul_p521(&mut out[0], &coords[0], &z2);
        low::bignum_mul_p521(&mut out[1], &coords[1], &z3);
        Some(r)
    }

    fn same_point(a: &[u64; 27], b: &[u64; 27]) -> bool {
        affine(a) == affine(b)
    }

    proptest! {
        #[test]
        fn field_ops(x in field(), y in field()) {
            let (sx, sy) = (into_secret(x), into_secret(y));
            let (mut ours, mut theirs) = ([0; 9], [0; 9]);

            bignum_mul_p521(&mut ours, &sx, &sy);
            low::bignum_mul_p521(&mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_sqr_p521(&mut ours, &sx);
            low::bignum_sqr_p521(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_add_p521(&mut ours, &sx, &sy);
            low::bignum_add_p521(&mut theirs, &x, &y);
            prop_assert_eq!(into_public(ours), theirs);

            bignum_neg_p521(&mut ours, &sx);
            low::bignum_neg_p521(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn field_inv(x in raw()) {
            // s2n-bignum leaves the inverse of a multiple of p unspecified.
            let mut low = x;
            low[8] &= 0x1ff;
            let high = [x[8] >> 9, 0, 0, 0, 0, 0, 0, 0, 0];
            prop_assume!(words(&fe_add(&fe(&low), &fe(&high))) != [0; 9]);
            let (mut ours, mut theirs) = ([0; 9], [0; 9]);
            bignum_inv_p521(&mut ours, &into_secret(x));
            low::bignum_inv_p521(&mut theirs, &x);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_add(p in point(), q in point()) {
            prop_assume!(!same_point(&p, &q));
            let mut neg_q = q;
            low::bignum_neg_p521(&mut neg_q.as_chunks_mut::<9>().0[1], &q.as_chunks::<9>().0[1]);
            prop_assume!(!same_point(&p, &neg_q));
            let (sp, sq) = (into_secret(p), into_secret(q));
            let (mut ours, mut theirs) = ([0; 27], [0; 27]);
            p521_jadd(&mut ours, &sp, &sq);
            low::p521_jadd(&mut theirs, &p, &q);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_mixadd(p in point(), q in point()) {
            prop_assume!(!same_point(&p, &q));
            let q = affine(&q).unwrap();
            let mut neg = [0; 27];
            neg[..18].copy_from_slice(&q);
            neg[18] = 1;
            low::bignum_neg_p521(&mut neg.as_chunks_mut::<9>().0[1], &q.as_chunks::<9>().0[1]);
            prop_assume!(!same_point(&p, &neg));
            let (sp, sq) = (into_secret(p), into_secret(q));
            let (mut ours, mut theirs) = ([0; 27], [0; 27]);
            p521_jmixadd(&mut ours, &sp, &sq);
            low::p521_jmixadd(&mut theirs, &p, &q);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_double(p in point()) {
            let sp = into_secret(p);
            let (mut ours, mut theirs) = ([0; 27], [0; 27]);
            p521_jdouble(&mut ours, &sp);
            low::p521_jdouble(&mut theirs, &p);
            prop_assert_eq!(into_public(ours), theirs);
        }

        #[test]
        fn point_select(table in prop::collection::vec(any::<u64>(), 288), index: u8) {
            let index = index % 20;
            let (mut ours, mut theirs) = ([0; 18], [0; 18]);
            bignum_aff_point_select_p521(&mut ours, &table, into_secret(index));
            low::bignum_aff_point_select_p521(&mut theirs, &table, index);
            prop_assert_eq!(into_public(ours), theirs);
        }
    }

    // Each case scalar-multiplies or inverts, which is slow in a debug build.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn scalar_multiply(k in raw(), p in point()) {
            let (mut ours, mut theirs) = ([0; 27], [0; 27]);
            p521_jscalarmul(&mut ours, &into_secret(k), &into_secret(p));
            low::p521_jscalarmul(&mut theirs, &k, &p);
            let ours = into_public(ours);
            prop_assert!(same_point(&ours, &theirs));
        }

        #[test]
        fn twin_multiply(g in scalar(), p in scalar(), c in 1..40u64, wide: bool) {
            check_twin_multiply(&g, &p, c, wide);
        }

        #[test]
        fn scalar_ops(x in scalar(), y in scalar(), raw in raw()) {
            let (sx, sy, sraw) = (into_secret(x), into_secret(y), into_secret(raw));
            let (mut ours, mut theirs) = ([0; 9], [0; 9]);

            bignum_mod_n521(&mut ours, &sraw);
            low::bignum_mod_n521(&mut theirs, &raw);
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
            if x != [0; 9] {
                bignum_modinv(&mut ours, &sx, &N, &mut [0; 27]);
                low::bignum_modinv(&mut theirs, &x, &N, &mut [0; 27]);
                prop_assert_eq!(into_public(ours), theirs);
            }
        }
    }

    #[test]
    fn scalar_multiply_edges() {
        // Zero, n, and either side of n / 2, where the scalar is negated.
        for k in [
            [0; 9],
            N,
            HALF_N,
            add_small(HALF_N, 1),
            add_small(N, -1),
            [1, 0, 0, 0, 0, 0, 0, 0, 0],
        ] {
            let (mut ours, mut theirs) = ([0; 27], [0; 27]);
            p521_jscalarmul(&mut ours, &k, &GENERATOR);
            low::p521_jscalarmul(&mut theirs, &k, &GENERATOR);
            assert!(same_point(&ours, &theirs), "{k:x?}");
        }
    }

    /// The width-`w` NAF of `k`, low first.
    fn naf(k: &[u64; 9], w: u32) -> [i8; 522] {
        let mut k = *k;
        let mut digits = [0; 522];
        for digit in &mut digits {
            if k[0] & 1 == 1 {
                let low = (k[0] & ((1 << w) - 1)) as i64;
                let d = if low >= 1 << (w - 1) {
                    low - (1 << w)
                } else {
                    low
                };
                // k - d, which clears the low bits or carries out of them.
                let mut carry = d.unsigned_abs();
                for word in &mut k {
                    let (sum, c) = match d < 0 {
                        true => word.overflowing_add(carry),
                        false => word.overflowing_sub(carry),
                    };
                    (*word, carry) = (sum, u64::from(c));
                }
                *digit = d as i8;
            }
            for i in 0..9 {
                k[i] = (k[i] >> 1) | (k.get(i + 1).map_or(0, |w| w << 63));
            }
        }
        assert_eq!(k, [0; 9]);
        digits
    }

    /// Checks `p521_public_twin_multiply` for g * G + p * P, with P = c * G,
    /// against s2n-bignum's scalar multiplication by g + c * p.
    fn check_twin_multiply(g: &[u64; 9], p: &[u64; 9], c: u64, wide: bool) {
        let multiple = |k: u64, point: &[u64; 27]| {
            let mut r = [0; 27];
            low::p521_jscalarmul(&mut r, &[k, 0, 0, 0, 0, 0, 0, 0, 0], point);
            affine(&r).unwrap()
        };
        let mut point = [0; 27];
        point[..18].copy_from_slice(&multiple(c, &GENERATOR));
        point[18] = 1;
        let rows = if wide { 16 } else { 8 };
        let g_multiples: Vec<_> = (0..8).map(|i| multiple(2 * i + 1, &GENERATOR)).collect();
        let p_multiples: Vec<_> = (0..rows).map(|i| multiple(2 * i + 1, &point)).collect();
        let (g_digits, p_digits) = (naf(g, 5), naf(p, if wide { 6 } else { 5 }));

        let mut ours = [0; 27];
        p521_public_twin_multiply(
            &mut ours,
            &Naf {
                digits: &g_digits,
                odd_multiples: &g_multiples,
            },
            &Naf {
                digits: &p_digits,
                odd_multiples: &p_multiples,
            },
        );

        let (mut cp, mut k) = ([0; 9], [0; 9]);
        low::bignum_montmul(&mut cp, &[c, 0, 0, 0, 0, 0, 0, 0, 0], p, &N);
        let cp_mont = cp;
        low::bignum_montmul(&mut cp, &cp_mont, &MM, &N);
        low::bignum_modadd(&mut k, g, &cp, &N);
        let mut theirs = [0; 27];
        low::p521_jscalarmul(&mut theirs, &k, &GENERATOR);
        assert!(same_point(&ours, &theirs), "{g:x?} {p:x?} {c}");
    }

    #[test]
    fn twin_multiply_exceptional() {
        // With P = G or 2G, the accumulator meets the point it adds: equal,
        // which must double, or opposite, which must give infinity.
        let small = |k: u64| [k, 0, 0, 0, 0, 0, 0, 0, 0];
        let n_minus = |k: i64| add_small(N, -k);
        for c in [1, 2] {
            for (g, p) in [
                (small(0), small(0)),
                (small(1), small(0)),
                (small(0), small(1)),
                (small(1), small(1)),
                (small(3), small(3)),
                (small(2), small(1)),
                (small(6), small(3)),
                (small(1), n_minus(1)),
                (n_minus(5), small(5)),
                (n_minus(2), small(1)),
                (n_minus(1), n_minus(1)),
            ] {
                for wide in [false, true] {
                    check_twin_multiply(&g, &p, c, wide);
                }
            }
        }
    }

    #[test]
    fn montifier() {
        let (mut ours, mut theirs) = ([0; 9], [0; 9]);
        bignum_montifier(&mut ours, &N, &mut [0; 9]);
        low::bignum_montifier(&mut theirs, &N, &mut [0; 27]);
        assert_eq!(ours, theirs);
    }

    // Only the top bit set is where an exclusive or of `x` and `-x` would
    // drop it, and only words sharing a bit cancel in an exclusive or.
    #[test]
    fn nonzero_at_the_top_bit() {
        assert_eq!(nonzero(&fe(&[0; 9])), 0);
        assert_eq!(nonzero(&fe(&[1 << 63, 0, 0, 0, 0, 0, 0, 0, 0])), 1);
        assert_eq!(nonzero(&fe(&[1, 1, 0, 0, 0, 0, 0, 0, 0])), 1);
        assert_eq!((nonzero_u8(0), nonzero_u8(1), nonzero_u8(0x80)), (0, 1, 1));
        assert_eq!(mask_nonzero(0), 0);
        assert_eq!(mask_nonzero(1 << 63), u64::MAX);
    }

    #[test]
    #[should_panic]
    fn other_modulus_refused() {
        bignum_modadd(&mut [0; 9], &[1; 9], &[1; 9], &P);
    }

    /// G, with z = 1.
    const GENERATOR: [u64; 27] = [
        0xf97e_7e31_c2e5_bd66,
        0x3348_b3c1_856a_429b,
        0xfe1d_c127_a2ff_a8de,
        0xa14b_5e77_efe7_5928,
        0xf828_af60_6b4d_3dba,
        0x9c64_8139_053f_b521,
        0x9e3e_cb66_2395_b442,
        0x858e_06b7_0404_e9cd,
        0x0000_0000_0000_00c6,
        0x88be_9476_9fd1_6650,
        0x353c_7086_a272_c240,
        0xc550_b901_3fad_0761,
        0x97ee_7299_5ef4_2640,
        0x17af_bd17_273e_662c,
        0x98f5_4449_579b_4468,
        0x5c8a_5fb4_2c7d_1bd9,
        0x3929_6a78_9a3b_c004,
        0x0000_0000_0000_0118,
        1,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
        0,
    ];
}
