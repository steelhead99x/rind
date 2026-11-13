// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The edwards25519 group over s2n-bignum's field and point routines, with a
//! constant-time variable-base scalar multiplication, for ristretto255 and
//! ECVRF.
//!
//! Each field and point routine is HOL Light-proven in s2n-bignum. What this
//! module composes from them (the ladder, the square root of a ratio, the
//! inversion, and the signed recoding) is rind's own, covered by tests only.

use crate::error::Error;
use crate::low;
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::util;

/// An element of GF(p), `p = 2^255 - 19`, as little-endian words, reduced.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Fe(pub(crate) [u64; 4]);

impl Fe {
    pub(crate) const ZERO: Self = Self([0; 4]);
    pub(crate) const ONE: Self = Self([1, 0, 0, 0]);

    /// `d = -121665 / 121666`, the curve's constant.
    pub(crate) const D: Self = Self([
        0x75eb4dca135978a3,
        0x00700a4d4141d8ab,
        0x8cc740797779e898,
        0x52036cee2b6ffe73,
    ]);

    /// The non-negative square root of `-1`.
    pub(crate) const SQRT_M1: Self = Self([
        0xc4ee1b274a0ea0b0,
        0x2f431806ad2fe478,
        0x2b4d00993dfbd7a7,
        0x2b8324804fc1df0b,
    ]);

    /// Reads a little-endian integer modulo `p`, with 1 if it was below `p`,
    /// that is, canonical, else 0.
    pub(crate) fn from_le_bytes(bytes: &[u8; 32]) -> (Self, u64) {
        let x = util::little_endian_to_u64x4(bytes);
        // s2n-bignum's multiplication reduces any 256-bit input.
        (Self::ONE.mul(&Self(x)), low::bignum_cmp_lt(&x, &P))
    }

    pub(crate) fn to_le_bytes(self) -> [u8; 32] {
        util::u64x4_to_little_endian(&self.0)
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let mut z = Self::ZERO;
        low::bignum_add_p25519(&mut z.0, &self.0, &other.0);
        z
    }

    pub(crate) fn sub(&self, other: &Self) -> Self {
        let mut z = Self::ZERO;
        low::bignum_sub_p25519(&mut z.0, &self.0, &other.0);
        z
    }

    pub(crate) fn mul(&self, other: &Self) -> Self {
        let mut z = Self::ZERO;
        low::bignum_mul_p25519(&mut z.0, &self.0, &other.0);
        z
    }

    pub(crate) fn square(&self) -> Self {
        let mut z = Self::ZERO;
        low::bignum_sqr_p25519(&mut z.0, &self.0);
        z
    }

    pub(crate) fn neg(&self) -> Self {
        let mut z = Self::ZERO;
        low::bignum_neg_p25519(&mut z.0, &self.0);
        z
    }

    /// `self^(2^k)`.
    fn square_times(&self, k: u32) -> Self {
        let mut z = *self;
        for _ in 0..k {
            z = z.square();
        }
        z
    }

    /// `self^((p - 5) / 8) = self^(2^252 - 3)`, by ref10's addition chain.
    fn pow_p58(&self) -> Self {
        let x = self;
        let x2 = x.square();
        let x9 = x2.square_times(2).mul(x);
        let x11 = x9.mul(&x2);
        let x_5_0 = x11.square().mul(&x9); // x^(2^5 - 1)
        let x_10_0 = x_5_0.square_times(5).mul(&x_5_0);
        let x_20_0 = x_10_0.square_times(10).mul(&x_10_0);
        let x_40_0 = x_20_0.square_times(20).mul(&x_20_0);
        let x_50_0 = x_40_0.square_times(10).mul(&x_10_0);
        let x_100_0 = x_50_0.square_times(50).mul(&x_50_0);
        let x_200_0 = x_100_0.square_times(100).mul(&x_100_0);
        let x_250_0 = x_200_0.square_times(50).mul(&x_50_0);
        x_250_0.square_times(2).mul(x)
    }

    /// `1 / self`, or 0 for 0, by Fermat's little theorem:
    /// `self^(p - 2) = (self^((p - 5) / 8))^8 * self^3`.
    pub(crate) fn invert(&self) -> Self {
        self.pow_p58().square_times(3).mul(&self.square().mul(self))
    }

    /// 1 if `self` is negative, that is, odd, else 0.
    pub(crate) fn is_negative(&self) -> u64 {
        self.0[0] & 1
    }

    /// 1 if `self == other`, else 0.
    pub(crate) fn ct_eq(&self, other: &Self) -> u64 {
        low::bignum_eq(&self.0, &other.0) as u64
    }

    /// `if_set` if `choice` is nonzero, else `if_unset`.
    pub(crate) fn select(choice: u64, if_set: &Self, if_unset: &Self) -> Self {
        let mut z = Self::ZERO;
        low::bignum_mux(choice, &mut z.0, &if_set.0, &if_unset.0);
        z
    }

    /// `-self` if `choice` is nonzero, else `self`.
    pub(crate) fn negate_if(&self, choice: u64) -> Self {
        Self::select(choice, &self.neg(), self)
    }

    /// The non-negative one of `self` and `-self`.
    pub(crate) fn abs(&self) -> Self {
        self.negate_if(self.is_negative())
    }

    /// `(1, 1 / sqrt(self))`, the non-negative root, if `self` is a nonzero
    /// square, else 0 and an unspecified element.
    pub(crate) fn invsqrt(&self) -> (u64, Self) {
        let mut z = Self::ZERO;
        let legendre = low::bignum_invsqrt_p25519(&mut z.0, &self.0);
        ((legendre == 1) as u64, z)
    }

    /// RFC 9496 4.2's `SQRT_RATIO_M1(u, v)`: `(1, sqrt(u / v))` if `u / v` is
    /// square, `(1, 0)` if `u` is 0, `(0, 0)` if only `v` is, and otherwise
    /// `(0, sqrt(SQRT_M1 * u / v))`, each root non-negative.
    pub(crate) fn sqrt_ratio_m1(u: &Self, v: &Self) -> (u64, Self) {
        let v3 = v.square().mul(v);
        let v7 = v3.square().mul(v);
        let r = u.mul(&v3).mul(&u.mul(&v7).pow_p58());
        let check = v.mul(&r.square());

        let u_neg = u.neg();
        let correct_sign_sqrt = check.ct_eq(u);
        let flipped_sign_sqrt = check.ct_eq(&u_neg);
        let flipped_sign_sqrt_i = check.ct_eq(&u_neg.mul(&Self::SQRT_M1));

        let r_prime = Self::SQRT_M1.mul(&r);
        let r = Self::select(flipped_sign_sqrt | flipped_sign_sqrt_i, &r_prime, &r);
        (correct_sign_sqrt | flipped_sign_sqrt, r.abs())
    }
}

/// `p = 2^255 - 19`, little-endian.
const P: [u64; 4] = [
    0xffffffffffffffed,
    0xffffffffffffffff,
    0xffffffffffffffff,
    0x7fffffffffffffff,
];

/// A point on edwards25519 in extended coordinates `(X, Y, Z, T)`, where
/// `x = X / Z`, `y = Y / Z`, and `x * y = T / Z`, each reduced.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Point(pub(crate) [u64; 16]);

impl Point {
    pub(crate) const IDENTITY: Self = Self([0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]);

    /// The point `(X / Z, Y / Z)` with `T = X * Y / Z`, from its coordinates.
    pub(crate) fn from_coordinates(x: &Fe, y: &Fe, z: &Fe, t: &Fe) -> Self {
        let mut p = [0u64; 16];
        p[0..4].copy_from_slice(&x.0);
        p[4..8].copy_from_slice(&y.0);
        p[8..12].copy_from_slice(&z.0);
        p[12..16].copy_from_slice(&t.0);
        Self(p)
    }

    /// `(X, Y, Z, T)`.
    pub(crate) fn coordinates(&self) -> [Fe; 4] {
        let c = |i: usize| Fe(self.0[4 * i..4 * i + 4].try_into().unwrap());
        [c(0), c(1), c(2), c(3)]
    }

    /// RFC 8032 5.1.3's decoding, or `None` for an encoding it rejects: `y`
    /// not below `p`, no point with that `y`, or `x = 0` with the sign bit
    /// set.
    ///
    /// Only public encodings are decoded: whether one decodes is public.
    pub(crate) fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let mut xy = [0u64; 8];
        if !low::edwards25519_decode(&mut xy, bytes) {
            return None;
        }
        let x = Fe(xy[0..4].try_into().unwrap());
        let y = Fe(xy[4..8].try_into().unwrap());
        Some(Self::from_coordinates(&x, &y, &Fe::ONE, &x.mul(&y)))
    }

    /// RFC 8032 5.1.2's encoding, in constant time.
    pub(crate) fn to_bytes(self) -> [u8; 32] {
        let [x, y, z, _] = self.coordinates();
        let z_inv = z.invert();
        // The multiplication reduces fully, whatever the point routines left.
        let mut bytes = y.mul(&z_inv).to_le_bytes();
        bytes[31] |= (x.mul(&z_inv).is_negative() as u8) << 7;
        bytes
    }

    /// `-self`: `-(x, y) = (-x, y)`, so `X` and `T` change sign.
    pub(crate) fn neg(&self) -> Self {
        let [x, y, z, t] = self.coordinates();
        Self::from_coordinates(&x.neg(), &y, &z, &t.neg())
    }

    /// `8 * self`, which leaves only its component in the prime-order
    /// subgroup.
    pub(crate) fn mul_by_cofactor(&self) -> Self {
        let mut a = [0u64; 12];
        let mut b = [0u64; 12];
        low::edwards25519_pdouble(&mut a, self.projective());
        low::edwards25519_pdouble(&mut b, &a);
        let mut r = Self::IDENTITY;
        low::edwards25519_epdouble(&mut r.0, &b);
        r
    }

    /// `[scalar]B`, for the curve's base point `B`.
    pub(crate) fn mul_base(scalar: &Scalar) -> Self {
        let mut affine = [0u64; 8];
        low::edwards25519_scalarmulbase(&mut affine, &scalar.0);
        let x = Fe(affine[0..4].try_into().unwrap());
        let y = Fe(affine[4..8].try_into().unwrap());
        Self::from_coordinates(&x, &y, &Fe::ONE, &x.mul(&y))
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        let mut r = Self::IDENTITY;
        low::edwards25519_epadd(&mut r.0, &self.0, &other.0);
        r
    }

    /// `2 * self`, ignoring `T`.
    fn double(&self) -> Self {
        let mut r = Self::IDENTITY;
        low::edwards25519_epdouble(&mut r.0, self.projective());
        r
    }

    /// `16 * self`. The first three doublings are projective, skipping `T`,
    /// which only the addition after the last one reads.
    fn mul_by_16(&self) -> Self {
        let mut a = [0u64; 12];
        let mut b = [0u64; 12];
        low::edwards25519_pdouble(&mut a, self.projective());
        low::edwards25519_pdouble(&mut b, &a);
        low::edwards25519_pdouble(&mut a, &b);
        let mut r = Self::IDENTITY;
        low::edwards25519_epdouble(&mut r.0, &a);
        r
    }

    /// `(X, Y, Z)`.
    fn projective(&self) -> &[u64; 12] {
        self.0[..12].try_into().unwrap()
    }

    /// `[scalar]self`, in constant time.
    ///
    /// A fixed window of four bits over signed digits: a table of
    /// `0 * self ..= 8 * self`, then for each digit from the top, sixteen
    /// times the sum so far plus the digit's entry, read in constant time and
    /// negated for a negative digit. It does the work of s2n-bignum's
    /// `edwards25519_scalarmuldouble` without the base point's half, and
    /// stays in extended coordinates, so ristretto255 never inverts `Z`.
    pub(crate) fn mul(&self, scalar: &Scalar) -> Self {
        let mut table = [Self::IDENTITY.0; 9];
        table[1] = self.0;
        for i in 2..table.len() {
            table[i] = match i % 2 {
                0 => Self(table[i / 2]).double().0,
                _ => Self(table[i - 1]).add(self).0,
            };
        }
        let digits = scalar.signed_radix_16();
        let mut acc = Self::select(&table, digits[63]);
        for digit in digits[..63].iter().rev() {
            acc = acc.mul_by_16().add(&Self::select(&table, *digit));
        }
        acc
    }

    /// `[digit]P` from the table of `0 * P ..= 8 * P`, for `-8 <= digit <= 8`,
    /// in constant time.
    ///
    /// Masks read every row, as s2n-bignum's `bignum_copy_row_from_table`
    /// does, which measured twenty times slower here as it walks a table of
    /// any shape.
    fn select(table: &[[u64; 16]; 9], digit: i8) -> Self {
        let sign = digit >> 7; // 0 or -1, by an arithmetic shift
        let negative = (sign & 1) as u64;
        // Wrapping, so a debug build's overflow check adds no branch on the
        // digit; `digit ^ sign` is at most 7 for a negative digit.
        let magnitude = (digit ^ sign).wrapping_sub(sign) as u64;
        let mut p = [0u64; 16];
        for (i, row) in table.iter().enumerate() {
            // 1 where `i == magnitude`, hidden from the optimiser so it stays
            // arithmetic rather than a branch.
            let hit = core::hint::black_box((i as u64 ^ magnitude).wrapping_sub(1) >> 63);
            let mask = hit.wrapping_neg();
            for (out, word) in p.iter_mut().zip(row) {
                *out |= word & mask;
            }
        }

        // -(x, y) = (-x, y), so `X` and `T` change sign.
        let [x, y, z, t] = Self(p).coordinates();
        Self::from_coordinates(&x.negate_if(negative), &y, &z, &t.negate_if(negative))
    }
}

/// An integer modulo the prime order of edwards25519's base point,
/// `L = 2^252 + 27742317777372353535851937790883648493`, as little-endian
/// words, reduced.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scalar(pub(crate) [u64; 4]);

impl Scalar {
    /// `L`, little-endian.
    const ORDER: [u64; 4] = [
        0x5812631a5cf5d3ed,
        0x14def9dea2f79cd6,
        0x0000000000000000,
        0x1000000000000000,
    ];

    /// Reads a little-endian scalar, or `None` unless it is below `L`.
    ///
    /// Whether it is below `L` is public; the value stays secret.
    pub(crate) fn from_canonical_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let s = util::little_endian_to_u64x4(bytes);
        let canonical = low::bignum_cmp_lt(&s, &Self::ORDER) != 0;
        low::ct::into_public(canonical).then_some(Self(s))
    }

    /// Reduces 64 little-endian bytes modulo `L`.
    pub(crate) fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        let mut s = Self([0; 4]);
        low::bignum_mod_n25519(&mut s.0, &util::little_endian_to_u64x8(bytes));
        s
    }

    pub(crate) fn to_bytes(self) -> [u8; 32] {
        util::u64x4_to_little_endian(&self.0)
    }

    /// `self * other mod L`.
    // Only tests multiply scalars alone until FROST does.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn mul(&self, other: &Self) -> Self {
        self.mul_add(other, &Self([0; 4]))
    }

    /// `self * other + addend mod L`.
    pub(crate) fn mul_add(&self, other: &Self, addend: &Self) -> Self {
        let mut z = Self([0; 4]);
        low::bignum_madd_n25519(&mut z.0, &self.0, &other.0, &addend.0);
        z
    }

    /// `1 / self mod L`, or `None` for zero, which has no inverse.
    ///
    /// Whether `self` is zero is public; the value stays secret.
    pub(crate) fn invert(&self) -> Option<Self> {
        if low::ct::into_public(low::bignum_eq(&self.0, &[0; 4])) {
            return None;
        }
        let mut z = Self([0; 4]);
        let mut temp = [0u64; 4 * 3];
        low::bignum_modinv(&mut z.0, &self.0, &Self::ORDER, &mut temp);
        Some(z)
    }

    /// `-self mod L`.
    pub(crate) fn neg(&self) -> Self {
        let mut z = Self([0; 4]);
        low::bignum_modsub(&mut z.0, &[0; 4], &self.0, &Self::ORDER);
        z
    }

    /// Whether this is zero, computed in constant time.
    pub(crate) fn is_zero(&self) -> bool {
        low::bignum_eq(&self.0, &[0; 4])
    }

    /// A uniformly random nonzero scalar: 64 bytes from the system's random
    /// source, reduced modulo `L`.
    pub(crate) fn random() -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        // Zero has a chance of 2^-252 a draw, so only a broken source fails.
        for _ in 0..64 {
            let mut bytes = [0u8; 64];
            SystemRandom.fill(&mut bytes)?;
            low::ct::secret_slice(&bytes);
            let scalar = Self::from_uniform_bytes(&bytes);
            if !low::ct::into_public(scalar.is_zero()) {
                return Ok(scalar);
            }
        }
        Err(Error::RngFailed)
    }

    /// The scalar as 64 signed digits in `-8..=8`, least significant first,
    /// whose sum of `digit[i] * 16^i` is the scalar.
    ///
    /// Each digit takes the low nibble's carry into the next, so the top
    /// digit, under `L < 2^253`, ends at most 2.
    fn signed_radix_16(&self) -> [i8; 64] {
        let bytes = self.to_bytes();
        let mut digits = [0i8; 64];
        for (i, byte) in bytes.iter().enumerate() {
            digits[2 * i] = (byte & 15) as i8;
            digits[2 * i + 1] = (byte >> 4) as i8;
        }
        for i in 0..63 {
            // Arithmetic shifts, so the carry is branch-free, and wrapping,
            // so a debug build's overflow checks add no branch on the digits;
            // every digit stays within `-8..=16`.
            let carry = digits[i].wrapping_add(8) >> 4;
            digits[i] = digits[i].wrapping_sub(carry << 4);
            digits[i + 1] = digits[i + 1].wrapping_add(carry);
        }
        digits
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn fe(hex: &str) -> Fe {
        let (x, canonical) = Fe::from_le_bytes(&hex::decode(hex).unwrap().try_into().unwrap());
        assert_eq!(canonical, 1);
        x
    }

    /// RFC 9496 A.4.
    #[test]
    fn sqrt_ratio_m1_vectors() {
        const ZERO: &str = "0000000000000000000000000000000000000000000000000000000000000000";
        const ONE: &str = "0100000000000000000000000000000000000000000000000000000000000000";
        const TWO: &str = "0200000000000000000000000000000000000000000000000000000000000000";
        const FOUR: &str = "0400000000000000000000000000000000000000000000000000000000000000";
        for (u, v, was_square, r) in [
            (ZERO, ZERO, 1, ZERO),
            (ZERO, ONE, 1, ZERO),
            (ONE, ZERO, 0, ZERO),
            (
                TWO,
                ONE,
                0,
                "3c5ff1b5d8e4113b871bd052f9e7bcd0582804c266ffb2d4f4203eb07fdb7c54",
            ),
            (FOUR, ONE, 1, TWO),
            (
                ONE,
                FOUR,
                1,
                "f6ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f",
            ),
        ] {
            let (got_square, got_r) = Fe::sqrt_ratio_m1(&fe(u), &fe(v));
            assert_eq!((got_square, got_r.0), (was_square, fe(r).0), "{u} / {v}");
        }
    }

    #[test]
    fn constants() {
        // SQRT_M1^2 = -1
        assert_eq!(Fe::SQRT_M1.square().0, Fe::ONE.neg().0);
        // d * 121666 = -121665
        let n = |x| Fe([x, 0, 0, 0]);
        assert_eq!(Fe::D.mul(&n(121666)).0, n(121665).neg().0);
    }

    #[test]
    fn signed_radix_16_sums_to_the_scalar() {
        let max = Scalar([Scalar::ORDER[0] - 1, Scalar::ORDER[1], 0, Scalar::ORDER[3]]);
        for s in [Scalar([0; 4]), Scalar([0x0888_8888_8888_8888; 4]), max] {
            let digits = s.signed_radix_16();
            assert!(digits[..63].iter().all(|d| (-8..8).contains(d)));
            assert!((0..=2).contains(&digits[63]));
            // Carrying back to digits in `0..16` gives the scalar's nibbles.
            let mut nibbles = digits.map(i32::from);
            for i in 0..63 {
                let carry = nibbles[i].div_euclid(16);
                nibbles[i] -= carry * 16;
                nibbles[i + 1] += carry;
            }
            let want = s.to_bytes().map(i32::from);
            let want: Vec<i32> = want.iter().flat_map(|b| [b & 15, b >> 4]).collect();
            assert_eq!(nibbles.to_vec(), want);
        }
    }
}
