// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-384 group operations for RFC 9497, over the curve arithmetic P-384
//! already runs.
//!
//! Point addition is the complete projective formula for `a = -3` curves
//! (Renes, Costello, and Batina, "Complete addition formulas for prime order
//! elliptic curves", 2015, Appendix A.2 Algorithm 4; EFD `add-2015-rcb-3`).
//! The assembly additions are proven only for unequal, finite points, and a
//! peer's batch can force the other cases while the server's key is in use.
//! Coordinates are projective `(X : Y : Z)` for the affine point `(X/Z, Y/Z)`,
//! in Montgomery form, the same representation the field arithmetic uses.

use super::{
    AffineMontPoint, CURVE_B_MONT, CURVE_ONE_MONT, CURVE_ORDER, FieldElement, JacobianMontPoint,
    Scalar,
};
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::RandomSource;

pub(crate) const ELEMENT: usize = 49;
pub(crate) const SCALAR: usize = 48;

pub(crate) fn hash_to_group(msg: &[u8], dst: &[u8]) -> Result<[u8; ELEMENT], Error> {
    let point = super::hash_to_curve::hash_to_curve(msg, dst)?;
    Ok(compress(&point.point))
}

pub(crate) fn hash_to_scalar(msg: &[u8], dst: &[u8]) -> Result<[u8; SCALAR], Error> {
    Ok(super::hash_to_curve::hash_to_scalar(msg, dst)?.as_bytes())
}

pub(crate) fn random_scalar(rng: &mut dyn RandomSource) -> Result<[u8; SCALAR], Error> {
    // A candidate is rejected when it is zero or at least n. The cap makes
    // exhaustion negligible even where n is several bits under a byte boundary.
    for _ in 0..8192 {
        let mut bytes = [0u8; SCALAR];
        rng.fill(&mut bytes)?;
        low::ct::secret_slice(&bytes);
        if let Ok(scalar) = scalar_nonzero(&bytes) {
            return Ok(scalar);
        }
    }
    Err(Error::RngFailed)
}

/// A scalar in `[1, n)`.
pub(crate) fn scalar_nonzero(bytes: &[u8]) -> Result<[u8; SCALAR], Error> {
    if bytes.len() != SCALAR {
        return Err(Error::WrongLength);
    }
    Ok(Scalar::from_bytes_checked(bytes)?.as_bytes())
}

/// A scalar in `[0, n)`, the range RFC 9497 deserializes a proof scalar into.
pub(crate) fn scalar_any(bytes: &[u8]) -> Result<[u8; SCALAR], Error> {
    Ok(scalar_words(bytes)?.as_bytes())
}

pub(crate) fn scalar_is_zero(bytes: &[u8]) -> bool {
    // Whether a derived key candidate is zero is the loop condition RFC 9497
    // publishes by retrying. The value stays secret. A byte string that is
    // not a scalar is not zero.
    match scalar_words(bytes) {
        Ok(scalar) => low::ct::into_public(scalar.is_zero()),
        Err(_) => false,
    }
}

pub(crate) fn generator() -> [u8; ELEMENT] {
    let mut one = [0u8; SCALAR];
    one[SCALAR - 1] = 1;
    base_mul(&one).expect("1 is a scalar")
}

pub(crate) fn base_mul(scalar: &[u8]) -> Result<[u8; ELEMENT], Error> {
    let scalar = scalar_words(scalar)?;
    if low::ct::into_public(scalar.is_zero()) {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    Ok(compress(&checked(mul_base_point(&scalar))?))
}

pub(crate) fn mul(element: &[u8], scalar: &[u8]) -> Result<[u8; ELEMENT], Error> {
    let scalar = scalar_words(scalar)?;
    if low::ct::into_public(scalar.is_zero()) {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    let point = decompress(element)?;
    Ok(compress(&checked(mul_point(&point, &scalar))?))
}

pub(crate) fn invert(scalar: &[u8]) -> Result<[u8; SCALAR], Error> {
    let scalar = scalar_words(scalar)?;
    if low::ct::into_public(scalar.is_zero()) {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    Ok(scalar.inv().as_bytes())
}

pub(crate) fn mul_scalars(a: &[u8], b: &[u8]) -> Result<[u8; SCALAR], Error> {
    let (a, b) = (scalar_words(a)?, scalar_words(b)?);
    // `a` in Montgomery form times plain `b` is the product, plain.
    Ok(a.as_mont().mont_mul(&b).as_bytes())
}

pub(crate) fn sub_scalars(a: &[u8], b: &[u8]) -> Result<[u8; SCALAR], Error> {
    let (a, b) = (scalar_words(a)?, scalar_words(b)?);
    let mut r = Scalar::default();
    low::bignum_modsub(&mut r.0, &a.0, &b.0, &CURVE_ORDER);
    Ok(r.as_bytes())
}

/// `sum scalars[i] * points[i]`, starting from the identity.
///
/// A zero scalar contributes the identity. The encoded sum is never the
/// identity: RFC 9497 has no fixed-length encoding of it.
pub(crate) fn sum_scaled(points: &[&[u8]], scalars: &[&[u8]]) -> Result<[u8; ELEMENT], Error> {
    if points.len() != scalars.len() {
        return Err(Error::WrongLength);
    }
    let mut acc = Proj::identity();
    for (point, scalar) in points.iter().zip(scalars) {
        let point = decompress(point)?;
        let scalar = scalar_words(scalar)?;
        acc = proj_add(acc, scaled(&point, &scalar)?);
    }
    encode(acc)
}

fn mul_base_point(scalar: &Scalar) -> AffineMontPoint {
    JacobianMontPoint::base_multiply(scalar).as_affine()
}

fn mul_point(point: &AffineMontPoint, scalar: &Scalar) -> AffineMontPoint {
    JacobianMontPoint::multiply(scalar, point).as_affine()
}

fn scalar_words(bytes: &[u8]) -> Result<Scalar, Error> {
    if bytes.len() != SCALAR {
        return Err(Error::WrongLength);
    }
    let full = Scalar(super::util::big_endian_slice_to_u64x6(bytes).ok_or(Error::WrongLength)?);
    let reduced = full.reduce_mod_n();
    match low::ct::into_public(reduced.private_eq(&full)) {
        true => Ok(full),
        false => Err(KeyFormatError::ScalarOutOfRange.into()),
    }
}

fn checked(point: AffineMontPoint) -> Result<AffineMontPoint, Error> {
    match low::ct::into_public(point.on_curve()) {
        true => Ok(point),
        false => Err(Error::Fault),
    }
}

fn compress(point: &AffineMontPoint) -> [u8; ELEMENT] {
    let raw = point.as_bytes_uncompressed();
    let mut out = [0u8; ELEMENT];
    // SEC1: 0x02 when y is even, 0x03 when y is odd. The low bit is copied,
    // not branched on, so a secret point's encoding stays constant time.
    out[0] = 0x02 | (raw[raw.len() - 1] & 1);
    out[1..].copy_from_slice(&raw[1..ELEMENT]);
    out
}

fn decompress(bytes: &[u8]) -> Result<AffineMontPoint, Error> {
    if bytes.len() != ELEMENT {
        return Err(Error::WrongLength);
    }
    AffineMontPoint::from_x962_compressed(bytes)
}

/// `scalar * point` as a projective point. A zero scalar is the identity,
/// and the multiplication runs on one so its affine conversion is defined.
fn scaled(point: &AffineMontPoint, scalar: &Scalar) -> Result<Proj, Error> {
    let zero = u64::from(low::bignum_eq(&scalar.0, &[0; 6]));
    let mut one = [0u8; SCALAR];
    one[SCALAR - 1] = 1;
    let one = scalar_words(&one)?;
    let mut used = Scalar::default();
    low::bignum_mux(zero, &mut used.0, &one.0, &scalar.0);
    let product = checked(mul_point(point, &used))?;
    Ok(Proj::select(
        &Proj::from_affine(&product),
        &Proj::identity(),
        zero,
    ))
}

#[derive(Clone, Copy)]
struct Proj {
    x: FieldElement,
    y: FieldElement,
    z: FieldElement,
}

impl Proj {
    fn identity() -> Self {
        Self {
            x: FieldElement::default(),
            y: CURVE_ONE_MONT,
            z: FieldElement::default(),
        }
    }

    fn from_affine(point: &AffineMontPoint) -> Self {
        Self {
            x: point.x(),
            y: point.y(),
            z: CURVE_ONE_MONT,
        }
    }

    /// `if_set` when `select` is nonzero, otherwise `if_unset`.
    fn select(if_unset: &Self, if_set: &Self, select: u64) -> Self {
        let mut x = [0; 6];
        let mut y = [0; 6];
        let mut z = [0; 6];
        low::bignum_mux(select, &mut x, &if_set.x.0, &if_unset.x.0);
        low::bignum_mux(select, &mut y, &if_set.y.0, &if_unset.y.0);
        low::bignum_mux(select, &mut z, &if_set.z.0, &if_unset.z.0);
        Self {
            x: FieldElement(x),
            y: FieldElement(y),
            z: FieldElement(z),
        }
    }
}

fn encode(point: Proj) -> Result<[u8; ELEMENT], Error> {
    let zero = u64::from(low::bignum_eq(&point.z.0, &[0; 6]));
    if low::ct::into_public(zero) == 1 {
        return Err(KeyFormatError::SmallOrder.into());
    }
    let zinv = point.z.demont().inv().as_mont();
    let affine = AffineMontPoint::from_xy(point.x.mont_mul(&zinv), point.y.mont_mul(&zinv));
    Ok(compress(&checked(affine)?))
}

fn sub(a: &FieldElement, b: &FieldElement) -> FieldElement {
    a.add(&b.negate_mod_p())
}

/// Complete addition. See the module comment for the formula.
fn proj_add(p: Proj, q: Proj) -> Proj {
    let (x1, y1, z1) = (p.x, p.y, p.z);
    let (x2, y2, z2) = (q.x, q.y, q.z);
    let b = CURVE_B_MONT;
    let t0 = x1.mont_mul(&x2);
    let t1 = y1.mont_mul(&y2);
    let t2 = z1.mont_mul(&z2);
    let t3 = x1.add(&y1);
    let t4 = x2.add(&y2);
    let t3 = t3.mont_mul(&t4);
    let t4 = t0.add(&t1);
    let t3 = sub(&t3, &t4);
    let t4 = y1.add(&z1);
    let x3 = y2.add(&z2);
    let t4 = t4.mont_mul(&x3);
    let x3 = t1.add(&t2);
    let t4 = sub(&t4, &x3);
    let x3 = x1.add(&z1);
    let y3 = x2.add(&z2);
    let x3 = x3.mont_mul(&y3);
    let y3 = t0.add(&t2);
    let y3 = sub(&x3, &y3);
    let z3 = b.mont_mul(&t2);
    let x3 = sub(&y3, &z3);
    let z3 = x3.add(&x3);
    let x3 = x3.add(&z3);
    let z3 = sub(&t1, &x3);
    let x3 = t1.add(&x3);
    let y3 = b.mont_mul(&y3);
    let t1 = t2.add(&t2);
    let t2 = t1.add(&t2);
    let y3 = sub(&y3, &t2);
    let y3 = sub(&y3, &t0);
    let t1 = y3.add(&y3);
    let y3 = t1.add(&y3);
    let t1 = t0.add(&t0);
    let t0 = t1.add(&t0);
    let t0 = sub(&t0, &t2);
    let t1 = t4.mont_mul(&y3);
    let t2 = t0.mont_mul(&y3);
    let y3 = x3.mont_mul(&z3);
    let y3 = y3.add(&t2);
    let x3 = t3.mont_mul(&x3);
    let x3 = sub(&x3, &t1);
    let z3 = t4.mont_mul(&z3);
    let t1 = t3.mont_mul(&t0);
    let z3 = z3.add(&t1);
    Proj {
        x: x3,
        y: y3,
        z: z3,
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn be(last: u8) -> [u8; SCALAR] {
        let mut bytes = [0u8; SCALAR];
        bytes[SCALAR - 1] = last;
        bytes
    }

    #[test]
    fn addition_matches_the_generator_multiples() {
        let _entry = low::Entry::new_secret();
        let one = be(1);
        let two = be(2);
        let g = generator();
        let double = base_mul(&two).unwrap();
        assert_eq!(sum_scaled(&[&g, &g], &[&one, &one]).unwrap(), double);
        assert_eq!(sum_scaled(&[&g, &g], &[&[0; SCALAR], &one]).unwrap(), g);

        let mut negated = decompress(&g).unwrap();
        negated.negate_y();
        let negated = compress(&negated);
        assert!(matches!(
            sum_scaled(&[&g, &negated], &[&one, &one]),
            Err(Error::KeyRejected(_))
        ));
    }
}
