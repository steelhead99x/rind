// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::ops::Range;

use super::util;
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::{RandomSource, SystemRandom};

pub(crate) mod hash_to_curve;
pub(crate) mod oprf;
mod precomp;

/// A P-521 public key.
#[derive(Clone, Debug)]
pub(crate) struct PublicKey {
    point: AffinePoint,
}

impl PublicKey {
    pub(crate) const BYTES: usize = 1 + FieldElement::BYTES + FieldElement::BYTES;

    /// Create a P-521 [`PublicKey`] from a byte slice.
    ///
    /// This must be exactly 133 bytes in length, using the X9.62
    /// uncompressed encoding.  An error is returned if a coordinate
    /// is not below the field prime, or the point is not on the curve.
    pub(crate) fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        let point = AffinePoint::from_x962_uncompressed(bytes)?;
        Ok(Self { point })
    }

    /// Decompress an X9.62 compressed point to its uncompressed encoding,
    /// written to the start of `output`, which
    /// [`Self::from_x962_uncompressed`] takes.
    ///
    /// An error is returned unless `bytes` is 67 bytes with tag 2 or 3, its
    /// `x` is below the field prime, and a point on the curve has that `x`.
    pub(crate) fn decompress<'a>(bytes: &[u8], output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = low::Entry::new_public();
        let point = AffinePoint::from_x962_compressed(bytes)?;
        let output = output.get_mut(..Self::BYTES).ok_or(Error::WrongLength)?;
        output.copy_from_slice(&point.as_bytes_uncompressed());
        Ok(output)
    }
}

/// A P-521 public key for ECDSA verification.
///
/// It builds the point's multiples on its first verification and keeps
/// them, so verifying again skips computing them, and a key never verified
/// with, such as an ECDSA key pair's, never pays for them.
#[derive(Clone, Debug)]
pub(crate) struct VerifyingKey {
    point: AffinePoint,
    /// P, 3P, ..., 15P.
    odd_multiples: low::ReuseCache<[AffinePoint; 8]>,
    /// 17P, 19P, ..., 31P, which widen P's digits but pay for building
    /// only once a key is reused.
    more_odd_multiples: low::ReuseCache<[AffinePoint; 8]>,
}

impl VerifyingKey {
    /// Create a [`VerifyingKey`] as [`PublicKey::from_x962_uncompressed`] does.
    pub(crate) fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        low::Entry::assert_held();
        let PublicKey { point } = PublicKey::from_x962_uncompressed(bytes)?;
        Ok(Self {
            point,
            odd_multiples: low::ReuseCache::new(),
            more_odd_multiples: low::ReuseCache::new(),
        })
    }

    pub(crate) fn raw_ecdsa_verify(&self, r: &Scalar, s: &Scalar, e: &Scalar) -> Result<(), Error> {
        // 4. Compute: u1 = e s^-1 mod n and u2 = r s^−1 mod n
        let s_inv = s.inv().as_mont();
        let u1 = s_inv.mont_mul(&e.as_mont()).demont();
        let u2 = s_inv.mont_mul(&r.as_mont()).demont();

        // 5. Compute: R = (xR, yR) = u1 G + u2 QU
        //  If R = O, output "invalid" and stop.
        let odd_multiples = self
            .odd_multiples
            .get_or_build_now(|| self.point.public_odd_multiples());
        let more = self
            .more_odd_multiples
            .get_or_build(|| AffinePoint::public_more_odd_multiples(&odd_multiples));
        let point = match more {
            Some(more) => JacobianPoint::public_twin_multiply(&u1, &u2, &[&odd_multiples, more]),
            None => JacobianPoint::public_twin_multiply(&u1, &u2, &[&odd_multiples]),
        };

        if point.public_is_infinity() {
            return Err(Error::BadSignature);
        }

        // 6. Convert the field element xR to an integer xR using the conversion routine specified in Section 2.3.9.
        // 7. Set v = xR mod n.
        let v = point.x_scalar();

        // 8. Compare v and r — if v = r, output "valid", and if v != r, output "invalid".
        match v.public_eq(r) {
            true => Ok(()),
            false => Err(Error::BadSignature),
        }
    }
}

/// A P-521 private key.
///
/// `agreement::PrivateKey` holds one for Diffie-Hellman. It is not wiped on
/// drop: the public keys holding one wipe it, and an ECDSA nonce is one too,
/// which lives only for the signing call.
pub(crate) struct PrivateKey {
    scalar: Scalar,
}

impl PrivateKey {
    /// Generate a new random private key using the system RNG.
    pub(crate) fn new_random() -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        Self::generate(&mut SystemRandom)
    }

    /// Derive the corresponding public key, and return it in
    /// X9.62 uncompressed encoding.
    pub(crate) fn public_key_uncompressed(&self) -> [u8; PublicKey::BYTES] {
        let _entry = low::Entry::new_secret();
        self.public_point().as_bytes_uncompressed()
    }

    /// Do the Diffie-Hellman operation.
    ///
    /// `peer` is the peer's public key (and this type means it was
    /// already checked to be on the curve.)
    ///
    /// Returns a [`SharedSecret`].  May return an error in fault conditions.
    pub(crate) fn diffie_hellman(&self, peer: &PublicKey) -> Result<SharedSecret, Error> {
        let _entry = low::Entry::new_secret();
        let result = JacobianPoint::multiply(&self.scalar, &peer.point).as_affine();
        match low::ct::into_public(result.on_curve()) {
            true => Ok(SharedSecret(result.x().as_bytes())),
            false => Err(Error::Fault),
        }
    }

    fn public_point(&self) -> AffinePoint {
        let point = JacobianPoint::base_multiply(&self.scalar).as_affine();
        let point = low::ct::into_public(point);
        match point.on_curve() {
            true => point,
            false => panic!("internal fault"),
        }
    }

    /// Draws a scalar as RFC6979's `bits2int` does: the leftmost 521 bits
    /// of 66 random bytes, retried until it is in range.
    ///
    /// Through `HmacDrbg`, this is RFC6979's nonce generation; from the
    /// system RNG, it is a uniform key.
    fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        for _ in 0..64 {
            let mut r = [0u8; Scalar::BYTES];
            rng.fill(&mut r)?;
            low::ct::secret_slice(&r);
            let words = util::big_endian_slice_any_size_to_u64x9(&r).unwrap();
            let words = core::array::from_fn(|i| {
                let above = words
                    .get(i + 1)
                    .map_or(0, |w| w << (64 - Scalar::EXCESS_BITS));
                (words[i] >> Scalar::EXCESS_BITS) | above
            });
            if let Ok(scalar) = Scalar(words).into_range_check() {
                return Ok(Self {
                    scalar: low::ct::into_secret(scalar),
                });
            }
        }

        Err(Error::RngFailed)
    }

    /// Decode a private key as [`StaticPrivateKey::from_bytes`] does.
    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        Scalar::from_bytes_checked(bytes).map(|scalar| Self {
            scalar: low::ct::into_secret(scalar),
        })
    }

    /// Return a fixed-length encoding of this private key's value, still secret.
    pub(crate) fn secret_bytes(&self) -> [u8; Scalar::BYTES] {
        self.scalar.as_bytes()
    }
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey").finish_non_exhaustive()
    }
}

/// A P-521 static private key.
///
/// This backs ECDSA, so it can be serialized and deserialized.
pub(crate) struct StaticPrivateKey(PrivateKey);

impl StaticPrivateKey {
    /// Generate a new random private key using the system RNG.
    #[cfg(test)]
    pub(crate) fn new_random() -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        Self::generate(&mut SystemRandom)
    }

    /// Decode a private key from `bytes`.
    ///
    /// `bytes` may be larger or smaller than the size of `n`: excess bytes
    /// must be zero.  If given a variable-sized input, this is deemed a
    /// non-secret property.  Prefer to use fixed-sized inputs.
    ///
    /// An error is returned if the magnitude of the value is larger than
    /// `n` (ie, the input is never reduced mod n),  or the value is zero.
    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        PrivateKey::from_bytes(bytes).map(Self)
    }

    /// Return a fixed-length encoding of this private key's value, still secret.
    pub(crate) fn secret_bytes(&self) -> [u8; Scalar::BYTES] {
        self.0.secret_bytes()
    }

    /// Derive the corresponding public key, and return it in
    /// X9.62 uncompressed encoding.
    pub(crate) fn public_key_uncompressed(&self) -> [u8; PublicKey::BYTES] {
        let _entry = low::Entry::new_secret();
        self.0.public_point().as_bytes_uncompressed()
    }

    pub(crate) fn public_key_x_scalar(&self) -> Scalar {
        let _entry = low::Entry::new_secret();
        self.0.public_point().x_scalar()
    }

    pub(crate) fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        PrivateKey::generate(rng).map(Self)
    }

    pub(crate) fn raw_ecdsa_sign(&self, k: &Self, e: &Scalar, r: &Scalar) -> Scalar {
        // this is (e + r * d) / k
        let lhs_mont = self
            .0
            .scalar
            .as_mont()
            .mont_mul(&r.as_mont())
            .demont()
            .add(e)
            .as_mont();
        low::ct::into_public(k.0.scalar.inv().mont_mul(&lhs_mont))
    }
}

/// A shared secret output from a P-521 Diffie-Hellman operation.
///
/// It is not wiped on drop: `agreement::SharedSecret` wipes it.
pub(crate) struct SharedSecret(pub(crate) [u8; FieldElement::BYTES]);

#[derive(Clone, Copy, Debug, Default)]
struct AffinePoint {
    xy: [u64; 18],
}

impl AffinePoint {
    const X: Range<usize> = 0..9;
    const Y: Range<usize> = 9..18;

    fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.first() {
            Some(0x04) => (),
            Some(_) => return Err(KeyFormatError::Compressed.into()),
            None => return Err(KeyFormatError::WrongLength.into()),
        }

        if bytes.len() != PublicKey::BYTES {
            return Err(KeyFormatError::WrongLength.into());
        }

        let (_, xy) = bytes.split_at(1);
        let (x, y) = xy.split_at(FieldElement::BYTES);

        let x = util::big_endian_slice_any_size_to_u64x9(x).unwrap();
        let y = util::big_endian_slice_any_size_to_u64x9(y).unwrap();

        // A coordinate at or above p would be reduced, giving the point a
        // second encoding.  Public, so this need not be constant time.
        let below_p = |v: &[u64; 9]| v.iter().rev().lt(CURVE_PRIME.iter().rev());
        if !below_p(&x) || !below_p(&y) {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        let point = Self::from_xy(FieldElement(x), FieldElement(y));

        if !point.on_curve() {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        Ok(point)
    }

    /// Decodes an X9.62 compressed point: `x`, and the parity of `y`.
    ///
    /// p is `2^521 - 1`, 3 mod 4, so a square's root is its
    /// `(p + 1) / 4 = 2^519`th power (Euler's criterion). The root is squared
    /// back, so an `x` with no point is refused rather than given one. No
    /// point of a curve of prime order has `y = 0`, so `y` and `p - y` differ
    /// in parity.
    fn from_x962_compressed(bytes: &[u8]) -> Result<Self, Error> {
        let (tag, x) = match bytes.split_first() {
            Some((&tag @ (0x02 | 0x03), x)) => (tag, x),
            Some(_) => return Err(KeyFormatError::PointEncoding.into()),
            None => return Err(KeyFormatError::WrongLength.into()),
        };
        if x.len() != FieldElement::BYTES {
            return Err(KeyFormatError::WrongLength.into());
        }
        let x = util::big_endian_slice_any_size_to_u64x9(x).unwrap();
        if !x.iter().rev().lt(CURVE_PRIME.iter().rev()) {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        let x = FieldElement(x);
        let rhs = x.sqr().add(&CURVE_A).mul(&x).add(&CURVE_B);
        let mut y = rhs;
        for _ in 0..519 {
            y = y.sqr();
        }
        if !y.sqr().public_eq(&rhs) {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        let y = match y.0[0] & 1 == u64::from(tag & 1) {
            true => y,
            false => y.negate(),
        };
        Ok(Self::from_xy(x, y))
    }

    fn x_scalar(&self) -> Scalar {
        Scalar(self.x().0).reduce_mod_n()
    }

    fn from_xy(x: FieldElement, y: FieldElement) -> Self {
        let mut r = Self::default();
        r.xy[Self::X].copy_from_slice(&x.0[..]);
        r.xy[Self::Y].copy_from_slice(&y.0[..]);
        r
    }

    fn x(&self) -> FieldElement {
        FieldElement(self.xy[Self::X].try_into().unwrap())
    }

    fn y(&self) -> FieldElement {
        FieldElement(self.xy[Self::Y].try_into().unwrap())
    }

    fn on_curve(&self) -> bool {
        // Compute the curve equation:
        //
        // y ^ 2 === x ^ 3 + ax + b
        //
        // all in GF(p)
        //

        let x = self.x();
        let rhs = x.sqr(); // x ^ 2
        let rhs = rhs.add(&CURVE_A); // x ^ 2 + a
        let rhs = rhs.mul(&x); // (x ^ 2 + a) * x   equiv  x ^ 3 + ax
        let rhs = rhs.add(&CURVE_B);

        let lhs = self.y().sqr();

        // Constant time, since `diffie_hellman` checks a secret point.
        low::bignum_eq(&lhs.0, &rhs.0)
    }

    fn as_bytes_uncompressed(&self) -> [u8; PublicKey::BYTES] {
        let mut r = [0u8; PublicKey::BYTES];

        let (indicator, xy) = r.split_at_mut(1);
        let (x, y) = xy.split_at_mut(FieldElement::BYTES);
        indicator[0] = 0x04;
        x.copy_from_slice(&self.x().as_bytes());
        y.copy_from_slice(&self.y().as_bytes());
        r
    }

    #[cfg(test)]
    fn slow_multiply(&self, scalar: &Scalar) -> Self {
        let mut result = JacobianPoint::infinity();
        let mut j = *self;

        for bit in scalar.bits() {
            if bit == 1 {
                result = result.public_add_affine(&j);
            }
            j = JacobianPoint::from_affine(&j).double().as_affine();
        }

        result.as_affine()
    }

    /// Returns table[i - 1] if index > 0, or else the affine point at infinity
    fn lookup_comb(table: &[u64; 288], index: u8) -> Self {
        let mut r = Self::default();
        low::bignum_aff_point_select_p521(&mut r.xy, table, index);
        r
    }

    /// Returns table[i - 1] for a public index > 0
    fn public_lookup_comb(table: &[u64; 288], index: u8) -> Self {
        let offs = (index - 1) as usize * 18;
        let mut r = Self::default();
        r.xy.copy_from_slice(&table[offs..offs + 18]);
        r
    }

    fn negate_y(&mut self) {
        let neg_y = self.y().negate();
        self.xy[Self::Y].copy_from_slice(&neg_y.0);
    }

    fn maybe_negate_y(&mut self, sign: u8) {
        let y = self.y();
        let neg_y = y.negate();
        let result = FieldElement::select(&y, &neg_y, sign);
        self.xy[Self::Y].copy_from_slice(&result.0);
    }

    /// P, 3P, ..., 15P: the odd multiples a width-5 NAF digit picks, in
    /// affine form so that each is added by `p521_jmixadd`.
    ///
    /// Each sum adds 2P to an odd multiple below n, never equal, as
    /// `p521_jadd` requires, and none is at infinity.
    fn public_odd_multiples(&self) -> [Self; 8] {
        let p = JacobianPoint::from_affine(self);
        let p2 = p.double();
        let mut multiples = [p; 8];
        for i in 1..multiples.len() {
            multiples[i] = multiples[i - 1].add(&p2);
        }
        JacobianPoint::public_batch_as_affine(&multiples)
    }

    /// 17P, 19P, ..., 31P, given P, 3P, ..., 15P: the rest of the odd
    /// multiples a width-6 NAF digit picks.
    ///
    /// Each is 16P = 15P + P plus one of those, so no sum adds equal points,
    /// as `p521_jmixadd` requires, and none is at infinity.
    fn public_more_odd_multiples(odd_multiples: &[Self; 8]) -> [Self; 8] {
        let p16 = JacobianPoint::from_affine(&odd_multiples[7]).add_affine(&odd_multiples[0]);
        let multiples = odd_multiples.map(|multiple| p16.add_affine(&multiple));
        JacobianPoint::public_batch_as_affine(&multiples)
    }
}

/// A point in Jacobian coordinates, at infinity when z is zero.
///
/// s2n-bignum's P-521 point routines require a nonzero z, and the two
/// points of an addition to differ and not be opposites, so the callers
/// here keep to those.
#[derive(Clone, Copy, Debug)]
struct JacobianPoint {
    xyz: [u64; 27],
}

impl JacobianPoint {
    const X: Range<usize> = 0..9;
    const Y: Range<usize> = 9..18;
    const XY: Range<usize> = 0..18;
    const Z: Range<usize> = 18..27;

    fn infinity() -> Self {
        Self { xyz: [0; 27] }
    }

    fn public_is_infinity(&self) -> bool {
        self.z().public_eq(&FieldElement::default())
    }

    /// 1 if this point is at infinity, else 0, in constant time.
    fn is_infinity(&self) -> u8 {
        low::bignum_eq(&self.z().0, &[0; 9]) as u8
    }

    fn x(&self) -> FieldElement {
        FieldElement(self.xyz[Self::X].try_into().unwrap())
    }

    fn y(&self) -> FieldElement {
        FieldElement(self.xyz[Self::Y].try_into().unwrap())
    }

    fn z(&self) -> FieldElement {
        FieldElement(self.xyz[Self::Z].try_into().unwrap())
    }

    /// `scalar * G`, for a `scalar` below n, by the comb layout of aws-lc's
    /// `ec_nistp_scalar_mul_base`.
    ///
    /// Window `w` of the 105 Booth-recoded 5-bit windows is `4j + t` for
    /// one tooth `t` in 0..4, and table `j` holds its multiples of
    /// `2^(20j) G`.  So each tooth's windows are added straight from the
    /// tables, and the 5 doublings between teeth supply the `2^(5t)`: 15
    /// doublings in all, rather than 520.
    ///
    /// No addition doubles or cancels, which `p521_jmixadd` cannot.  Scaled
    /// by `2^(-5t)`, the accumulator and the table point are sums of signed
    /// digits of distinct windows, so their sum and difference are nonzero
    /// integers unless one is zero, which is handled apart as infinity.
    /// Until window 104, which is added last, the accumulator is below
    /// `16/31 * 2^520` and the table point below `2^505`, so neither sum
    /// nor difference reaches n.  Window 104's digit `d` is at most 2: an
    /// equal accumulator would be `d * 2^520 - n`, out of its range for
    /// `d = 1` and making `scalar` `2^522 - n` for `d = 2`, and an opposite
    /// one would make `scalar` a multiple of n.
    fn base_multiply(scalar: &Scalar) -> Self {
        let mut windows = [(0u8, 0u8); 105];
        for ((digit, sign, _), window) in scalar
            .reversed_booth_recoded_w5()
            .zip(windows.iter_mut().rev())
        {
            *window = (digit, sign);
        }

        let mut result = Self::infinity();
        for tooth in (0..4).rev() {
            if tooth != 3 {
                // `p521_jdouble` requires a nonzero z, so infinity is kept.
                let mut doubled = result;
                doubled.double_inplace_n(5);
                result = Self::select(&doubled, &result, result.is_infinity());
            }

            for (table, &(digit, sign)) in precomp::CURVE_GENERATOR_PRECOMP_COMB
                .iter()
                .zip(windows.iter().skip(tooth).step_by(4))
            {
                let mut tmp = AffinePoint::lookup_comb(table, digit);
                tmp.maybe_negate_y(sign);
                result.add_inplace_affine(&tmp, digit);
            }
        }

        result
    }

    /// `scalar * point`, by s2n-bignum's `p521_jscalarmul`.
    fn multiply(scalar: &Scalar, point: &AffinePoint) -> Self {
        let mut r = Self::infinity();
        low::p521_jscalarmul(&mut r.xyz, &scalar.0, &Self::from_affine(point).xyz);
        r
    }

    /// `g * G + p * P` for public scalars, given P's odd multiples in rows
    /// of 8.
    ///
    /// One chain of doublings serves both: P's digits are a NAF over
    /// `odd_multiples`, width 5 for one row and 6 for two, and G's a width-5
    /// NAF over the first comb table, which holds G to 16G.
    fn public_twin_multiply(g: &Scalar, p: &Scalar, odd_multiples: &[&[AffinePoint; 8]]) -> Self {
        let (mut g_digits, mut p_digits) = ([0; 522], [0; 522]);
        util::public_naf::<5>(&g.0, &mut g_digits);
        match odd_multiples.len() {
            1 => util::public_naf::<5>(&p.0, &mut p_digits),
            _ => util::public_naf::<6>(&p.0, &mut p_digits),
        }
        let g_multiples = &precomp::CURVE_GENERATOR_PRECOMP_COMB[0];

        let mut result = Self::infinity();
        for (g_digit, p_digit) in g_digits.iter().zip(&p_digits).rev() {
            // `p521_jdouble` requires a nonzero z.
            if !result.public_is_infinity() {
                result = result.double();
            }
            if *p_digit != 0 {
                let i = usize::from(p_digit.unsigned_abs() / 2);
                let mut term = odd_multiples[i / 8][i % 8];
                if *p_digit < 0 {
                    term.negate_y();
                }
                result = result.public_add_affine(&term);
            }
            if *g_digit != 0 {
                let mut term = AffinePoint::public_lookup_comb(g_multiples, g_digit.unsigned_abs());
                if *g_digit < 0 {
                    term.negate_y();
                }
                result = result.public_add_affine(&term);
            }
        }
        result
    }

    /// `self + p`, for any points, including at infinity, equal, or opposite.
    ///
    /// `p521_jmixadd` is proven only for unequal points, so points with the
    /// same x never reach it.
    fn public_add_affine(&self, p: &AffinePoint) -> Self {
        if self.public_is_infinity() {
            return Self::from_affine(p);
        }

        // `p` scaled to this point's z.
        let z2 = self.z().sqr();
        if !p.x().mul(&z2).public_eq(&self.x()) {
            return self.add_affine(p);
        }
        match p.y().mul(&z2.mul(&self.z())).public_eq(&self.y()) {
            true => self.double(),
            false => Self::infinity(),
        }
    }

    fn from_affine(p: &AffinePoint) -> Self {
        let mut xyz = [0; 27];
        xyz[Self::XY].copy_from_slice(&p.xy);
        xyz[Self::Z].copy_from_slice(&CURVE_ONE.0);
        Self { xyz }
    }

    fn as_affine(&self) -> AffinePoint {
        self.as_affine_by(&self.z().inv())
    }

    /// `points` in affine form, none at infinity, by one inversion of the
    /// product of their z's (Montgomery's trick).
    fn public_batch_as_affine(points: &[Self; 8]) -> [AffinePoint; 8] {
        // `prefix[i]` is the product of the z's before `points[i]`.
        let mut prefix = [CURVE_ONE; 8];
        for i in 1..prefix.len() {
            prefix[i] = prefix[i - 1].mul(&points[i - 1].z());
        }
        let mut inv = prefix[7].mul(&points[7].z()).inv();

        let mut r = [AffinePoint::default(); 8];
        for i in (0..r.len()).rev() {
            // `inv` is the inverse of the z's up to `points[i]`.
            r[i] = points[i].as_affine_by(&inv.mul(&prefix[i]));
            inv = inv.mul(&points[i].z());
        }
        r
    }

    /// This point in affine form, given the inverse of its z.
    fn as_affine_by(&self, z_inv: &FieldElement) -> AffinePoint {
        // recover (x, y) from (x / z ^ 2, x / z ^ 3, z)
        let z2_inv = z_inv.sqr();
        let z3_inv = z2_inv.mul(z_inv);

        let x = self.x().mul(&z2_inv);
        let y = self.y().mul(&z3_inv);

        AffinePoint::from_xy(x, y)
    }

    fn x_scalar(&self) -> Scalar {
        // this is a faster version of `as_affine().x_scalar()`
        let z2_inv = self.z().sqr().inv();
        Scalar(self.x().mul(&z2_inv).0).reduce_mod_n()
    }

    #[must_use]
    fn double(&self) -> Self {
        let mut tmp = Self::infinity();
        low::p521_jdouble(&mut tmp.xyz, &self.xyz);
        tmp
    }

    fn double_inplace_n(&mut self, n: usize) {
        for _ in 0..n {
            let tmp = *self;
            low::p521_jdouble(&mut self.xyz, &tmp.xyz);
        }
    }

    /// Adds `p`, a table entry for `digit`, which is zero when `digit` is zero.
    ///
    /// `p521_jmixadd` requires a nonzero z, so the sum is `p` itself when
    /// this point is at infinity, and this point when `digit` is zero.
    fn add_inplace_affine(&mut self, p: &AffinePoint, digit: u8) {
        let sum = self.add_affine(p);
        let sum = Self::select(&sum, &Self::from_affine(p), self.is_infinity());
        *self = Self::select(self, &sum, digit);
    }

    #[must_use]
    fn add_affine(&self, p: &AffinePoint) -> Self {
        let mut r = Self::infinity();
        low::p521_jmixadd(&mut r.xyz, &self.xyz, &p.xy);
        r
    }

    #[must_use]
    fn add(&self, p: &Self) -> Self {
        let mut r = Self::infinity();
        low::p521_jadd(&mut r.xyz, &self.xyz, &p.xyz);
        r
    }

    /// Return p0 if select == 0, p1 otherwise
    #[must_use]
    fn select(p0: &Self, p1: &Self, select: u8) -> Self {
        let mut r = Self::infinity();
        let select = select as u64;
        low::bignum_mux(select, &mut r.xyz[..], &p1.xyz[..], &p0.xyz[..]);
        r
    }
}

/// An element of GF(p), fully reduced.  P-521's prime is a Mersenne prime,
/// so its arithmetic is direct rather than Montgomery's.
#[derive(Clone, Copy, Debug, Default)]
struct FieldElement([u64; 9]);

impl FieldElement {
    const BYTES: usize = 66;

    /// Big-endian, from the 72 bytes of the words, whose top 7 bits are zero.
    fn as_bytes(&self) -> [u8; Self::BYTES] {
        util::u64x9_to_big_endian(&self.0)[72 - Self::BYTES..]
            .try_into()
            .unwrap()
    }

    fn inv(&self) -> Self {
        let mut r = Self::default();
        low::bignum_inv_p521(&mut r.0, &self.0);
        r
    }

    /// Squaring mod p521
    fn sqr(&self) -> Self {
        let mut r = Self::default();
        low::bignum_sqr_p521(&mut r.0, &self.0);
        r
    }

    /// Addition mod p521
    fn add(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_add_p521(&mut r.0, &self.0, &other.0);
        r
    }

    /// Multiplication mod p521
    fn mul(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_mul_p521(&mut r.0, &self.0, &other.0);
        r
    }

    fn negate(&self) -> Self {
        let mut r = Self::default();
        low::bignum_neg_p521(&mut r.0, &self.0);
        r
    }

    /// Public equality
    fn public_eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }

    /// Return p0 if select == 0, p1 otherwise
    fn select(p0: &Self, p1: &Self, select: u8) -> Self {
        let mut r = Self::default();
        let select = select as u64;
        low::bignum_mux(select, &mut r.0[..], &p1.0[..], &p0.0[..]);
        r
    }
}

#[derive(Default)]
pub(crate) struct Scalar([u64; 9]);

impl Scalar {
    pub(crate) const BYTES: usize = 66;

    /// The bits of `BYTES` above n's 521.
    const EXCESS_BITS: u32 = 7;

    /// Create a scalar from the given slice, which can be any size.
    ///
    /// If it is larger than 72 bytes, the leading bytes must be
    /// zero (this is deemed a non-secret property).
    ///
    /// This returns an error if the scalar is zero or larger than
    /// the curve order.
    pub(crate) fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error> {
        let full = Self(
            util::big_endian_slice_any_size_to_u64x9(bytes)
                .ok_or(KeyFormatError::ScalarOutOfRange)?,
        );

        full.into_range_check()
    }

    pub(crate) fn from_bytes_reduced(bytes: &[u8]) -> Result<Self, Error> {
        Ok(
            Self(util::big_endian_slice_any_size_to_u64x9(bytes).ok_or(Error::WrongLength)?)
                .reduce_mod_n(),
        )
    }

    fn into_range_check(self) -> Result<Self, Error> {
        let reduced = self.reduce_mod_n();

        // Whether a scalar is in range is public: a key or signature is refused
        // on it, and a rejected nonce candidate says nothing of the one accepted.
        match low::ct::into_public(reduced.private_eq(&self) & !self.is_zero()) {
            true => Ok(self),
            false => Err(KeyFormatError::ScalarOutOfRange.into()),
        }
    }

    pub(crate) fn as_bytes(&self) -> [u8; Self::BYTES] {
        util::u64x9_to_big_endian(&self.0)[72 - Self::BYTES..]
            .try_into()
            .unwrap()
    }

    #[cfg(test)]
    fn small_u64(v: u64) -> Self {
        Self([v, 0, 0, 0, 0, 0, 0, 0, 0])
    }

    /// Private test for zero
    pub(crate) fn is_zero(&self) -> bool {
        self.private_eq(&Self::default())
    }

    /// Private equality
    fn private_eq(&self, other: &Self) -> bool {
        low::bignum_eq(&self.0, &other.0)
    }

    /// Public equality
    fn public_eq(&self, other: &Self) -> bool {
        low::bignum_eq(&self.0, &other.0)
    }

    /// Reduce mod n (curve order)
    fn reduce_mod_n(&self) -> Self {
        let mut r = Self::default();
        low::bignum_mod_n521(&mut r.0, &self.0);
        r
    }

    /// Remove one montgomery factor mod n
    fn demont(&self) -> Self {
        let mut r = Self::default();
        low::bignum_demont(&mut r.0, &self.0, &CURVE_ORDER);
        r
    }

    /// Add a montgomery factor mod n
    fn as_mont(&self) -> Self {
        let mut r = Self::default();
        low::bignum_montmul(&mut r.0, &self.0, &CURVE_ORDER_MM, &CURVE_ORDER);
        r
    }

    /// Return 2^1152 mod n, ie MM mod n
    #[cfg(test)]
    fn montifier() -> Self {
        let mut r = Self::default();
        let mut tmp = Self::default();
        low::bignum_montifier(&mut r.0, &CURVE_ORDER, &mut tmp.0);
        r
    }

    /// Montgomery multiplication mod n
    ///
    /// Assumes `self` and `other` are in montgomery domain.
    /// Result is in montgomery domain.
    fn mont_mul(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_montmul(&mut r.0, &self.0, &other.0, &CURVE_ORDER);
        r
    }

    /// Find the multiplicative inverse of `self` mod n
    fn inv(&self) -> Self {
        let mut r = Self::default();
        let mut temp = [0u64; 9 * 3];
        low::bignum_modinv(&mut r.0, &self.0, &CURVE_ORDER, &mut temp);
        r
    }

    /// Add `self` + `other` mod n
    fn add(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_modadd(&mut r.0, &self.0, &other.0, &CURVE_ORDER);
        r
    }

    /// Iterator of the bits of the element, lowest first
    #[cfg(test)]
    fn bits(&self) -> impl Iterator<Item = u8> + '_ {
        (0..576).map(|i| ((self.0[i / 64] >> (i % 64)) & 1) as u8)
    }

    /// Iterator of 105 5-bit windows, highest first, each a digit, its sign,
    /// and whether it is the last
    fn reversed_booth_recoded_w5(&self) -> BoothRecodeW5 {
        BoothRecodeW5::new(self)
    }
}

struct BoothRecodeW5 {
    // little endian
    bytes: [u8; 73],
    index: usize,
}

impl BoothRecodeW5 {
    fn new(scalar: &Scalar) -> Self {
        let mut bytes = [0u8; 73];
        for (chunk, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(scalar.0) {
            *chunk = word.to_le_bytes();
        }

        Self { bytes, index: 520 }
    }

    fn recode(v: u8) -> (u8, u8) {
        // see the comment above boringssl's `ec_GFp_nistp_recode_scalar_bits` for
        // references
        let sign = !((v >> 5).wrapping_sub(1));

        let d = (1u16 << 6).wrapping_sub(v as u16).wrapping_sub(1) as u8;
        let d = (d & sign) | (v & !sign);
        let d = (d >> 1).wrapping_add(d & 1);

        (d, sign & 1)
    }
}

impl Iterator for BoothRecodeW5 {
    type Item = (u8, u8, bool);

    fn next(&mut self) -> Option<Self::Item> {
        const MASK: u8 = (1 << (5 + 1)) - 1;

        match self.index {
            5..=520 => {
                let offset = (self.index - 1) / 8;
                let shift = (self.index - 1) % 8;
                let value = (((self.bytes[offset] as u16) | ((self.bytes[offset + 1] as u16) << 8))
                    >> shift) as u8
                    & MASK;
                let (digit, sign) = Self::recode(value);
                self.index -= 5;
                Some((digit, sign, false))
            }

            0 => {
                let value = (self.bytes[0] << 1) & MASK;
                let (digit, sign) = Self::recode(value);
                self.index = usize::MAX;
                Some((digit, sign, true))
            }

            _ => None,
        }
    }
}

/// 27 tables of 16 affine points
type AffinePointTableComb = [[u64; 288]; 27];

/// a, which is -3
const CURVE_A: FieldElement = FieldElement([
    0xffff_ffff_ffff_fffc,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x0000_0000_0000_01ff,
]);

const CURVE_B: FieldElement = FieldElement([
    0xef45_1fd4_6b50_3f00,
    0x3573_df88_3d2c_34f1,
    0x1652_c0bd_3bb1_bf07,
    0x5619_3951_ec7e_937b,
    0xb8b4_8991_8ef1_09e1,
    0xa2da_725b_99b3_15f3,
    0x929a_21a0_b685_40ee,
    0x953e_b961_8e1c_9a1f,
    0x0000_0000_0000_0051,
]);

const CURVE_ONE: FieldElement = FieldElement([1, 0, 0, 0, 0, 0, 0, 0, 0]);

const CURVE_PRIME: [u64; 9] = [
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x0000_0000_0000_01ff,
];

const CURVE_ORDER: [u64; 9] = [
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

/// 2^1152 mod n: the Montgomery factor, 2^576, squared.
const CURVE_ORDER_MM: [u64; 9] = [
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

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    // The key's Debug, which no public type's Debug reaches, shows nothing of it.
    #[test]
    fn private_key_debug() {
        let key = PrivateKey::new_random().unwrap();
        assert_eq!(format!("{key:?}"), "PrivateKey { .. }");
    }

    use super::*;

    const CURVE_GENERATOR: AffinePoint = AffinePoint {
        xy: [
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
        ],
    };

    fn n_minus(k: u64) -> Scalar {
        let mut s = CURVE_ORDER;
        s[0] -= k;
        Scalar(s)
    }

    /// Scalars at the edges of the windowed multiplications: small ones,
    /// one top bit, and those near n, including n - 2 to n - 32, whose last
    /// window doubles in `public_multiply_w5`.
    fn edge_scalars() -> impl Iterator<Item = Scalar> {
        [1, 2, 3, 16, 17, 31, 32, 33, 99999999]
            .into_iter()
            .map(Scalar::small_u64)
            .chain([Scalar([0, 0, 0, 0, 0, 0, 0, 0, 0x100])])
            .chain((1..=34).map(n_minus))
    }

    #[test]
    fn generator_on_curve() {
        assert!(CURVE_GENERATOR.on_curve());
    }

    #[test]
    fn multiplications_match_double_and_add() {
        let point = CURVE_GENERATOR.slow_multiply(&Scalar::small_u64(5));
        let odd_multiples = point.public_odd_multiples();
        let more = AffinePoint::public_more_odd_multiples(&odd_multiples);
        let both = [&[&odd_multiples][..], &[&odd_multiples, &more]];
        for scalar in edge_scalars() {
            let expected = point.slow_multiply(&scalar).xy;
            assert_eq!(
                JacobianPoint::multiply(&scalar, &point).as_affine().xy,
                expected
            );
            let zero = Scalar::default();
            for rows in both {
                assert_eq!(
                    JacobianPoint::public_twin_multiply(&zero, &scalar, rows)
                        .as_affine()
                        .xy,
                    expected
                );
            }

            let expected = CURVE_GENERATOR.slow_multiply(&scalar).xy;
            assert_eq!(
                JacobianPoint::base_multiply(&scalar).as_affine().xy,
                expected
            );
            for rows in both {
                assert_eq!(
                    JacobianPoint::public_twin_multiply(&scalar, &zero, rows)
                        .as_affine()
                        .xy,
                    expected
                );
            }
        }
    }

    #[test]
    fn public_add_affine_edges() {
        let g = JacobianPoint::from_affine(&CURVE_GENERATOR);
        let g2 = g.double();
        let negate = |p: &JacobianPoint| {
            let mut r = *p;
            r.xyz[JacobianPoint::Y].copy_from_slice(&p.y().negate().0);
            r
        };
        // 2G again, as 4G - 2G, with another z.
        let g2_again = g2.double().add(&negate(&g2));
        assert_ne!(g2_again.z().0, g2.z().0);
        let infinity = JacobianPoint::infinity();
        let mut neg_g = CURVE_GENERATOR;
        neg_g.negate_y();

        assert_eq!(
            g.public_add_affine(&CURVE_GENERATOR).as_affine().xy,
            g2.as_affine().xy
        );
        assert_eq!(
            g2_again.public_add_affine(&g2.as_affine()).as_affine().xy,
            g2.double().as_affine().xy
        );
        assert!(
            negate(&g2_again)
                .public_add_affine(&g2.as_affine())
                .public_is_infinity()
        );
        assert!(g.public_add_affine(&neg_g).public_is_infinity());
        assert_eq!(infinity.public_add_affine(&CURVE_GENERATOR).xyz, g.xyz);
    }

    #[test]
    fn twin_multiply_exceptional() {
        // The accumulator meets the point it adds: equal, which must double,
        // or opposite, which must give infinity. With P = G it meets G's
        // multiples, and with P = 2G, P's.
        let odd_multiples = CURVE_GENERATOR.public_odd_multiples();
        let more = AffinePoint::public_more_odd_multiples(&odd_multiples);
        for (g, p) in [
            (Scalar::small_u64(1), Scalar::small_u64(1)),
            (Scalar::small_u64(3), Scalar::small_u64(3)),
            (Scalar::small_u64(2), Scalar::small_u64(1)),
            (Scalar::small_u64(1), n_minus(1)),
            (n_minus(5), Scalar::small_u64(5)),
            (n_minus(1), n_minus(1)),
        ] {
            let sum = g.add(&p);
            let expected = CURVE_GENERATOR.slow_multiply(&sum).xy;
            for rows in [&[&odd_multiples][..], &[&odd_multiples, &more]] {
                let result = JacobianPoint::public_twin_multiply(&g, &p, rows);
                assert_eq!(result.as_affine().xy, expected);
                // Verification refuses a sum at infinity by this check, and the
                // constant-time multiplications keep infinity by the other.
                let infinity = sum.0 == [0; 9];
                assert_eq!(result.public_is_infinity(), infinity);
                assert_eq!(result.is_infinity(), u8::from(infinity));
            }
        }

        let p2 = JacobianPoint::from_affine(&CURVE_GENERATOR)
            .double()
            .as_affine();
        let odd_multiples = p2.public_odd_multiples();
        let more = AffinePoint::public_more_odd_multiples(&odd_multiples);
        for (g, p) in [
            (Scalar::small_u64(2), Scalar::small_u64(1)),
            (Scalar::small_u64(6), Scalar::small_u64(3)),
        ] {
            let expected = CURVE_GENERATOR.slow_multiply(&g.add(&p).add(&p)).xy;
            for rows in [&[&odd_multiples][..], &[&odd_multiples, &more]] {
                assert_eq!(
                    JacobianPoint::public_twin_multiply(&g, &p, rows)
                        .as_affine()
                        .xy,
                    expected
                );
            }
        }
    }

    #[test]
    fn generate_key_known_answer() {
        // From RFC6979 A.2.7.
        let private = PrivateKey::from_bytes(&hex::decode("00fad06daa62ba3b25d2fb40133da757205de67f5bb0018fee8c86e1b68c7e75caa896eb32f1f47c70855836a6d16fcc1466f6d8fbec67db89ec0c08b0e996b83538").unwrap()).unwrap();
        let public = private.public_key_uncompressed();
        assert_eq!(
            hex::encode(public),
            "04\
             01894550d0785932e00eaa23b694f213f8c3121f86dc97a04e5a7167db4e5bcd371123d46e45db6b5d5370a7f20fb633155d38ffa16d2bd761dcac474b9a2f5023a4\
             00493101c962cd4d2fddf782285e64584139c2f91b47f87ff82354d6630f746a28a0db25741b5b34a828008b22acc23f924faafbd4d33f81ea66956dfeaa2bfdfcf5"
        );
        PublicKey::from_x962_uncompressed(&public).unwrap();
    }

    #[test]
    fn generate_takes_leftmost_521_bits() {
        // RFC6979's bits2int: the top 7 of 528 bits drawn are dropped.
        let mut drawn = [0xffu8; Scalar::BYTES];
        drawn[0] = 0x00;
        drawn[1] = 0x80;
        let key = PrivateKey::generate(&mut crate::mid::rng::SliceRandomSource(&drawn)).unwrap();
        let mut expected = [0xffu8; Scalar::BYTES];
        expected[0] = 0x00;
        expected[1] = 0x01;
        expected[2] = 0x01;
        assert_eq!(low::ct::into_public(key.scalar.as_bytes()), expected);
    }

    #[test]
    fn test_scalar() {
        let mut one = [0u8; 66];
        one[65] = 1;
        let scalar = Scalar::from_bytes_checked(&one);
        assert!(scalar.is_ok());
        assert_eq!(scalar.unwrap().as_bytes(), Scalar::small_u64(1).as_bytes());

        assert!(Scalar::from_bytes_checked(&[0xff; 66]).is_err());
    }

    #[test]
    fn private_key_in_range() {
        assert_eq!(
            PrivateKey::from_bytes(&[0u8; 66]).unwrap_err(),
            Error::from(KeyFormatError::ScalarOutOfRange)
        );

        let order = Scalar(CURVE_ORDER).as_bytes();
        assert_eq!(
            PrivateKey::from_bytes(&order).unwrap_err(),
            Error::from(KeyFormatError::ScalarOutOfRange)
        );
        let mut order_plus_1 = order;
        order_plus_1[65] += 1;
        assert_eq!(
            PrivateKey::from_bytes(&order_plus_1).unwrap_err(),
            Error::from(KeyFormatError::ScalarOutOfRange)
        );
        PrivateKey::from_bytes(&n_minus(1).as_bytes()).unwrap();
    }

    #[test]
    fn montifier() {
        assert_eq!(Scalar::montifier().0, CURVE_ORDER_MM);
    }

    /// Checks each point of `admin/p521-precomp`'s table, which uses
    /// Python's integers, against rind's own arithmetic.
    #[test]
    fn base_point_precomp_comb() {
        let mut base = JacobianPoint::from_affine(&CURVE_GENERATOR);
        for table in &precomp::CURVE_GENERATOR_PRECOMP_COMB {
            let mut multiple = base;
            for (i, entry) in (1..).zip(table.as_chunks::<18>().0) {
                assert_eq!(&multiple.as_affine().xy, entry);
                multiple = match i {
                    1 => multiple.double(),
                    _ => multiple.add(&base),
                };
            }
            base.double_inplace_n(20);
        }
    }
}
