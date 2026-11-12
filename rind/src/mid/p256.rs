// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::ops::Range;

use super::util;
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::{RandomSource, SystemRandom};

#[path = "p256_group.rs"]
pub(crate) mod group;
mod precomp;

/// A P-256 public key.
#[derive(Clone, Debug)]
pub(crate) struct PublicKey {
    point: AffineMontPoint,
}

impl PublicKey {
    pub(crate) const BYTES: usize = 1 + FieldElement::BYTES + FieldElement::BYTES;

    /// Create an P-256 [`PublicKey`] from a byte slice.
    ///
    /// This must be exactly 65 bytes in length, using the X9.62
    /// uncompressed encoding.  An error is returned if a coordinate
    /// is not below the field prime, or the point is not on the curve.
    pub(crate) fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        let point = AffineMontPoint::from_x962_uncompressed(bytes)?;
        Ok(Self { point })
    }

    /// Decompress an X9.62 compressed point to its uncompressed encoding,
    /// written to the start of `output`, which
    /// [`Self::from_x962_uncompressed`] takes.
    ///
    /// An error is returned unless `bytes` is 33 bytes with tag 2 or 3, its
    /// `x` is below the field prime, and a point on the curve has that `x`.
    pub(crate) fn decompress<'a>(bytes: &[u8], output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = low::Entry::new_public();
        let point = AffineMontPoint::from_x962_compressed(bytes)?;
        let output = output.get_mut(..Self::BYTES).ok_or(Error::WrongLength)?;
        output.copy_from_slice(&point.as_bytes_uncompressed());
        Ok(output)
    }
}

/// A P-256 public key for ECDSA verification.
///
/// It builds the point's multiples on its first verification and keeps
/// them, so verifying again skips computing them, and a key never verified
/// with, such as an ECDSA key pair's, never pays for them.
#[derive(Clone, Debug)]
pub(crate) struct VerifyingKey {
    point: AffineMontPoint,
    /// P, 3P, ..., 15P.
    odd_multiples: low::ReuseCache<[AffineMontPoint; 8]>,
    /// 17P, 19P, ..., 31P, which widen P's digits but pay for building
    /// only once a key is reused.
    more_odd_multiples: low::ReuseCache<[AffineMontPoint; 8]>,
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
            .get_or_build(|| AffineMontPoint::public_more_odd_multiples(&odd_multiples));
        let point = JacobianMontPoint::public_twin_multiply(&u1, &u2, &odd_multiples, more);

        if point.public_is_infinity() {
            return Err(Error::BadSignature);
        }

        // 6. Convert the field element xR to an integer xR using the conversion routine specified in Section 2.3.9.
        // 7. Set v = xR mod n.
        // 8. Compare v and r — if v = r, output "valid", and if v != r, output "invalid".
        match point.public_x_is(r) {
            true => Ok(()),
            false => Err(Error::BadSignature),
        }
    }
}

/// A P-256 private key.
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
        let result = peer.point.multiply(&self.scalar);
        match low::ct::into_public(result.on_curve()) {
            true => Ok(SharedSecret(util::u64x4_to_big_endian(
                &result.x().demont().0,
            ))),
            false => Err(Error::Fault),
        }
    }

    fn public_point(&self) -> AffineMontPoint {
        let point = low::ct::into_public(AffineMontPoint::base_multiply(&self.scalar));
        match point.on_curve() {
            true => point,
            false => panic!("internal fault"),
        }
    }

    pub(crate) fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        for _ in 0..64 {
            let mut r = [0u8; Scalar::BYTES];
            rng.fill(&mut r)?;
            low::ct::secret_slice(&r);
            if let Ok(p) = Self::from_bytes(&r) {
                return Ok(p);
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

/// A P-256 static private key.
///
/// This backs ECDSA, so it can be serialized and deserialized.
pub(crate) struct StaticPrivateKey(PrivateKey);

impl StaticPrivateKey {
    /// Generate a new random private key using the system RNG.
    #[cfg(test)]
    pub(crate) fn new_random() -> Result<Self, Error> {
        PrivateKey::generate(&mut SystemRandom).map(Self)
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

    /// Whether `encoded`, an X9.62 uncompressed point, is this key's public
    /// key.
    ///
    /// This checks the point against the Jacobian product, x * z² = X and
    /// y * z³ = Y, as BoringSSL's `EC_KEY_check_key` does, so it needs no
    /// inversion. Equal words are equal mod p, and z is not zero for a
    /// scalar in [1, n), so a match is this key's point; the parse refused
    /// coordinates at or above p, so the encoding is the canonical one. The
    /// key's own point matches because aws-lc's addition leaves X, Y, and z
    /// below p: `twins_agree` checks it word for word against s2n-bignum's,
    /// whose proof bounds them. They stay secret, as z says something of the
    /// scalar: only the answer is public.
    #[cfg(rind_backend = "x86_64")]
    pub(crate) fn public_key_is_uncompressed(&self, encoded: &[u8]) -> bool {
        let _entry = low::Entry::new_secret();
        let Ok(PublicKey { point }) = PublicKey::from_x962_uncompressed(encoded) else {
            return false;
        };
        let product = JacobianMontPoint::base_multiply(&self.0.scalar);
        let z2 = product.z().mont_sqr();
        let z3 = z2.mont_mul(&product.z());
        let x = point.x().mont_mul(&z2);
        let y = point.y().mont_mul(&z3);
        low::ct::into_public(
            low::bignum_eq(&x.0, &product.x().0) & low::bignum_eq(&y.0, &product.y().0),
        )
    }

    pub(crate) fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        PrivateKey::generate(rng).map(Self)
    }

    pub(crate) fn public_key_x_scalar(&self) -> Scalar {
        let _entry = low::Entry::new_secret();
        self.0.public_point().x_scalar()
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

/// A shared secret output from a P-256 Diffie-Hellman operation.
///
/// It is not wiped on drop: `agreement::SharedSecret` wipes it.
pub(crate) struct SharedSecret(pub(crate) [u8; FieldElement::BYTES]);

#[derive(Clone, Copy, Debug, Default)]
struct AffineMontPoint {
    xy: [u64; 8],
}

impl AffineMontPoint {
    const X: Range<usize> = 0..4;
    const Y: Range<usize> = 4..8;

    fn from_x962_uncompressed(bytes: &[u8]) -> Result<Self, Error> {
        match bytes.first() {
            Some(&0x04) => (),
            Some(_) => return Err(KeyFormatError::Compressed.into()),
            None => return Err(KeyFormatError::WrongLength.into()),
        }

        if bytes.len() != PublicKey::BYTES {
            return Err(KeyFormatError::WrongLength.into());
        }

        let (_, xy) = bytes.split_at(1);
        let (x, y) = xy.split_at(FieldElement::BYTES);

        let x = util::big_endian_slice_to_u64x4(x).unwrap();
        let y = util::big_endian_slice_to_u64x4(y).unwrap();

        // A coordinate at or above p would be reduced, giving the point a
        // second encoding.
        if !public_below_p(&x) || !public_below_p(&y) {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        let point = Self::from_xy(FieldElement(x).as_mont(), FieldElement(y).as_mont());

        if !point.on_curve() {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        Ok(point)
    }

    /// Decodes an X9.62 compressed point: `x`, and the parity of `y`.
    ///
    /// p is 3 mod 4, so a square's root is its `(p + 1) / 4`th power
    /// (Euler's criterion). The root is squared back, so an `x` with no
    /// point is refused rather than given one. No point of a curve of prime
    /// order has `y = 0`, so `y` and `p - y` differ in parity.
    fn from_x962_compressed(bytes: &[u8]) -> Result<Self, Error> {
        let (tag, x) = match bytes.split_first() {
            Some((&tag @ (0x02 | 0x03), x)) => (tag, x),
            Some(_) => return Err(KeyFormatError::PointEncoding.into()),
            None => return Err(KeyFormatError::WrongLength.into()),
        };
        let x = util::big_endian_slice_to_u64x4(x).ok_or(KeyFormatError::WrongLength)?;
        if !public_below_p(&x) {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        let x = FieldElement(x).as_mont();
        let rhs = x
            .mont_sqr()
            .add(&CURVE_A_MONT)
            .mont_mul(&x)
            .add(&CURVE_B_MONT);
        let y = rhs.mont_sqrt_candidate();
        if !y.mont_sqr().public_eq(&rhs) {
            return Err(KeyFormatError::NotOnCurve.into());
        }

        let y = y.demont();
        let y = match y.0[0] & 1 == u64::from(tag & 1) {
            true => y,
            false => y.negate_mod_p(),
        };
        Ok(Self::from_xy(x, y.as_mont()))
    }

    fn x_scalar(&self) -> Scalar {
        let bytes = self.as_bytes_uncompressed();
        Scalar::from_bytes_reduced(&bytes[1..1 + Scalar::BYTES]).unwrap()
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
        let rhs = x.mont_sqr(); // x ^ 2
        let rhs = rhs.add(&CURVE_A_MONT); // x ^ 2 + a
        let rhs = rhs.mont_mul(&x); // (x ^ 2 + a) * x   equiv  x ^ 3 + ax
        let rhs = rhs.add(&CURVE_B_MONT);

        let lhs = self.y().mont_sqr();

        // Constant time, since `diffie_hellman` checks a secret point.
        low::bignum_eq(&lhs.0, &rhs.0)
    }

    fn as_bytes_uncompressed(&self) -> [u8; PublicKey::BYTES] {
        let mut r = [0u8; PublicKey::BYTES];
        let (indicator, xy) = r.split_at_mut(1);
        let (x, y) = xy.split_at_mut(FieldElement::BYTES);

        indicator[0] = 0x04;
        x.copy_from_slice(&util::u64x4_to_big_endian(&self.x().demont().0));
        y.copy_from_slice(&util::u64x4_to_big_endian(&self.y().demont().0));
        r
    }

    #[cfg(test)]
    fn slow_multiply(&self, scalar: &Scalar) -> Self {
        let mut result = JacobianMontPoint::infinity();

        let mut j = JacobianMontPoint::from_affine(self);
        let zero = JacobianMontPoint::zero();

        for bit in scalar.bits() {
            result.add_inplace(&JacobianMontPoint::select(&zero, &j, bit));
            j = j.double();
        }

        result.as_affine()
    }

    fn negate_y(&mut self) {
        let neg_y = self.y().negate_mod_p();
        self.xy[Self::Y].copy_from_slice(&neg_y.0);
    }

    /// P, 3P, ..., 15P: the odd multiples a width-5 NAF digit picks, in
    /// affine form so that each is added by `p256_montjmixadd`.
    ///
    /// Each sum adds 2P to an odd multiple below n, never equal, as
    /// `p256_montjadd` requires, and none is at infinity.
    fn public_odd_multiples(&self) -> [Self; 8] {
        let p = JacobianMontPoint::from_affine(self);
        let p2 = p.double();
        let mut multiples = [p; 8];
        for i in 1..multiples.len() {
            multiples[i] = multiples[i - 1].add(&p2);
        }
        JacobianMontPoint::public_batch_as_affine(&multiples)
    }

    /// 17P, 19P, ..., 31P, given P, 3P, ..., 15P: the rest of the odd
    /// multiples a width-6 NAF digit picks.
    ///
    /// Each is 16P = 15P + P plus one of those, so no sum adds equal points,
    /// as `p256_montjmixadd` requires, and none is at infinity.
    fn public_more_odd_multiples(odd_multiples: &[Self; 8]) -> [Self; 8] {
        let mut p16 = JacobianMontPoint::from_affine(&odd_multiples[7]);
        p16.add_inplace_affine(&odd_multiples[0]);
        let multiples = odd_multiples.map(|multiple| {
            let mut sum = p16;
            sum.add_inplace_affine(&multiple);
            sum
        });
        JacobianMontPoint::public_batch_as_affine(&multiples)
    }

    /// `scalar * self`, by s2n-bignum's `p256_montjscalarmul`.
    #[cfg(not(rind_backend = "aarch64"))]
    fn multiply(&self, scalar: &Scalar) -> Self {
        JacobianMontPoint::multiply(scalar, self).as_affine()
    }

    /// `scalar * self`, by s2n-bignum's `p256_scalarmul`.
    ///
    /// Its proof covers the aarch64 routine from affine input to affine
    /// output, inversion included, for any scalar and a point on the curve,
    /// which `self` is. It takes and returns plain coordinates, the result
    /// proven only mod p, which `as_mont` reduces.
    #[cfg(rind_backend = "aarch64")]
    fn multiply(&self, scalar: &Scalar) -> Self {
        let point = Self::from_xy(self.x().demont(), self.y().demont());
        let mut xy = [0; 8];
        low::p256_scalarmul(&mut xy, &scalar.0, &point.xy);
        let x = FieldElement(xy[Self::X].try_into().unwrap());
        let y = FieldElement(xy[Self::Y].try_into().unwrap());
        Self::from_xy(x.as_mont(), y.as_mont())
    }

    /// `scalar * G`, by aws-lc's routines over the generator table.
    #[cfg(rind_backend = "x86_64")]
    fn base_multiply(scalar: &Scalar) -> Self {
        JacobianMontPoint::base_multiply(scalar).as_affine()
    }

    /// `scalar * G`, by s2n-bignum's `p256_scalarmulbase` over the
    /// generator table.
    ///
    /// Its proof, which covers the aarch64 routine, assumes the table holds
    /// exactly the multiples of G that `admin/p256-precomp` writes, and
    /// returns plain affine coordinates.
    #[cfg(not(rind_backend = "x86_64"))]
    fn base_multiply(scalar: &Scalar) -> Self {
        let mut xy = [0; 8];
        low::p256_scalarmulbase(&mut xy, &scalar.0, &precomp::CURVE_GENERATOR_PRECOMP);
        let x = FieldElement(xy[Self::X].try_into().unwrap());
        let y = FieldElement(xy[Self::Y].try_into().unwrap());
        Self::from_xy(x.as_mont(), y.as_mont())
    }

    /// Returns `row[index - 1]`, for a public `index` above zero.
    fn public_lookup(row: &[u64], index: u8) -> Self {
        Self {
            xy: row.as_chunks::<8>().0[index as usize - 1],
        }
    }

    /// Becomes `row`'s point `digit - 1`, or zeros for a zero `digit`, with
    /// `y` negated if `negate` is 1, in constant time.
    #[cfg(rind_backend = "x86_64")]
    fn select_w7(&mut self, row: &low::P256GeneratorRow, digit: u8, negate: u8) {
        low::p256_select_w7(&mut self.xy, row, digit);
        let y = self.y();
        low::bignum_mux(
            negate.into(),
            &mut self.xy[Self::Y],
            &y.negate_mod_p().0,
            &y.0,
        );
    }
}

#[derive(Clone, Copy, Debug)]
struct JacobianMontPoint {
    xyz: [u64; 12],
}

impl JacobianMontPoint {
    const X: Range<usize> = 0..4;
    const Y: Range<usize> = 4..8;
    const XY: Range<usize> = 0..8;
    const Z: Range<usize> = 8..12;

    fn infinity() -> Self {
        Self {
            xyz: [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
        }
    }

    fn public_is_infinity(&self) -> bool {
        self.z().public_eq(&FieldElement::default())
    }

    fn zero() -> Self {
        Self { xyz: [0; 12] }
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

    /// `scalar * point`, by s2n-bignum's `p256_montjscalarmul`.
    #[cfg(not(rind_backend = "aarch64"))]
    fn multiply(scalar: &Scalar, point: &AffineMontPoint) -> Self {
        let mut r = Self::zero();
        low::p256_montjscalarmul(&mut r.xyz, &scalar.0, &Self::from_affine(point).xyz);
        r
    }

    /// `scalar * G`, as aws-lc's `ecp_nistz256_point_mul_base` computes it:
    /// one addition from each generator table row per Booth-recoded 7-bit
    /// window, with every row scanned whole.
    ///
    /// No addition doubles, which `p256_point_add_affine` cannot: the
    /// accumulator sums lower windows, so it is a smaller integer than the
    /// table point, in magnitude, and below n.
    #[cfg(rind_backend = "x86_64")]
    fn base_multiply(scalar: &Scalar) -> Self {
        let mut windows = precomp::CURVE_GENERATOR_PRECOMP
            .iter()
            .zip(scalar.booth_recoded::<BASE_WINDOW>());
        let mut point = AffineMontPoint::default();

        // unwrap: the number of windows is constant. The first point is
        // infinity, with a zero `z`, when its digit is zero.
        let (row, (digit, sign)) = windows.next().unwrap();
        point.select_w7(row, digit, sign);
        let mut result = Self::from_affine(&point);
        low::bignum_mux(
            digit.into(),
            &mut result.xyz[Self::Z],
            &CURVE_ONE_MONT.0,
            &[0; 4],
        );

        for (row, (digit, sign)) in windows {
            point.select_w7(row, digit, sign);
            low::p256_point_add_affine(&mut result.xyz, &point.xy);
        }
        result
    }

    /// `g * G + p * P` for public scalars, given P, 3P, ..., 15P, and 17P,
    /// ..., 31P if `more` holds them.
    ///
    /// One chain of doublings serves both: P's digits are a NAF over its odd
    /// multiples, width 5 without `more` and 6 with it, and G's a width-6 NAF
    /// over the generator table's first row, which holds G to at least 32G.
    ///
    /// The rows are two arguments, and the digits indexed rather than zipped,
    /// as Aeneas cannot translate a slice of borrowed rows or the zip.
    fn public_twin_multiply(
        g: &Scalar,
        p: &Scalar,
        odd_multiples: &[AffineMontPoint; 8],
        more: Option<&[AffineMontPoint; 8]>,
    ) -> Self {
        let g_digits = g.public_naf::<6>();
        let p_digits = match more {
            None => p.public_naf::<5>(),
            Some(_) => p.public_naf::<6>(),
        };
        let g_multiples = &precomp::CURVE_GENERATOR_PRECOMP[0][..];

        let mut result = Self::infinity();
        for i in (0..g_digits.len()).rev() {
            let (g_digit, p_digit) = (&g_digits[i], &p_digits[i]);
            if !result.public_is_infinity() {
                result = result.double();
            }
            if *p_digit != 0 {
                let i = usize::from(p_digit.unsigned_abs() / 2);
                let mut tmp = match more {
                    Some(more) if i >= 8 => more[i - 8],
                    _ => odd_multiples[i],
                };
                if *p_digit < 0 {
                    tmp.negate_y();
                }
                result = result.public_add_affine(&tmp);
            }
            if *g_digit != 0 {
                let mut tmp = AffineMontPoint::public_lookup(g_multiples, g_digit.unsigned_abs());
                if *g_digit < 0 {
                    tmp.negate_y();
                }
                result = result.public_add_affine(&tmp);
            }
        }
        result
    }

    fn from_affine(p: &AffineMontPoint) -> Self {
        let mut xyz: [u64; 12] = Default::default();
        xyz[Self::XY].copy_from_slice(&p.xy);
        xyz[Self::Z].copy_from_slice(&CURVE_ONE_MONT.0);
        Self { xyz }
    }

    // aarch64's `p256_scalarmul` makes its result affine itself.
    #[cfg(any(test, not(rind_backend = "aarch64")))]
    fn as_affine(&self) -> AffineMontPoint {
        // inversion calculated outside montgomery domain
        // (benchmarked vs addition chain in montgomery)
        self.as_affine_by(&self.z().demont().inv().as_mont())
    }

    /// `points` in affine form, none at infinity, by one inversion of the
    /// product of their z's (Montgomery's trick).
    fn public_batch_as_affine(points: &[Self; 8]) -> [AffineMontPoint; 8] {
        // `prefix[i]` is the product of the z's before `points[i]`.
        let mut prefix = [CURVE_ONE_MONT; 8];
        for i in 1..prefix.len() {
            prefix[i] = prefix[i - 1].mont_mul(&points[i - 1].z());
        }
        let product = prefix[7].mont_mul(&points[7].z());
        let mut inv = product.demont().inv().as_mont();

        let mut r = [AffineMontPoint::default(); 8];
        for i in (0..r.len()).rev() {
            // `inv` is the inverse of the z's up to `points[i]`.
            r[i] = points[i].as_affine_by(&inv.mont_mul(&prefix[i]));
            inv = inv.mont_mul(&points[i].z());
        }
        r
    }

    /// This point in affine form, given the inverse of its z.
    fn as_affine_by(&self, z_inv: &FieldElement) -> AffineMontPoint {
        // recover (x, y) from (x / z ^ 2, x / z ^ 3, z)
        let z2_inv = z_inv.mont_sqr();
        let z3_inv = z2_inv.mont_mul(z_inv);

        let x = self.x().mont_mul(&z2_inv);
        let y = self.y().mont_mul(&z3_inv);

        AffineMontPoint::from_xy(x, y)
    }

    /// `self + p`, for any points, including at infinity, equal, or opposite.
    ///
    /// `p256_montjmixadd` is proven only for unequal points, so points with
    /// the same x never reach it.
    fn public_add_affine(&self, p: &AffineMontPoint) -> Self {
        if self.public_is_infinity() {
            return Self::from_affine(p);
        }

        // `p` scaled to this point's z.
        let z2 = self.z().mont_sqr();
        if !p.x().mont_mul(&z2).public_eq(&self.x()) {
            let mut sum = *self;
            sum.add_inplace_affine(p);
            return sum;
        }
        match p.y().mont_mul(&z2.mont_mul(&self.z())).public_eq(&self.y()) {
            true => self.double(),
            false => Self::infinity(),
        }
    }

    /// Whether this point's x, reduced mod n, is `r`, for a point not at
    /// infinity.
    ///
    /// x = X / z², so this checks X = r * z², and (r + n) * z² when that is
    /// below p, the only other x that reduces to `r`. Unlike computing x,
    /// that needs no inversion.
    fn public_x_is(&self, r: &Scalar) -> bool {
        let z2 = self.z().mont_sqr();
        let is = |x: [u64; 4]| FieldElement(x).as_mont().mont_mul(&z2).public_eq(&self.x());
        if is(r.0) {
            return true;
        }
        let mut r_plus_n = [0; 4];
        let mut carry = false;
        for i in 0..4 {
            let (s, c1) = r.0[i].overflowing_add(CURVE_ORDER[i]);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            r_plus_n[i] = s;
            carry = c1 | c2;
        }
        !carry && public_below_p(&r_plus_n) && is(r_plus_n)
    }

    #[must_use]
    fn double(&self) -> Self {
        let mut tmp = Self::zero();
        low::p256_montjdouble(&mut tmp.xyz, &self.xyz);
        tmp
    }

    #[cfg(test)]
    fn double_inplace_n(&mut self, n: usize) {
        for _ in 0..n {
            let tmp = *self;
            low::p256_montjdouble(&mut self.xyz, &tmp.xyz);
        }
    }

    #[cfg(test)]
    fn add_inplace(&mut self, p: &Self) {
        let mut r = Self::infinity();
        low::p256_montjadd(&mut r.xyz, &self.xyz, &p.xyz);
        *self = r;
    }

    fn add_inplace_affine(&mut self, p: &AffineMontPoint) {
        let mut r = Self::infinity();
        low::p256_montjmixadd(&mut r.xyz, &self.xyz, &p.xy);
        *self = r;
    }

    #[must_use]
    fn add(&self, p: &Self) -> Self {
        let mut r = Self::infinity();
        low::p256_montjadd(&mut r.xyz, &self.xyz, &p.xyz);
        r
    }

    /// Return p0 if select == 0, p1 otherwise
    #[cfg(test)]
    #[must_use]
    fn select(p0: &Self, p1: &Self, select: u8) -> Self {
        let mut r = Self::zero();
        let select = select as u64;
        low::bignum_mux(select, &mut r.xyz[..], &p1.xyz[..], &p0.xyz[..]);
        r
    }
}

/// Whether `v` is below p, for public `v`.
///
/// A loop from the top limb rather than `Iterator::lt`, which Aeneas cannot
/// translate; the compiled code is the same.
fn public_below_p(v: &[u64; 4]) -> bool {
    for i in 0..4 {
        let j = 3 - i;
        if v[j] != CURVE_PRIME[j] {
            return v[j] < CURVE_PRIME[j];
        }
    }
    false
}

#[derive(Clone, Copy, Debug, Default)]
struct FieldElement([u64; 4]);

impl FieldElement {
    const BYTES: usize = 32;

    fn inv(&self) -> Self {
        let mut r = Self::default();
        low::bignum_inv_p256(&mut r.0, &self.0);
        r
    }

    /// Montgomery squaring mod p256
    fn mont_sqr(&self) -> Self {
        let mut r = Self::default();
        low::bignum_montsqr_p256(&mut r.0, &self.0);
        r
    }

    /// Addition mod p256
    fn add(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_add_p256(&mut r.0, &self.0, &other.0);
        r
    }

    /// Montgomery multiplication mod p256
    fn mont_mul(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_montmul_p256(&mut r.0, &self.0, &other.0);
        r
    }

    /// `n` Montgomery squarings mod p256
    fn mont_sqr_n(&self, n: usize) -> Self {
        let mut r = *self;
        for _ in 0..n {
            r = r.mont_sqr();
        }
        r
    }

    /// `self` to the `(p + 1) / 4`th power, `2^254 - 2^222 + 2^190 + 2^94`,
    /// in Montgomery form: `x32 = self^(2^32 - 1)`, shifted past one set bit
    /// and then another.
    fn mont_sqrt_candidate(&self) -> Self {
        let x2 = self.mont_sqr_n(1).mont_mul(self);
        let x4 = x2.mont_sqr_n(2).mont_mul(&x2);
        let x8 = x4.mont_sqr_n(4).mont_mul(&x4);
        let x16 = x8.mont_sqr_n(8).mont_mul(&x8);
        let x32 = x16.mont_sqr_n(16).mont_mul(&x16);
        x32.mont_sqr_n(32)
            .mont_mul(self)
            .mont_sqr_n(96)
            .mont_mul(self)
            .mont_sqr_n(94)
    }

    /// Remove one montgomery factor
    fn demont(&self) -> Self {
        let mut r = Self::default();
        low::bignum_demont_p256(&mut r.0, &self.0);
        r
    }

    /// Add a montgomery factor
    fn as_mont(&self) -> Self {
        let mut r = Self::default();
        low::bignum_tomont_p256(&mut r.0, &self.0);
        r
    }

    fn negate_mod_p(&self) -> Self {
        let mut r = Self::default();
        low::bignum_neg_p256(&mut r.0, &self.0);
        r
    }

    /// Public equality
    fn public_eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

#[derive(Default)]
pub(crate) struct Scalar([u64; 4]);

impl Scalar {
    pub(crate) const BYTES: usize = 32;

    /// Create a scalar from the given slice, which can be any size.
    ///
    /// If it is larger than 32 bytes, the leading bytes must be
    /// zero (this is deemed a non-secret property).
    ///
    /// This returns an error if the scalar is zero or larger than
    /// the curve order.
    pub(crate) fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error> {
        let full = Self(
            util::big_endian_slice_any_size_to_u64x4(bytes)
                .ok_or(KeyFormatError::ScalarOutOfRange)?,
        );

        full.into_range_check()
    }

    pub(crate) fn from_bytes_reduced(bytes: &[u8]) -> Result<Self, Error> {
        Ok(
            Self(util::big_endian_slice_any_size_to_u64x4(bytes).ok_or(Error::WrongLength)?)
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
        util::u64x4_to_big_endian(&self.0)
    }

    #[cfg(test)]
    fn small_u64(v: u64) -> Self {
        Self([v, 0, 0, 0])
    }

    /// Private test for zero
    pub(crate) fn is_zero(&self) -> bool {
        self.private_eq(&Self::default())
    }

    /// Private equality
    fn private_eq(&self, other: &Self) -> bool {
        low::bignum_eq(&self.0, &other.0)
    }

    /// Reduce mod n (curve order)
    fn reduce_mod_n(&self) -> Self {
        let mut r = Self::default();
        low::bignum_mod_n256(&mut r.0, &self.0);
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

    /// Return 2^512 mod n, ie MM mod n
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
        let mut temp = [0u64; 4 * 3];
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
    fn bits(&self) -> Bits<'_> {
        Bits {
            scalar: self,
            word: 0,
            bit: 0,
        }
    }

    /// Iterator of `256 / W + 1` W-bit elements, LSB first, sign bit is separate
    #[cfg(rind_backend = "x86_64")]
    fn booth_recoded<const W: usize>(&self) -> BoothRecode<W> {
        BoothRecode::new(self)
    }

    /// The width-`W` non-adjacent form of this scalar, by
    /// [`util::public_naf`].
    fn public_naf<const W: u32>(&self) -> [i8; 257] {
        let mut digits = [0; 257];
        util::public_naf::<W>(&self.0, &mut digits);
        digits
    }
}

#[cfg(test)]
struct Bits<'a> {
    scalar: &'a Scalar,
    word: usize,
    bit: usize,
}

#[cfg(test)]
impl Iterator for Bits<'_> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        if self.word > 3 {
            return None;
        }

        let v = (self.scalar.0[self.word] >> self.bit) & 1;

        self.bit += 1;
        if self.bit == 64 {
            self.word += 1;
            self.bit = 0;
        }

        Some(v as u8)
    }
}

#[cfg(rind_backend = "x86_64")]
struct BoothRecode<const W: usize> {
    // little endian
    bytes: [u8; 33],
    index: usize,
}

#[cfg(rind_backend = "x86_64")]
impl<const W: usize> BoothRecode<W> {
    fn new(scalar: &Scalar) -> Self {
        let mut bytes = [0u8; 33];

        bytes[0..8].copy_from_slice(&scalar.0[0].to_le_bytes());
        bytes[8..16].copy_from_slice(&scalar.0[1].to_le_bytes());
        bytes[16..24].copy_from_slice(&scalar.0[2].to_le_bytes());
        bytes[24..32].copy_from_slice(&scalar.0[3].to_le_bytes());

        Self { bytes, index: 0 }
    }

    fn recode(v: u8) -> (u8, u8) {
        // see the comment above boringssl's `ec_GFp_nistp_recode_scalar_bits` for
        // references
        let sign = !((v >> W).wrapping_sub(1));

        let d = (1u16 << (W + 1)).wrapping_sub(v as u16).wrapping_sub(1) as u8;
        let d = (d & sign) | (v & !sign);
        let d = (d >> 1).wrapping_add(d & 1);

        (d, sign & 1)
    }
}

#[cfg(rind_backend = "x86_64")]
impl<const W: usize> Iterator for BoothRecode<W> {
    type Item = (u8, u8);

    fn next(&mut self) -> Option<Self::Item> {
        let mask = ((1u16 << (W + 1)) - 1) as u8;

        match self.index {
            0 => {
                self.index += W;
                Some(Self::recode((self.bytes[0] << 1) & mask))
            }

            _ if self.index < 256 => {
                let offset = (self.index - 1) / 8;
                let shift = (self.index - 1) % 8;
                let value = (((self.bytes[offset] as u16) | ((self.bytes[offset + 1] as u16) << 8))
                    >> shift) as u8
                    & mask;
                self.index += W;
                Some(Self::recode(value))
            }

            _ => None,
        }
    }
}

/// The generator table's window, aws-lc's.
#[cfg(rind_backend = "x86_64")]
const BASE_WINDOW: usize = 7;

/// 37 rows of the 64 multiples `i * 2^(7 * j) * G`, one row per 7-bit window.
///
/// 37 := 256 / 7 + 1, as Booth recoding carries into a window above the top bit.
#[cfg(rind_backend = "x86_64")]
type AffineMontPointTable = [low::P256GeneratorRow; 37];

/// 43 rows of the 32 multiples `i * 2^(6 * j) * G`, one row per 6-bit window.
///
/// 43 := 256 / 6 + 1, as Booth recoding carries into a window above the top bit.
#[cfg(not(rind_backend = "x86_64"))]
type AffineMontPointTable = [[u64; 256]; 43];

const CURVE_A_MONT: FieldElement = FieldElement([
    0xffff_ffff_ffff_fffc,
    0x0000_0003_ffff_ffff,
    0x0000_0000_0000_0000,
    0xffff_fffc_0000_0004,
]);

const CURVE_B_MONT: FieldElement = FieldElement([
    0xd89c_df62_29c4_bddf,
    0xacf0_05cd_7884_3090,
    0xe5a2_20ab_f721_2ed6,
    0xdc30_061d_0487_4834,
]);

const CURVE_ONE_MONT: FieldElement = FieldElement([
    0x0000_0000_0000_0001,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_ffff,
    0x0000_0000_ffff_fffe,
]);

const CURVE_PRIME: [u64; 4] = [
    0xffff_ffff_ffff_ffff,
    0x0000_0000_ffff_ffff,
    0x0000_0000_0000_0000,
    0xffff_ffff_0000_0001,
];

const CURVE_ORDER: [u64; 4] = [
    0xf3b9_cac2_fc63_2551,
    0xbce6_faad_a717_9e84,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_0000_0000,
];

const CURVE_ORDER_MM: [u64; 4] = [
    0x83244c95be79eea2,
    0x4699799c49bd6fa6,
    0x2845b2392b6bec59,
    0x66e12d94f3d95620,
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

    const CURVE_GENERATOR: AffineMontPoint = AffineMontPoint {
        xy: [
            0x79e7_30d4_18a9_143c,
            0x75ba_95fc_5fed_b601,
            0x79fb_732b_7762_2510,
            0x1890_5f76_a537_55c6,
            0xddf2_5357_ce95_560a,
            0x8b4a_b8e4_ba19_e45c,
            0xd2e8_8688_dd21_f325,
            0x8571_ff18_2588_5d85,
        ],
    };

    #[test]
    fn generator_on_curve() {
        println!("{CURVE_GENERATOR:x?}");
        assert!(CURVE_GENERATOR.on_curve());
        println!("demont {:x?}", CURVE_GENERATOR.as_bytes_uncompressed());
    }

    #[test]
    fn generate_key_1() {
        let scalar = Scalar::small_u64(1);
        let r = CURVE_GENERATOR.slow_multiply(&scalar);
        assert_eq!(
            r.as_bytes_uncompressed(),
            CURVE_GENERATOR.as_bytes_uncompressed()
        );
        println!("raw {r:x?}");
        println!("fmt {:x?}", r.as_bytes_uncompressed());
    }

    #[test]
    fn point_double() {
        let mut p = JacobianMontPoint::from_affine(&CURVE_GENERATOR);
        println!("p = {p:x?}");
        p = p.double();
        println!("p2 = {p:x?}");
        println!("p2 aff = {:x?}", p.as_affine());
        println!("enc = {:x?}", p.as_affine().as_bytes_uncompressed());
    }

    #[test]
    fn generate_key_2() {
        let scalar = Scalar::small_u64(2);
        let r = CURVE_GENERATOR.slow_multiply(&scalar);
        println!("raw {r:x?}");
        println!("fmt {:x?}", r.as_bytes_uncompressed());
    }

    #[test]
    fn multiply_matches_double_and_add() {
        let n_minus = |k: u64| {
            let mut s = CURVE_ORDER;
            s[0] -= k;
            Scalar(s)
        };
        // Every 6-bit window 32, and every 7-bit window 64, so each Booth
        // digit is a full row's last entry, on aarch64 and x86_64.
        let all_32 = Scalar([0x0820_8208_2082_0820; 4]);
        let all_64 = Scalar([
            0x4081_0204_0810_2040,
            0x2040_8102_0408_1020,
            0x1020_4081_0204_0810,
            0x0810_2040_8102_0408,
        ]);
        for scalar in [
            Scalar::small_u64(1),
            Scalar::small_u64(2),
            Scalar::small_u64(3),
            Scalar::small_u64(32),
            Scalar::small_u64(33),
            Scalar::small_u64(99999999),
            Scalar([0, 0, 0, 1 << 63]),
            all_32,
            all_64,
            n_minus(1),
            n_minus(2),
        ] {
            let expected = CURVE_GENERATOR.slow_multiply(&scalar).xy;
            assert_eq!(AffineMontPoint::base_multiply(&scalar).xy, expected);
            let odd_multiples = CURVE_GENERATOR.public_odd_multiples();
            let more = AffineMontPoint::public_more_odd_multiples(&odd_multiples);
            let zero = Scalar::default();
            for more in [None, Some(&more)] {
                for (g, p) in [(&scalar, &zero), (&zero, &scalar)] {
                    assert_eq!(
                        JacobianMontPoint::public_twin_multiply(g, p, &odd_multiples, more)
                            .as_affine()
                            .xy,
                        expected
                    );
                }
            }
            assert_eq!(CURVE_GENERATOR.multiply(&scalar).xy, expected);
        }
    }

    #[cfg(rind_backend = "x86_64")]
    #[test]
    fn booth_recoding_sums_to_scalar() {
        let mut n_minus_1 = CURVE_ORDER;
        n_minus_1[0] -= 1;
        // The third has every 7-bit window 64, the largest digit.
        for words in [
            [0; 4],
            [1, 0, 0, 0],
            [
                0x4081_0204_0810_2040,
                0x2040_8102_0408_1020,
                0x1020_4081_0204_0810,
                0x0810_2040_8102_0408,
            ],
            n_minus_1,
            [u64::MAX; 4],
        ] {
            // Each digit at bit 7i, as a byte's multiple at byte 7i / 8.
            let mut sum = [0i64; 33];
            let mut windows = 0;
            for (i, (digit, sign)) in Scalar(words).booth_recoded::<BASE_WINDOW>().enumerate() {
                let digit = i64::from(digit) * if sign == 1 { -1 } else { 1 };
                sum[7 * i / 8] += digit << (7 * i % 8);
                windows += 1;
            }
            for i in 0..32 {
                sum[i + 1] += sum[i] >> 8;
                sum[i] &= 0xff;
            }
            let bytes: Vec<i64> = words
                .iter()
                .flat_map(|w| w.to_le_bytes())
                .map(i64::from)
                .collect();
            assert_eq!(sum[..32], bytes[..], "{words:x?}");
            assert_eq!(sum[32], 0, "{words:x?}");
            // One window for each row of the generator table.
            assert_eq!(windows, precomp::CURVE_GENERATOR_PRECOMP.len());
        }
    }

    #[test]
    fn twin_multiply_exceptional() {
        // The accumulator meets the point it adds: equal, which must double,
        // or opposite, which must give infinity. With P = G it meets G's
        // multiples, and with P = 2G, P's.
        let odd_multiples = CURVE_GENERATOR.public_odd_multiples();
        let more = AffineMontPoint::public_more_odd_multiples(&odd_multiples);
        let n_minus = |k: u64| {
            let mut s = CURVE_ORDER;
            s[0] -= k;
            Scalar(s)
        };
        for (g, p) in [
            (Scalar::small_u64(1), Scalar::small_u64(1)),
            (Scalar::small_u64(3), Scalar::small_u64(3)),
            (Scalar::small_u64(2), Scalar::small_u64(1)),
            (Scalar::small_u64(1), n_minus(1)),
            (n_minus(5), Scalar::small_u64(5)),
            (n_minus(1), n_minus(1)),
            (Scalar([0, 0, 0, 1 << 63]), Scalar([0, 0, 0, 1 << 63])),
        ] {
            let sum = g.add(&p);
            let expected = CURVE_GENERATOR.slow_multiply(&sum).xy;
            for more in [None, Some(&more)] {
                let result = JacobianMontPoint::public_twin_multiply(&g, &p, &odd_multiples, more);
                assert_eq!(result.as_affine().xy, expected);
                // Verification refuses a sum at infinity by this check.
                assert_eq!(result.public_is_infinity(), sum.0 == [0; 4]);
            }
        }

        let p2 = JacobianMontPoint::from_affine(&CURVE_GENERATOR)
            .double()
            .as_affine();
        let odd_multiples = p2.public_odd_multiples();
        let more = AffineMontPoint::public_more_odd_multiples(&odd_multiples);
        for (g, p) in [
            (Scalar::small_u64(2), Scalar::small_u64(1)),
            (Scalar::small_u64(6), Scalar::small_u64(3)),
        ] {
            let expected = CURVE_GENERATOR.slow_multiply(&g.add(&p).add(&p)).xy;
            for more in [None, Some(&more)] {
                assert_eq!(
                    JacobianMontPoint::public_twin_multiply(&g, &p, &odd_multiples, more)
                        .as_affine()
                        .xy,
                    expected
                );
            }
        }
    }

    #[test]
    fn generate_key_known_answer() {
        let bytes = b"\x1F\x55\x45\x23\x08\x50\x8C\x6B\x24\x37\x0F\x22\x1E\xF1\xB3\xF9\x54\x46\xBE\x4F\x8A\x4B\x42\x8A\x5B\x51\xB7\x10\xC2\x68\x4C\x03";
        let private = PrivateKey::from_bytes(bytes).unwrap();
        println!("priv = {private:x?}");
        let public = private.public_key_uncompressed();
        println!("pub = {public:x?}");
        const EXPECTED: &[u8; 65] = b"\x04\xcb\x8a\x14\x1c\xd7\xe4\x07\xaf\x69\xa5\x01\x88\xe9\x1c\xe5\x5d\xcc\xfd\x33\x48\xda\xba\x4a\x9c\x46\x64\x33\x2e\x95\x59\xb6\x81\x44\xfc\x1a\x61\xd8\x41\xe4\xdb\x80\x1b\x33\x51\x20\x12\x1d\x0b\xa4\x84\xb3\xc9\x53\xb3\x1d\x35\x1d\x7f\xa2\x13\x97\xd1\x25\x47";
        assert_eq!(&public, EXPECTED);
        PublicKey::from_x962_uncompressed(&public).unwrap();
    }

    #[test]
    fn test_raw_ecdsa_sign() {
        let private = StaticPrivateKey::from_bytes(b"\xd1\xf6\xbc\xcc\x3e\x5a\x40\x1b\xcc\x2c\x21\xbe\x34\x90\xed\x38\xde\xf4\x93\x7f\x78\x06\x03\xf5\x2b\x23\xb9\xa6\xfa\x9c\xf6\x0e").unwrap();
        let k = StaticPrivateKey::from_bytes(b"\xe7\x95\x37\xa1\xd7\x55\x45\x1f\x8c\x3c\xbf\xf7\x84\xea\x5c\x1c\xdf\xe1\x6b\x1d\x13\xe7\xbf\xbb\x04\xd7\xfd\x90\x57\xee\xee\xf7").unwrap();
        let e = Scalar::from_bytes_checked(b"\x2c\xf2\x4d\xba\x5f\xb0\xa3\x0e\x26\xe8\x3b\x2a\xc5\xb9\xe2\x9e\x1b\x16\x1e\x5c\x1f\xa7\x42\x5e\x73\x04\x33\x62\x93\x8b\x98\x24").unwrap();
        let r = Scalar::from_bytes_checked(b"\x78\xee\x34\xc8\xb6\x52\x29\x54\x96\x19\x79\x45\x2e\x6e\x0c\xe0\x68\x5d\x40\x42\x38\x41\xef\xeb\x06\xfe\x3e\x3f\xf7\xb6\x5d\xf5").unwrap();
        let s = private.raw_ecdsa_sign(&k, &e, &r);
        assert_eq!(
            format!("{:02x?}", s.as_bytes()),
            "[5b, c9, 8e, 7d, 28, 74, d0, 9d, e8, fb, da, 22, 34, 83, 24, 4f, a1, ba, a2, 6a, 71, 91, 4e, 8e, d4, 8f, 88, b8, 2d, 17, 0b, 4b]"
        );
    }

    #[test]
    fn private_key_in_range() {
        assert_eq!(
            PrivateKey::from_bytes(&[0u8; 32]).unwrap_err(),
            Error::from(KeyFormatError::ScalarOutOfRange)
        );

        // order rejected
        assert_eq!(PrivateKey::from_bytes(b"\xff\xff\xff\xff\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xbc\xe6\xfa\xad\xa7\x17\x9e\x84\xf3\xb9\xca\xc2\xfc\x63\x25\x51").unwrap_err(), Error::from(KeyFormatError::ScalarOutOfRange));

        // order + 1 rejected
        assert_eq!(PrivateKey::from_bytes(b"\xff\xff\xff\xff\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xbc\xe6\xfa\xad\xa7\x17\x9e\x84\xf3\xb9\xca\xc2\xfc\x63\x25\x52").unwrap_err(), Error::from(KeyFormatError::ScalarOutOfRange));

        // order - 1 is ok
        PrivateKey::from_bytes(b"\xff\xff\xff\xff\x00\x00\x00\x00\xff\xff\xff\xff\xff\xff\xff\xff\xbc\xe6\xfa\xad\xa7\x17\x9e\x84\xf3\xb9\xca\xc2\xfc\x63\x25\x50").unwrap();
    }

    #[test]
    fn curve_field_elements_as_mont() {
        const CURVE_A: FieldElement = FieldElement([
            0xffff_ffff_ffff_fffc,
            0x0000_0000_ffff_ffff,
            0x0000_0000_0000_0000,
            0xffff_ffff_0000_0001,
        ]);
        const CURVE_B: FieldElement = FieldElement([
            0x3bce_3c3e_27d2_604b,
            0x651d_06b0_cc53_b0f6,
            0xb3eb_bd55_7698_86bc,
            0x5ac6_35d8_aa3a_93e7,
        ]);

        println!("G.x = {:x?}", CURVE_GENERATOR.x().as_mont());
        println!("G.y = {:x?}", CURVE_GENERATOR.y().as_mont());
        println!("a = {:x?}", CURVE_A.as_mont());
        println!("b = {:x?}", CURVE_B.as_mont());
        let one = FieldElement([1, 0, 0, 0]);
        println!("R = {:x?}", one.as_mont());
        println!("R * R = {:x?}", one.as_mont().as_mont());

        println!("montify n = {:016x?}", Scalar::montifier().0);
    }

    #[test]
    fn base_point_precomp() {
        let mut base = JacobianMontPoint::from_affine(&CURVE_GENERATOR);
        for row in &precomp::CURVE_GENERATOR_PRECOMP {
            let mut multiple = base;
            for (i, entry) in (1..).zip(row.as_chunks::<8>().0) {
                assert_eq!(&multiple.as_affine().xy, entry);
                multiple = match i {
                    1 => multiple.double(),
                    _ => multiple.add(&base),
                };
            }
            // A row of 2^(w - 1) multiples spans a w-bit window.
            let window = row.as_chunks::<8>().0.len().ilog2() + 1;
            base.double_inplace_n(window as usize);
        }
    }
}
