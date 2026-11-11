// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::ops::Range;

use super::hash_to_curve::{self, ExpandError, HashedPoint, SwuConstants, SwuField};
use super::util;
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::{RandomSource, SystemRandom};

mod precomp;

/// A P-384 public key.
#[derive(Clone, Debug)]
pub(crate) struct PublicKey {
    point: AffineMontPoint,
}

impl PublicKey {
    pub(crate) const BYTES: usize = 1 + FieldElement::BYTES + FieldElement::BYTES;

    /// Create an P-384 [`PublicKey`] from a byte slice.
    ///
    /// This must be exactly 97 bytes in length, using the X9.62
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
    /// An error is returned unless `bytes` is 49 bytes with tag 2 or 3, its
    /// `x` is below the field prime, and a point on the curve has that `x`.
    pub(crate) fn decompress<'a>(bytes: &[u8], output: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let _entry = low::Entry::new_public();
        let point = AffineMontPoint::from_x962_compressed(bytes)?;
        let output = output.get_mut(..Self::BYTES).ok_or(Error::WrongLength)?;
        output.copy_from_slice(&point.as_bytes_uncompressed());
        Ok(output)
    }
}

/// A P-384 public key for ECDSA verification.
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
        let point = match more {
            Some(more) => {
                JacobianMontPoint::public_twin_multiply(&u1, &u2, &[&odd_multiples, more])
            }
            None => JacobianMontPoint::public_twin_multiply(&u1, &u2, &[&odd_multiples]),
        };

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

/// A P-384 private key.
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
        let result = JacobianMontPoint::multiply(&self.scalar, &peer.point).as_affine();
        match low::ct::into_public(result.on_curve()) {
            true => Ok(SharedSecret(util::u64x6_to_big_endian(
                &result.x().demont().0,
            ))),
            false => Err(Error::Fault),
        }
    }

    fn public_point(&self) -> AffineMontPoint {
        let point = JacobianMontPoint::base_multiply(&self.scalar).as_affine();
        let point = low::ct::into_public(point);
        match point.on_curve() {
            true => point,
            false => panic!("internal fault"),
        }
    }

    fn generate(rng: &mut dyn RandomSource) -> Result<Self, Error> {
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

/// A P-384 static private key.
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

/// A shared secret output from a P-384 Diffie-Hellman operation.
///
/// It is not wiped on drop: `agreement::SharedSecret` wipes it.
pub(crate) struct SharedSecret(pub(crate) [u8; FieldElement::BYTES]);

#[derive(Clone, Copy, Debug, Default)]
struct AffineMontPoint {
    xy: [u64; 12],
}

impl AffineMontPoint {
    const X: Range<usize> = 0..6;
    const Y: Range<usize> = 6..12;

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

        let x = util::big_endian_slice_to_u64x6(x).unwrap();
        let y = util::big_endian_slice_to_u64x6(y).unwrap();

        // A coordinate at or above p would be reduced, giving the point a
        // second encoding.  Public, so this need not be constant time.
        let below_p = |v: &[u64; 6]| v.iter().rev().lt(CURVE_PRIME.iter().rev());
        if !below_p(&x) || !below_p(&y) {
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
        let x = util::big_endian_slice_to_u64x6(x).ok_or(KeyFormatError::WrongLength)?;
        if !x.iter().rev().lt(CURVE_PRIME.iter().rev()) {
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
        Scalar::from_bytes_reduced(&bytes[1..1 + FieldElement::BYTES]).unwrap()
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
        x.copy_from_slice(&util::u64x6_to_big_endian(&self.x().demont().0));
        y.copy_from_slice(&util::u64x6_to_big_endian(&self.y().demont().0));
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

    /// Returns table[i - 1] if index > 0, or else the affine point at infinity
    fn lookup_comb(table: &[u64; 192], index: u8) -> Self {
        let mut r = Self::default();
        low::bignum_aff_point_select_p384(&mut r.xy, table, index);
        r
    }

    /// Returns table[i - 1] for a public index > 0
    fn public_lookup_comb(table: &[u64; 192], index: u8) -> Self {
        let offs = (index - 1) as usize * 12;
        let mut r = Self::default();
        r.xy.copy_from_slice(&table[offs..offs + 12]);
        r
    }

    fn negate_y(&mut self) {
        let neg_y = self.y().negate_mod_p();
        self.xy[Self::Y].copy_from_slice(&neg_y.0);
    }

    fn maybe_negate_y(&mut self, sign: u8) {
        let y = self.y();
        let neg_y = y.negate_mod_p();
        let result = FieldElement::select(&y, &neg_y, sign);
        self.xy[Self::Y].copy_from_slice(&result.0);
    }

    /// P, 3P, ..., 15P: the odd multiples a width-5 NAF digit picks, in
    /// affine form so that each is added by `p384_montjmixadd`.
    ///
    /// Each sum adds 2P to an odd multiple below n, never equal, as
    /// `p384_montjadd` requires, and none is at infinity.
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
    /// as `p384_montjmixadd` requires, and none is at infinity.
    fn public_more_odd_multiples(odd_multiples: &[Self; 8]) -> [Self; 8] {
        let p16 = JacobianMontPoint::from_affine(&odd_multiples[7]).add_affine(&odd_multiples[0]);
        let multiples = odd_multiples.map(|multiple| p16.add_affine(&multiple));
        JacobianMontPoint::public_batch_as_affine(&multiples)
    }

    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    fn public_precomp_w5(&self) -> JacobianMontPointTableW5 {
        let mut r = [JacobianMontPoint::zero(); 16];

        // indices into r are intuitively 1-based; index i contains i * G,
        // and 0 * G is not useful to store.
        macro_rules! index {
            ($i:literal) => {
                $i - 1
            };
        }

        // Each sum adds distinct multiples below n, none at infinity, as
        // `p384_montjadd` requires.
        r[index!(1)] = JacobianMontPoint::from_affine(self);
        r[index!(2)] = r[index!(1)].double();
        r[index!(3)] = r[index!(1)].add(&r[index!(2)]);
        r[index!(4)] = r[index!(2)].double();
        r[index!(5)] = r[index!(1)].add(&r[index!(4)]);
        r[index!(6)] = r[index!(3)].double();
        r[index!(7)] = r[index!(1)].add(&r[index!(6)]);
        r[index!(8)] = r[index!(4)].double();
        r[index!(9)] = r[index!(1)].add(&r[index!(8)]);
        r[index!(10)] = r[index!(5)].double();
        r[index!(11)] = r[index!(1)].add(&r[index!(10)]);
        r[index!(12)] = r[index!(6)].double();
        r[index!(13)] = r[index!(1)].add(&r[index!(12)]);
        r[index!(14)] = r[index!(7)].double();
        r[index!(15)] = r[index!(1)].add(&r[index!(14)]);
        r[index!(16)] = r[index!(8)].double();

        let mut t = [0; 288];

        let (chunks, _) = t.as_chunks_mut::<18>();
        for (out, rr) in chunks.iter_mut().zip(r) {
            out.copy_from_slice(&rr.xyz);
        }

        t
    }
}

#[derive(Clone, Copy, Debug)]
struct JacobianMontPoint {
    xyz: [u64; 18],
}

impl JacobianMontPoint {
    const X: Range<usize> = 0..6;
    const Y: Range<usize> = 6..12;
    const XY: Range<usize> = 0..12;
    const Z: Range<usize> = 12..18;

    fn infinity() -> Self {
        Self {
            xyz: [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        }
    }

    fn public_is_infinity(&self) -> bool {
        self.z().public_eq(&FieldElement::default())
    }

    fn zero() -> Self {
        Self { xyz: [0; 18] }
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
    /// Window `w` of the 77 Booth-recoded 5-bit windows is `4j + t` for
    /// one tooth `t` in 0..4, and table `j` holds its multiples of
    /// `2^(20j) G`.  So each tooth's windows are added straight from the
    /// tables, and the 5 doublings between teeth supply the `2^(5t)`: 15
    /// doublings in all, rather than 380.
    ///
    /// No addition doubles, which `p384_montjmixadd` cannot.  Scaled by
    /// `2^(-5t)`, the accumulator and the table point are sums of digits of
    /// distinct windows, so they are unequal integers unless both are zero
    /// (infinity, which the addition handles).  Until window 76, which is
    /// added last, each is below `2^380`, so they are unequal mod n too.  At
    /// window 76, equal points would need the accumulator to be
    /// `16 * 2^380 - n`, making `scalar` `2^385 - n`, which is above n.
    fn base_multiply(scalar: &Scalar) -> Self {
        let mut windows = [(0u8, 0u8); 77];
        for ((digit, sign, _), window) in scalar
            .reversed_booth_recoded_w5()
            .zip(windows.iter_mut().rev())
        {
            *window = (digit, sign);
        }

        let mut result = Self::infinity();
        for tooth in (0..4).rev() {
            if tooth != 3 {
                result.double_inplace_n(5);
            }

            for (table, &(digit, sign)) in precomp::CURVE_GENERATOR_PRECOMP_COMB
                .iter()
                .zip(windows.iter().skip(tooth).step_by(4))
            {
                let mut tmp = AffineMontPoint::lookup_comb(table, digit);
                tmp.maybe_negate_y(sign);
                result.add_inplace_affine(&tmp, digit);
            }
        }

        result
    }

    /// `scalar * point`, by s2n-bignum's `p384_montjscalarmul`.
    #[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
    fn multiply(scalar: &Scalar, point: &AffineMontPoint) -> Self {
        let mut r = Self::zero();
        low::p384_montjscalarmul(&mut r.xyz, &scalar.0, &Self::from_affine(point).xyz);
        r
    }

    /// `scalar * point`, by Booth-recoded 5-bit windows over the point's
    /// multiples.
    ///
    /// No addition doubles, which `p384_montjadd` cannot.  Before each, the
    /// accumulator is 32m P and the table point d P, for the nonnegative
    /// value m of the windows above and a digit d of at most 16.  So they
    /// are equal only if 32m - d is zero, when both are at infinity, or n,
    /// when the windows so far are worth 32m + d = n + 2d.  Below n, that
    /// needs the last window, a negative d, and n = -d mod 32, which the
    /// assertion below rules out.
    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    fn multiply(scalar: &Scalar, point: &AffineMontPoint) -> Self {
        const { assert!(CURVE_ORDER[0] % 32 > 16) };
        let precomp = point.public_precomp_w5();
        let mut terms = scalar.reversed_booth_recoded_w5();

        let (digit, _, _) = terms.next().unwrap();
        let mut result = Self::lookup_w5(&precomp, digit, 0);
        result.double_inplace_n(5);

        for (digit, sign, last) in terms {
            result.add_inplace(&Self::lookup_w5(&precomp, digit, sign));

            if !last {
                result.double_inplace_n(5);
            }
        }

        result
    }

    /// `g * G + p * P` for public scalars, given P's odd multiples in rows
    /// of 8.
    ///
    /// One chain of doublings serves both: P's digits are a NAF over
    /// `odd_multiples`, width 5 for one row and 6 for two, and G's a width-5
    /// NAF over the first comb table, which holds G to 16G.
    fn public_twin_multiply(
        g: &Scalar,
        p: &Scalar,
        odd_multiples: &[&[AffineMontPoint; 8]],
    ) -> Self {
        let (mut g_digits, mut p_digits) = ([0; 385], [0; 385]);
        util::public_naf::<5>(&g.0, &mut g_digits);
        match odd_multiples.len() {
            1 => util::public_naf::<5>(&p.0, &mut p_digits),
            _ => util::public_naf::<6>(&p.0, &mut p_digits),
        }
        let g_multiples = &precomp::CURVE_GENERATOR_PRECOMP_COMB[0];

        let mut result = Self::infinity();
        for (g_digit, p_digit) in g_digits.iter().zip(&p_digits).rev() {
            if !result.public_is_infinity() {
                result = result.double();
            }
            if *p_digit != 0 {
                let i = usize::from(p_digit.unsigned_abs() / 2);
                let mut tmp = odd_multiples[i / 8][i % 8];
                if *p_digit < 0 {
                    tmp.negate_y();
                }
                result = result.public_add_affine(&tmp);
            }
            if *g_digit != 0 {
                let mut tmp =
                    AffineMontPoint::public_lookup_comb(g_multiples, g_digit.unsigned_abs());
                if *g_digit < 0 {
                    tmp.negate_y();
                }
                result = result.public_add_affine(&tmp);
            }
        }
        result
    }

    fn from_affine(p: &AffineMontPoint) -> Self {
        let mut xyz: [u64; 18] = Default::default();
        xyz[Self::XY].copy_from_slice(&p.xy);
        xyz[Self::Z].copy_from_slice(&CURVE_ONE_MONT.0);
        Self { xyz }
    }

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
        let mut inv = prefix[7].mont_mul(&points[7].z()).demont().inv().as_mont();

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
    /// `p384_montjmixadd` is proven only for unequal points, so points with
    /// the same x never reach it.
    fn public_add_affine(&self, p: &AffineMontPoint) -> Self {
        if self.public_is_infinity() {
            return Self::from_affine(p);
        }

        // `p` scaled to this point's z.
        let z2 = self.z().mont_sqr();
        if !p.x().mont_mul(&z2).public_eq(&self.x()) {
            return self.add_affine(p);
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
        let is = |x: [u64; 6]| FieldElement(x).as_mont().mont_mul(&z2).public_eq(&self.x());
        if is(r.0) {
            return true;
        }
        let mut r_plus_n = [0; 6];
        let mut carry = false;
        for (sum, (r, n)) in r_plus_n.iter_mut().zip(r.0.iter().zip(CURVE_ORDER)) {
            let (s, c1) = r.overflowing_add(n);
            let (s, c2) = s.overflowing_add(u64::from(carry));
            *sum = s;
            carry = c1 | c2;
        }
        !carry && r_plus_n.iter().rev().lt(CURVE_PRIME.iter().rev()) && is(r_plus_n)
    }

    #[must_use]
    fn double(&self) -> Self {
        let mut tmp = Self::zero();
        low::p384_montjdouble(&mut tmp.xyz, &self.xyz);
        tmp
    }

    fn double_inplace_n(&mut self, n: usize) {
        for _ in 0..n {
            let tmp = *self;
            low::p384_montjdouble(&mut self.xyz, &tmp.xyz);
        }
    }

    #[cfg(any(any(rind_backend = "arm", rind_backend = "portable"), test))]
    fn add_inplace(&mut self, p: &Self) {
        let mut r = Self::infinity();
        low::p384_montjadd(&mut r.xyz, &self.xyz, &p.xyz);
        *self = r;
    }

    /// Adds `p`, a table entry for `digit`, which is the affine point at
    /// infinity when `digit` is zero.
    fn add_inplace_affine(&mut self, p: &AffineMontPoint, digit: u8) {
        let mut r = Self::infinity();
        low::p384_montjmixadd(&mut r.xyz, &self.xyz, &p.xy);
        // `p384_montjmixadd` cannot take an affine point at infinity.
        *self = Self::select(self, &r, digit);
    }

    #[must_use]
    fn add_affine(&self, p: &AffineMontPoint) -> Self {
        let mut r = Self::infinity();
        low::p384_montjmixadd(&mut r.xyz, &self.xyz, &p.xy);
        r
    }

    #[must_use]
    fn add(&self, p: &Self) -> Self {
        let mut r = Self::infinity();
        low::p384_montjadd(&mut r.xyz, &self.xyz, &p.xyz);
        r
    }

    /// Return p0 if select == 0, p1 otherwise
    #[must_use]
    fn select(p0: &Self, p1: &Self, select: u8) -> Self {
        let mut r = Self::zero();
        let select = select as u64;
        low::bignum_mux(select, &mut r.xyz[..], &p1.xyz[..], &p0.xyz[..]);
        r
    }

    /// Returns `table[index - 1]`, negated if `sign` is set, or infinity
    /// for a zero `index`, in constant time.
    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    fn lookup_w5(table: &JacobianMontPointTableW5, index: u8, sign: u8) -> Self {
        let mut r = Self::infinity();
        low::bignum_jac_point_select_p384(&mut r.xyz, table, index);
        r.maybe_negate_y(sign);
        r
    }

    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    fn maybe_negate_y(&mut self, sign: u8) {
        let y = self.y();
        let neg_y = y.negate_mod_p();
        let result = FieldElement::select(&y, &neg_y, sign);
        self.xyz[Self::Y].copy_from_slice(&result.0);
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct FieldElement([u64; 6]);

impl FieldElement {
    const BYTES: usize = 48;

    fn inv(&self) -> Self {
        let mut r = Self::default();
        low::bignum_inv_p384(&mut r.0, &self.0);
        r
    }

    /// Montgomery squaring mod p384
    fn mont_sqr(&self) -> Self {
        let mut r = Self::default();
        low::bignum_montsqr_p384(&mut r.0, &self.0);
        r
    }

    /// Addition mod p384
    fn add(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_add_p384(&mut r.0, &self.0, &other.0);
        r
    }

    /// Montgomery multiplication mod p384
    fn mont_mul(&self, other: &Self) -> Self {
        let mut r = Self::default();
        low::bignum_montmul_p384(&mut r.0, &self.0, &other.0);
        r
    }

    /// `n` Montgomery squarings mod p384
    fn mont_sqr_n(&self, n: usize) -> Self {
        let mut r = *self;
        for _ in 0..n {
            r = r.mont_sqr();
        }
        r
    }

    /// `self` to the `(p + 1) / 4`th power, in Montgomery form. That is
    /// `(2^255 - 1) * 2^127 + (2^32 - 1) * 2^94 + 2^30`: 255 set bits, a clear
    /// one, 32 set, 63 clear, one set, and 30 clear, so `xN = self^(2^N - 1)`
    /// builds `x255` and `x32`.
    fn mont_sqrt_candidate(&self) -> Self {
        let x2 = self.mont_sqr_n(1).mont_mul(self);
        let x3 = x2.mont_sqr_n(1).mont_mul(self);
        let x6 = x3.mont_sqr_n(3).mont_mul(&x3);
        let x12 = x6.mont_sqr_n(6).mont_mul(&x6);
        let x15 = x12.mont_sqr_n(3).mont_mul(&x3);
        let x30 = x15.mont_sqr_n(15).mont_mul(&x15);
        let x32 = x30.mont_sqr_n(2).mont_mul(&x2);
        let x60 = x30.mont_sqr_n(30).mont_mul(&x30);
        let x120 = x60.mont_sqr_n(60).mont_mul(&x60);
        let x240 = x120.mont_sqr_n(120).mont_mul(&x120);
        let x255 = x240.mont_sqr_n(15).mont_mul(&x15);
        x255.mont_sqr_n(33)
            .mont_mul(&x32)
            .mont_sqr_n(64)
            .mont_mul(self)
            .mont_sqr_n(30)
    }

    /// Remove one montgomery factor
    fn demont(&self) -> Self {
        let mut r = Self::default();
        low::bignum_demont_p384(&mut r.0, &self.0);
        r
    }

    /// Add a montgomery factor
    fn as_mont(&self) -> Self {
        let mut r = Self::default();
        low::bignum_tomont_p384(&mut r.0, &self.0);
        r
    }

    fn negate_mod_p(&self) -> Self {
        let mut r = Self::default();
        low::bignum_neg_p384(&mut r.0, &self.0);
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
pub(crate) struct Scalar([u64; 6]);

impl Scalar {
    pub(crate) const BYTES: usize = 48;

    /// Create a scalar from the given slice, which can be any size.
    ///
    /// If it is larger than 48 bytes, the leading bytes must be
    /// zero (this is deemed a non-secret property).
    ///
    /// This returns an error if the scalar is zero or larger than
    /// the curve order.
    pub(crate) fn from_bytes_checked(bytes: &[u8]) -> Result<Self, Error> {
        let full = Self(
            util::big_endian_slice_any_size_to_u64x6(bytes)
                .ok_or(KeyFormatError::ScalarOutOfRange)?,
        );

        full.into_range_check()
    }

    pub(crate) fn from_bytes_reduced(bytes: &[u8]) -> Result<Self, Error> {
        Ok(
            Self(util::big_endian_slice_any_size_to_u64x6(bytes).ok_or(Error::WrongLength)?)
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
        util::u64x6_to_big_endian(&self.0)
    }

    #[cfg(test)]
    fn small_u64(v: u64) -> Self {
        Self([v, 0, 0, 0, 0, 0])
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
        low::bignum_mod_n384(&mut r.0, &self.0);
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

    /// Return 2^768 mod n, ie MM mod n
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
        let mut temp = [0u64; 6 * 3];
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

    /// Iterator of 76 * 5-bit elements, LSB first, sign bit and final flag is separate
    fn reversed_booth_recoded_w5(&self) -> BoothRecodeW5 {
        BoothRecodeW5::new(self)
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
        if self.word > 5 {
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

struct BoothRecodeW5 {
    // little endian
    bytes: [u8; 49],
    index: usize,
}

impl BoothRecodeW5 {
    fn new(scalar: &Scalar) -> Self {
        let mut bytes = [0u8; 49];

        bytes[0..8].copy_from_slice(&scalar.0[0].to_le_bytes());
        bytes[8..16].copy_from_slice(&scalar.0[1].to_le_bytes());
        bytes[16..24].copy_from_slice(&scalar.0[2].to_le_bytes());
        bytes[24..32].copy_from_slice(&scalar.0[3].to_le_bytes());
        bytes[32..40].copy_from_slice(&scalar.0[4].to_le_bytes());
        bytes[40..48].copy_from_slice(&scalar.0[5].to_le_bytes());

        Self { bytes, index: 380 }
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
            5..=380 => {
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

/// 16 jacobian points
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
type JacobianMontPointTableW5 = [u64; 288];

/// 20 tables of 16 affine points
type AffineMontPointTableComb = [[u64; 192]; 20];

const CURVE_A_MONT: FieldElement = FieldElement([
    0x0000_0003_ffff_fffc,
    0xffff_fffc_0000_0000,
    0xffff_ffff_ffff_fffb,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
]);

const CURVE_B_MONT: FieldElement = FieldElement([
    0x0811_8871_9d41_2dcc,
    0xf729_add8_7a4c_32ec,
    0x77f2_209b_1920_022e,
    0xe337_4bee_9493_8ae2,
    0xb62b_21f4_1f02_2094,
    0xcd08_114b_604f_bff9,
]);

const CURVE_ONE_MONT: FieldElement = FieldElement([
    0xffff_ffff_0000_0001,
    0x0000_0000_ffff_ffff,
    0x0000_0000_0000_0001,
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0000,
]);

const CURVE_PRIME: [u64; 6] = [
    0x0000_0000_ffff_ffff,
    0xffff_ffff_0000_0000,
    0xffff_ffff_ffff_fffe,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

const CURVE_ORDER: [u64; 6] = [
    0xecec_196a_ccc5_2973,
    0x581a_0db2_48b0_a77a,
    0xc763_4d81_f437_2ddf,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
];

const CURVE_ORDER_MM: [u64; 6] = [
    0x2d31_9b24_19b4_09a9,
    0xff3d_81e5_df1a_a419,
    0xbc3e_483a_fcb8_2947,
    0xd40d_4917_4aab_1cc5,
    0x3fb0_5b7a_2826_6895,
    0x0c84_ee01_2b39_bf21,
];

/// `2^768 mod p`, the Montgomery factor for reducing a hash-to-field integer.
const FIELD_R2: [u64; 6] = [
    0xffff_fffe_0000_0001,
    0x0000_0002_0000_0000,
    0xffff_fffe_0000_0000,
    0x0000_0002_0000_0000,
    0x0000_0000_0000_0001,
    0x0000_0000_0000_0000,
];

/// `(p - 3) / 4`, the public exponent of `sqrt_ratio_3mod4`.
const HASH_C1: [u64; 6] = [
    0x0000_0000_3fff_ffff,
    0xbfff_ffff_c000_0000,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x3fff_ffff_ffff_ffff,
];

/// The byte length `L` of `P384_XMD:SHA-384_SSWU_RO_` (RFC 9380, section 8.3).
const HASH_L: usize = 72;

impl SwuField for FieldElement {
    const C1: &'static [u64] = &HASH_C1;

    fn zero() -> Self {
        Self::default()
    }

    fn one() -> Self {
        CURVE_ONE_MONT
    }

    fn field_add(self, rhs: Self) -> Self {
        Self::add(&self, &rhs)
    }

    fn field_sub(self, rhs: Self) -> Self {
        self.field_add(rhs.neg())
    }

    fn field_mul(self, rhs: Self) -> Self {
        self.mont_mul(&rhs)
    }

    fn field_sqr(self) -> Self {
        self.mont_sqr()
    }

    fn neg(self) -> Self {
        self.negate_mod_p()
    }

    fn inv0(self) -> Self {
        self.demont().inv().as_mont()
    }

    fn cmov(a: Self, b: Self, flag: u64) -> Self {
        let mut out = Self::default();
        low::bignum_mux(flag, &mut out.0, &b.0, &a.0);
        out
    }

    fn ct_eq(self, rhs: Self) -> u64 {
        u64::from(low::bignum_eq(&self.0, &rhs.0))
    }

    fn sgn0(self) -> u64 {
        self.demont().0[0] & 1
    }
}

impl FieldElement {
    #[cfg(test)]
    fn from_small(v: u64) -> Self {
        let mut w = Self::default();
        w.0[0] = v;
        w.as_mont()
    }

    /// Big-endian `bytes` reduced mod p, in Montgomery form.
    fn from_be_reduced(bytes: &[u8]) -> Self {
        Self(hash_to_curve::reduce_be(bytes, &CURVE_PRIME, &FIELD_R2)).as_mont()
    }

    fn to_be_bytes(self) -> [u8; Self::BYTES] {
        util::u64x6_to_big_endian(&self.demont().0)
    }
}

/// Z = -12, in Montgomery form, and `sqrt(-Z) = (-Z)^((p + 1) / 4)`.
///
/// The test `hash_addition_matches_base_point_multiples` checks these limbs
/// against that exponentiation.
const SWU: SwuConstants<FieldElement> = SwuConstants {
    a: CURVE_A_MONT,
    b: CURVE_B_MONT,
    z: FieldElement([
        0x0000_000c_ffff_fff3,
        0xffff_fff3_0000_0000,
        0xffff_ffff_ffff_fff2,
        0xffff_ffff_ffff_ffff,
        0xffff_ffff_ffff_ffff,
        0xffff_ffff_ffff_ffff,
    ]),
    sqrt_neg_z: FieldElement([
        0x1cdf_6f1c_c0a3_f1f8,
        0xfdf2_313b_4c08_f647,
        0x89cb_6776_d418_3d32,
        0xacb3_a761_476b_11b6,
        0xe428_a383_c093_fcea,
        0xd78f_a36b_3ae4_0b98,
    ]),
};

fn swu_constants() -> SwuConstants<FieldElement> {
    SWU
}

fn scalar_from_hash(bytes: &[u8]) -> Scalar {
    Scalar(hash_to_curve::reduce_be(
        bytes,
        &CURVE_ORDER,
        &CURVE_ORDER_MM,
    ))
}

fn point_from_affine(point: hash_to_curve::Affine<FieldElement>) -> HashedPoint<48> {
    HashedPoint {
        x: point.x.to_be_bytes(),
        y: point.y.to_be_bytes(),
        infinity: (point.infinity & 1) as u8,
    }
}

/// Hash `msg` to a P-384 point, suite `P384_XMD:SHA-384_SSWU_RO_`.
///
/// `dst` is the domain separation tag. The cofactor is 1, so clearing it
/// does nothing. See [`HashedPoint`] for the infinity flag.
// Used by the OPRF quest, which is not in the crate yet.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn hash_to_curve(msg: &[u8], dst: &[u8]) -> Result<HashedPoint<48>, ExpandError> {
    let _entry = low::Entry::new_secret();
    let (u0, u1) = hash_to_curve::expand_two::<HASH_L>(msg, dst, hash_to_curve::expand_sha384)?;
    Ok(point_from_affine(hash_to_curve::hash_to_curve_ro(
        FieldElement::from_be_reduced(&u0),
        FieldElement::from_be_reduced(&u1),
        &swu_constants(),
    )))
}

/// Hash `msg` to one P-384 field element, big-endian.
///
/// This is `hash_to_field` with count 1, `L` = 72, and SHA-384.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn hash_to_field(
    msg: &[u8],
    dst: &[u8],
) -> Result<[u8; FieldElement::BYTES], ExpandError> {
    let _entry = low::Entry::new_secret();
    let element = hash_to_curve::expand_reduced::<_, HASH_L>(
        msg,
        dst,
        hash_to_curve::expand_sha384,
        FieldElement::from_be_reduced,
    )?;
    Ok(element.to_be_bytes())
}

/// Hash `msg` to a P-384 scalar.
///
/// `hash_to_field` over the group order, with the suite's `L` and SHA-384.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn hash_to_scalar(msg: &[u8], dst: &[u8]) -> Result<Scalar, ExpandError> {
    let _entry = low::Entry::new_secret();
    hash_to_curve::expand_reduced::<_, HASH_L>(
        msg,
        dst,
        hash_to_curve::expand_sha384,
        scalar_from_hash,
    )
}

/// The simplified SWU image of a field element, for the suite's test vectors.
#[cfg(test)]
pub(super) fn map_field_element(
    be: &[u8],
) -> ([u8; FieldElement::BYTES], [u8; FieldElement::BYTES]) {
    let point = hash_to_curve::map_to_curve(FieldElement::from_be_reduced(be), &swu_constants());
    (point.x.to_be_bytes(), point.y.to_be_bytes())
}

/// The two `hash_to_field` elements `hash_to_curve` adds, big-endian.
#[cfg(test)]
pub(super) fn hash_elements(
    msg: &[u8],
    dst: &[u8],
) -> ([u8; FieldElement::BYTES], [u8; FieldElement::BYTES]) {
    let mut uniform = [0u8; HASH_L * 2];
    hash_to_curve::expand_sha384(msg, dst, &mut uniform).unwrap();
    let (u0, u1) = uniform.split_at(HASH_L);
    (
        FieldElement::from_be_reduced(u0).to_be_bytes(),
        FieldElement::from_be_reduced(u1).to_be_bytes(),
    )
}

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

    #[test]
    fn hash_addition_matches_base_point_multiples() {
        let g = CURVE_GENERATOR;
        let twice = JacobianMontPoint::from_affine(&g).double().as_affine();
        let thrice = JacobianMontPoint::from_affine(&twice)
            .add(&JacobianMontPoint::from_affine(&g))
            .as_affine();
        let affine = |point: AffineMontPoint| hash_to_curve::Affine {
            x: point.x(),
            y: point.y(),
            infinity: 0,
        };
        let doubled = hash_to_curve::add_affine(affine(g), affine(g), CURVE_A_MONT);
        assert_eq!(doubled.infinity, 0);
        assert_eq!(doubled.x.0, twice.x().0);
        assert_eq!(doubled.y.0, twice.y().0);
        let chord = hash_to_curve::add_affine(affine(g), affine(twice), CURVE_A_MONT);
        assert_eq!(chord.x.0, thrice.x().0);
        assert_eq!(chord.y.0, thrice.y().0);
        let opposite = hash_to_curve::add_affine(
            affine(g),
            hash_to_curve::Affine {
                x: g.x(),
                y: g.y().negate_mod_p(),
                infinity: 0,
            },
            CURVE_A_MONT,
        );
        assert_eq!(opposite.infinity, 1);
        assert_eq!(opposite.x.0, [0; 6]);

        let constants = swu_constants();
        let z = FieldElement::from_small(12).neg();
        let neg_z = z.neg();
        assert_eq!(constants.z.0, z.0);
        assert_eq!(constants.sqrt_neg_z.0, neg_z.pow_c1().field_mul(neg_z).0);
        assert_eq!(
            constants.sqrt_neg_z.field_mul(constants.sqrt_neg_z).0,
            constants.z.neg().0
        );
        assert!(scalar_from_hash(&Scalar(CURVE_ORDER).as_bytes()).is_zero());
    }

    const CURVE_GENERATOR: AffineMontPoint = AffineMontPoint {
        xy: [
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
    fn generate_key_3() {
        let scalar = Scalar::small_u64(3);
        let r = JacobianMontPoint::base_multiply(&scalar).as_affine();
        println!("raw {r:x?}");
        println!("fmt {:x?}", r.as_bytes_uncompressed());

        let u = CURVE_GENERATOR.slow_multiply(&scalar);
        println!("raw {u:x?}");
        println!("fmt {:x?}", u.as_bytes_uncompressed());
    }

    #[test]
    fn generate_key_99999999() {
        let scalar = Scalar::small_u64(99999999);
        let r = JacobianMontPoint::base_multiply(&scalar).as_affine();
        println!("raw {r:x?}");
        println!("fmt {:x?}", r.as_bytes_uncompressed());

        let u = CURVE_GENERATOR.slow_multiply(&scalar);
        println!("raw {u:x?}");
        println!("fmt {:x?}", u.as_bytes_uncompressed());
    }

    #[test]
    fn multiply_matches_double_and_add() {
        let n_minus = |k: u64| {
            let mut s = CURVE_ORDER;
            s[0] -= k;
            Scalar(s)
        };
        let point = CURVE_GENERATOR.slow_multiply(&Scalar::small_u64(5));
        let odd_multiples = point.public_odd_multiples();
        let more = AffineMontPoint::public_more_odd_multiples(&odd_multiples);
        for scalar in [
            Scalar::small_u64(1),
            Scalar::small_u64(2),
            Scalar::small_u64(16),
            Scalar::small_u64(17),
            Scalar::small_u64(33),
            Scalar::small_u64(99999999),
            Scalar([0, 0, 0, 0, 0, 1 << 63]),
            n_minus(1),
            n_minus(2),
        ] {
            let expected = point.slow_multiply(&scalar).xy;
            assert_eq!(
                JacobianMontPoint::multiply(&scalar, &point).as_affine().xy,
                expected
            );
            let zero = Scalar::default();
            for rows in [&[&odd_multiples][..], &[&odd_multiples, &more]] {
                assert_eq!(
                    JacobianMontPoint::public_twin_multiply(&zero, &scalar, rows)
                        .as_affine()
                        .xy,
                    expected
                );
                assert_eq!(
                    JacobianMontPoint::public_twin_multiply(&scalar, &zero, rows)
                        .as_affine()
                        .xy,
                    CURVE_GENERATOR.slow_multiply(&scalar).xy
                );
            }
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
        ] {
            let sum = g.add(&p);
            let expected = CURVE_GENERATOR.slow_multiply(&sum).xy;
            for rows in [&[&odd_multiples][..], &[&odd_multiples, &more]] {
                let result = JacobianMontPoint::public_twin_multiply(&g, &p, rows);
                assert_eq!(result.as_affine().xy, expected);
                // Verification refuses a sum at infinity by this check.
                assert_eq!(result.public_is_infinity(), sum.0 == [0; 6]);
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
            for rows in [&[&odd_multiples][..], &[&odd_multiples, &more]] {
                assert_eq!(
                    JacobianMontPoint::public_twin_multiply(&g, &p, rows)
                        .as_affine()
                        .xy,
                    expected
                );
            }
        }
    }

    #[test]
    fn generate_key_known_answer() {
        let bytes = b"\x76\x6e\x61\x42\x5b\x2d\xa9\xf8\x46\xc0\x9f\xc3\x56\x4b\x93\xa6\xf8\x60\x3b\x73\x92\xc7\x85\x16\x5b\xf2\x0d\xa9\x48\xc4\x9f\xd1\xfb\x1d\xee\x4e\xdd\x64\x35\x6b\x9f\x21\xc5\x88\xb7\x5d\xfd\x81";
        let private = PrivateKey::from_bytes(bytes).unwrap();
        println!("priv = {private:x?}");
        let public = private.public_key_uncompressed();
        println!("pub = {public:x?}");
        const EXPECTED: &[u8; 97] = &[
            0x04, 0x7a, 0x6e, 0xc8, 0xd3, 0x11, 0xd5, 0xca, 0x58, 0x8b, 0xae, 0xd4, 0x1b, 0xe3,
            0xe9, 0x8f, 0x30, 0xc9, 0x29, 0x48, 0x44, 0xec, 0xbb, 0x62, 0x99, 0x95, 0x65, 0x36,
            0x35, 0xdb, 0xc2, 0x2d, 0xa2, 0xf0, 0x83, 0xf2, 0x97, 0x11, 0xe0, 0xf9, 0xc5, 0x96,
            0x3b, 0xc0, 0x21, 0xbd, 0x8c, 0xb2, 0x10, 0x9d, 0xaf, 0x56, 0xa5, 0x5f, 0x88, 0x3a,
            0x72, 0x00, 0xce, 0xa9, 0xc4, 0xde, 0x44, 0x48, 0x8e, 0x6d, 0xc4, 0x9f, 0xb9, 0xc3,
            0x94, 0xf5, 0x1c, 0xb5, 0xa4, 0x9f, 0xc6, 0x9d, 0x7e, 0x8a, 0x03, 0x47, 0x92, 0x96,
            0x3a, 0xe4, 0xea, 0xbc, 0x63, 0x48, 0x3a, 0x2c, 0xf1, 0xa8, 0x99, 0xe8, 0xc8,
        ];
        assert_eq!(&public, EXPECTED);
        PublicKey::from_x962_uncompressed(&public).unwrap();
    }

    #[test]
    fn test_scalar() {
        const ONE: [u8; 48] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        ];
        let scalar = Scalar::from_bytes_checked(&ONE);
        assert!(scalar.is_ok());
        assert_eq!(scalar.unwrap().as_bytes(), Scalar::small_u64(1).as_bytes());

        let scalar = Scalar::from_bytes_checked(&[0xff; 48]);
        assert!(scalar.is_err());
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
            "[1f, 8d, d6, 1c, 4c, 84, 18, 24, 7c, 87, 54, 13, ad, e1, 0f, 3c, d7, b2, c8, c1, f7, 9d, c0, 88, 77, 9c, 01, 30, a7, af, 85, 5b, b8, d1, d2, ea, 05, 87, ba, 17, 1c, 4c, 57, 83, ad, 8c, 9a, a1]"
        );
    }

    #[test]
    fn private_key_in_range() {
        assert_eq!(
            PrivateKey::from_bytes(&[0u8; 48]).unwrap_err(),
            Error::from(KeyFormatError::ScalarOutOfRange)
        );

        // order rejected
        assert_eq!(PrivateKey::from_bytes(b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xc7\x63\x4d\x81\xf4\x37\x2d\xdf\x58\x1a\x0d\xb2\x48\xb0\xa7\x7a\xec\xec\x19\x6a\xcc\xc5\x29\x73").unwrap_err(), Error::from(KeyFormatError::ScalarOutOfRange));

        // order + 1 rejected
        assert_eq!(PrivateKey::from_bytes(b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xc7\x63\x4d\x81\xf4\x37\x2d\xdf\x58\x1a\x0d\xb2\x48\xb0\xa7\x7a\xec\xec\x19\x6a\xcc\xc5\x29\x74").unwrap_err(), Error::from(KeyFormatError::ScalarOutOfRange));

        // order - 1 is ok
        PrivateKey::from_bytes(b"\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xff\xc7\x63\x4d\x81\xf4\x37\x2d\xdf\x58\x1a\x0d\xb2\x48\xb0\xa7\x7a\xec\xec\x19\x6a\xcc\xc5\x29\x72").unwrap();
    }

    #[test]
    fn curve_field_elements_as_mont() {
        const CURVE_A: FieldElement = FieldElement([
            0x0000_0000_ffff_fffc,
            0xffff_ffff_0000_0000,
            0xffff_ffff_ffff_fffe,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
            0xffff_ffff_ffff_ffff,
        ]);
        const CURVE_B: FieldElement = FieldElement([
            0x2a85_c8ed_d3ec_2aef,
            0xc656_398d_8a2e_d19d,
            0x0314_088f_5013_875a,
            0x181d_9c6e_fe81_4112,
            0x988e_056b_e3f8_2d19,
            0xb331_2fa7_e23e_e7e4,
        ]);

        println!("G.x = {:x?}", CURVE_GENERATOR.x().as_mont());
        println!("G.y = {:x?}", CURVE_GENERATOR.y().as_mont());
        println!("a = {:x?}", CURVE_A.as_mont());
        println!("b = {:x?}", CURVE_B.as_mont());
        let one = FieldElement([1, 0, 0, 0, 0, 0]);
        println!("R = {:x?}", one.as_mont());
        println!("R * R = {:x?}", one.as_mont().as_mont());

        println!("montify n = {:016x?}", Scalar::montifier().0);
    }

    /// Checks each point of `admin/p384-precomp`'s table, which uses
    /// Python's integers, against rind's own arithmetic.
    #[test]
    fn base_point_precomp_comb() {
        let mut base = JacobianMontPoint::from_affine(&CURVE_GENERATOR);
        for table in &precomp::CURVE_GENERATOR_PRECOMP_COMB {
            let mut multiple = base;
            for (i, entry) in (1..).zip(table.as_chunks::<12>().0) {
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
