// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! FROST threshold Schnorr signatures (RFC 9591): its Ed25519, ristretto255,
//! and P-256 ciphersuites, with the trusted dealer of its Appendix C.
//!
//! Each suite's group is a [`Group`] over `mid`'s arithmetic, and each step
//! is RFC 9591's, written once over it. Dealing, nonce generation, and
//! signing multiply by or combine secrets in constant time, and declassify
//! only what they publish: the dealer's commitment, a participant's nonce
//! commitments, and its signature share. Decoding, binding factors, the
//! group commitment, and every verification handle public data, and the NIST
//! curve's run its variable-time multiplications.
//!
//! Distributed key generation, which RFC 9591 leaves out, waits for a
//! consumer, as do the secp256k1 and Ed448 suites.

// `as_chunks` takes no associated constant of a generic group, as clippy's
// suggestion for `chunks_exact(G::ELEMENT_LEN)` would need.
#![allow(clippy::chunks_exact_to_as_chunks)]

#[cfg(target_os = "none")]
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use super::ed25519::Ed25519VerifyingKey;
use crate::error::{Error, KeyFormatError};
use crate::low::{self, Entry, ZeroableRef, ct};
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::sha2::{Sha256Context, Sha512Context};
use crate::mid::{edwards25519, p256, ristretto255};

/// An RFC 9591 ciphersuite: a prime-order group and a hash.
pub struct Suite {
    id: SuiteId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum SuiteId {
    Ed25519Sha512,
    Ristretto255Sha512,
    P256Sha256,
}

impl PartialEq for Suite {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Suite {}

impl fmt::Debug for Suite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self.id {
            SuiteId::Ed25519Sha512 => "FROST(Ed25519, SHA-512)",
            SuiteId::Ristretto255Sha512 => "FROST(ristretto255, SHA-512)",
            SuiteId::P256Sha256 => "FROST(P-256, SHA-256)",
        })
    }
}

/// FROST(Ed25519, SHA-512): 32-byte elements and scalars, and 64-byte
/// signatures that verify as Ed25519 signatures under the group's key.
pub static ED25519_SHA512: Suite = Suite {
    id: SuiteId::Ed25519Sha512,
};

/// FROST(ristretto255, SHA-512): 32-byte elements and scalars, and 64-byte
/// signatures.
pub static RISTRETTO255_SHA512: Suite = Suite {
    id: SuiteId::Ristretto255Sha512,
};

/// FROST(P-256, SHA-256): 33-byte compressed elements, 32-byte scalars, and
/// 65-byte signatures.
pub static P256_SHA256: Suite = Suite {
    id: SuiteId::P256Sha256,
};

/// Every suite's scalar length, `Ns`.
const SCALAR_LEN: usize = 32;

/// The longest element, P-256's compressed point.
const MAX_ELEMENT: usize = p256::Point::COMPRESSED_BYTES;

/// The longest digest, SHA-512's.
const MAX_DIGEST: usize = Sha512Context::OUTPUT_SZ;

/// A suite's prime-order group and hashes, as RFC 9591 section 6 defines
/// them.
trait Group: 'static {
    /// `contextString`.
    const CONTEXT: &'static [u8];

    /// `Ne`.
    const ELEMENT_LEN: usize;

    /// Whether `SerializeScalar` is little-endian.
    const LITTLE_ENDIAN: bool;

    /// A scalar mod the group order.
    type Scalar: low::Zeroable;

    /// An element; the NIST curve's excludes the identity.
    type Element: Copy;

    fn suite() -> &'static Suite;

    /// `DeserializeScalar`: below the group order, zero included. Whether
    /// it is in range is public; its value stays secret.
    fn scalar_from_bytes(bytes: &[u8; SCALAR_LEN]) -> Option<Self::Scalar>;

    /// `SerializeScalar`.
    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; SCALAR_LEN];

    /// Whether `scalar` is zero, computed in constant time.
    fn is_zero(scalar: &Self::Scalar) -> bool;

    /// `a * b + c`, in constant time.
    fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar;

    /// `-scalar`.
    fn neg(scalar: &Self::Scalar) -> Self::Scalar;

    /// `1 / scalar`, for a public nonzero scalar.
    fn invert(scalar: &Self::Scalar) -> Self::Scalar;

    /// A uniformly random nonzero scalar.
    fn random_scalar() -> Result<Self::Scalar, Error>;

    /// `H1`, `H2`, or `H3`, by its `tag` (`rho`, `chal`, or `nonce`), of
    /// the concatenation of `msg`.
    fn hash_to_scalar(tag: &[u8], msg: &[&[u8]]) -> Result<Self::Scalar, Error>;

    /// `H4` or `H5`, by its `tag` (`msg` or `com`), of the concatenation of
    /// `msg`.
    fn hash(tag: &[u8], msg: &[&[u8]]) -> Bytes<MAX_DIGEST>;

    /// `DeserializeElement` of a public encoding of `ELEMENT_LEN` bytes,
    /// refusing one that does not decode, the identity, and, on Ed25519, a
    /// point outside the prime-order subgroup.
    fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element>;

    /// An encoding [`Self::element_from_bytes`] already took, decoded again
    /// without repeating its checks.
    fn element_from_checked(bytes: &[u8]) -> Option<Self::Element> {
        Self::element_from_bytes(bytes)
    }

    /// `SerializeElement` of an element other than the identity, in
    /// constant time.
    fn element_to_bytes(element: &Self::Element) -> Bytes<MAX_ELEMENT>;

    /// `scalar * G`, in constant time, for a nonzero scalar.
    fn mul_base(scalar: &Self::Scalar) -> Self::Element;

    /// The sum of `scalar * element` over `terms`, for public values, or
    /// `None` at the identity.
    fn public_mul_sum(terms: &[(Self::Element, Self::Scalar)]) -> Option<Self::Element>;

    /// `g * G + p * element`, for public values, or `None` at the identity.
    fn public_mul_base_add(
        g: &Self::Scalar,
        element: &Self::Element,
        p: &Self::Scalar,
    ) -> Option<Self::Element>;
}

/// SHA-512 of `prefix || tag || msg`, for the edwards25519 suites.
fn sha512(prefix: &[u8], tag: &[u8], msg: &[&[u8]]) -> [u8; 64] {
    let mut hash = Sha512Context::new();
    hash.update(prefix);
    hash.update(tag);
    for part in msg {
        hash.update(part);
    }
    hash.finish()
}

/// A digest, as [`Group::hash`] returns it.
fn digest(bytes: &[u8]) -> Bytes<MAX_DIGEST> {
    let mut digest = Bytes::zeroed(bytes.len());
    digest.as_mut().copy_from_slice(bytes);
    digest
}

/// The sum of `scalar * element` over `terms`, for the edwards25519
/// suites, whose only multiplication is constant-time: a term whose public
/// scalar is one, such as a hiding commitment, is added without one.
fn edwards_mul_sum<G: Group>(
    terms: &[(G::Element, G::Scalar)],
    mul: impl Fn(&G::Element, &G::Scalar) -> G::Element,
    add: impl Fn(&G::Element, &G::Element) -> G::Element,
) -> Option<G::Element> {
    let one = G::scalar_to_bytes(&scalar_from_u16::<G>(1));
    terms
        .iter()
        .map(
            |(element, scalar)| match G::scalar_to_bytes(scalar) == one {
                true => *element,
                false => mul(element, scalar),
            },
        )
        .reduce(|sum, product| add(&sum, &product))
}

/// FROST(Ed25519, SHA-512), over `mid`'s edwards25519.
struct Ed25519;

impl Ed25519 {
    /// The identity's encoding, `y = 1`.
    const IDENTITY: [u8; 32] = {
        let mut bytes = [0; 32];
        bytes[0] = 1;
        bytes
    };

    /// A public point, or `None` for the identity.
    fn not_identity(point: edwards25519::Point) -> Option<edwards25519::Point> {
        (point.to_bytes() != Self::IDENTITY).then_some(point)
    }
}

impl Group for Ed25519 {
    const CONTEXT: &'static [u8] = b"FROST-ED25519-SHA512-v1";
    const ELEMENT_LEN: usize = 32;
    const LITTLE_ENDIAN: bool = true;
    type Scalar = edwards25519::Scalar;
    type Element = edwards25519::Point;

    fn suite() -> &'static Suite {
        &ED25519_SHA512
    }

    fn scalar_from_bytes(bytes: &[u8; SCALAR_LEN]) -> Option<Self::Scalar> {
        edwards25519::Scalar::from_canonical_bytes(bytes)
    }

    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; SCALAR_LEN] {
        scalar.to_bytes()
    }

    fn is_zero(scalar: &Self::Scalar) -> bool {
        scalar.is_zero()
    }

    fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar {
        a.mul_add(b, c)
    }

    fn neg(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.neg()
    }

    fn invert(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.invert().expect("only nonzero scalars are inverted")
    }

    fn random_scalar() -> Result<Self::Scalar, Error> {
        edwards25519::Scalar::random()
    }

    /// `H2` is SHA-512 alone, as Ed25519's challenge is, so the signature
    /// verifies as Ed25519's.
    fn hash_to_scalar(tag: &[u8], msg: &[&[u8]]) -> Result<Self::Scalar, Error> {
        let uniform = match tag {
            b"chal" => sha512(b"", b"", msg),
            _ => sha512(Self::CONTEXT, tag, msg),
        };
        Ok(edwards25519::Scalar::from_uniform_bytes(&uniform))
    }

    fn hash(tag: &[u8], msg: &[&[u8]]) -> Bytes<MAX_DIGEST> {
        digest(&sha512(Self::CONTEXT, tag, msg))
    }

    /// RFC 8032 5.1.3's decoding, then `[L]P = 0`, checked as
    /// `[L - 1]P + P`, as `L` itself is not a reduced scalar.
    fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element> {
        let point = edwards25519::Point::from_bytes(bytes.try_into().ok()?)?;
        let point = Self::not_identity(point)?;
        let minus_one = scalar_from_u16::<Self>(1).neg();
        match Self::not_identity(point.mul(&minus_one).add(&point)) {
            Some(_) => None,
            None => Some(point),
        }
    }

    /// Skips the subgroup check, a constant-time multiplication.
    fn element_from_checked(bytes: &[u8]) -> Option<Self::Element> {
        edwards25519::Point::from_bytes(bytes.try_into().ok()?)
    }

    fn element_to_bytes(element: &Self::Element) -> Bytes<MAX_ELEMENT> {
        let mut bytes = Bytes::zeroed(Self::ELEMENT_LEN);
        bytes.as_mut().copy_from_slice(&element.to_bytes());
        bytes
    }

    fn mul_base(scalar: &Self::Scalar) -> Self::Element {
        edwards25519::Point::mul_base(scalar)
    }

    fn public_mul_sum(terms: &[(Self::Element, Self::Scalar)]) -> Option<Self::Element> {
        edwards_mul_sum::<Self>(terms, |e, s| e.mul(s), |a, b| a.add(b))
            .and_then(Self::not_identity)
    }

    fn public_mul_base_add(
        g: &Self::Scalar,
        element: &Self::Element,
        p: &Self::Scalar,
    ) -> Option<Self::Element> {
        Self::not_identity(edwards25519::Point::mul_base(g).add(&element.mul(p)))
    }
}

/// FROST(ristretto255, SHA-512), over `mid`'s ristretto255.
struct Ristretto255;

impl Ristretto255 {
    /// A public element, or `None` for the identity, whose only encoding is
    /// zeros.
    fn not_identity(element: ristretto255::Element) -> Option<ristretto255::Element> {
        (element.to_bytes() != [0; 32]).then_some(element)
    }
}

impl Group for Ristretto255 {
    const CONTEXT: &'static [u8] = b"FROST-RISTRETTO255-SHA512-v1";
    const ELEMENT_LEN: usize = 32;
    const LITTLE_ENDIAN: bool = true;
    type Scalar = ristretto255::Scalar;
    type Element = ristretto255::Element;

    fn suite() -> &'static Suite {
        &RISTRETTO255_SHA512
    }

    fn scalar_from_bytes(bytes: &[u8; SCALAR_LEN]) -> Option<Self::Scalar> {
        ristretto255::Scalar::from_canonical_bytes(bytes)
    }

    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; SCALAR_LEN] {
        scalar.to_bytes()
    }

    fn is_zero(scalar: &Self::Scalar) -> bool {
        scalar.is_zero()
    }

    fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar {
        a.mul_add(b, c)
    }

    fn neg(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.neg()
    }

    fn invert(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.invert().expect("only nonzero scalars are inverted")
    }

    fn random_scalar() -> Result<Self::Scalar, Error> {
        ristretto255::Scalar::random()
    }

    fn hash_to_scalar(tag: &[u8], msg: &[&[u8]]) -> Result<Self::Scalar, Error> {
        Ok(ristretto255::Scalar::from_uniform_bytes(&sha512(
            Self::CONTEXT,
            tag,
            msg,
        )))
    }

    fn hash(tag: &[u8], msg: &[&[u8]]) -> Bytes<MAX_DIGEST> {
        digest(&sha512(Self::CONTEXT, tag, msg))
    }

    fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element> {
        let bytes: &[u8; 32] = bytes.try_into().ok()?;
        Self::not_identity(ristretto255::Element::from_bytes(bytes)?)
    }

    fn element_to_bytes(element: &Self::Element) -> Bytes<MAX_ELEMENT> {
        let mut bytes = Bytes::zeroed(Self::ELEMENT_LEN);
        bytes.as_mut().copy_from_slice(&element.to_bytes());
        bytes
    }

    fn mul_base(scalar: &Self::Scalar) -> Self::Element {
        ristretto255::Element::mul_base(scalar)
    }

    fn public_mul_sum(terms: &[(Self::Element, Self::Scalar)]) -> Option<Self::Element> {
        edwards_mul_sum::<Self>(terms, |e, s| e.mul(s), |a, b| a.add(b))
            .and_then(Self::not_identity)
    }

    fn public_mul_base_add(
        g: &Self::Scalar,
        element: &Self::Element,
        p: &Self::Scalar,
    ) -> Option<Self::Element> {
        Self::not_identity(ristretto255::Element::mul_base(g).add(&element.mul(p)))
    }
}

/// FROST(P-256, SHA-256), over `mid`'s P-256.
struct P256;

impl Group for P256 {
    const CONTEXT: &'static [u8] = b"FROST-P256-SHA256-v1";
    const ELEMENT_LEN: usize = p256::Point::COMPRESSED_BYTES;
    const LITTLE_ENDIAN: bool = false;
    type Scalar = p256::Scalar;
    type Element = p256::Point;

    fn suite() -> &'static Suite {
        &P256_SHA256
    }

    fn scalar_from_bytes(bytes: &[u8; SCALAR_LEN]) -> Option<Self::Scalar> {
        p256::Scalar::from_bytes_below_n(bytes)
    }

    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; SCALAR_LEN] {
        scalar.as_bytes()
    }

    fn is_zero(scalar: &Self::Scalar) -> bool {
        scalar.is_zero()
    }

    fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar {
        a.mul_add(b, c)
    }

    fn neg(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.neg()
    }

    fn invert(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.inv()
    }

    fn random_scalar() -> Result<Self::Scalar, Error> {
        p256::Scalar::random()
    }

    /// RFC 9380's `hash_to_field` with the DST `contextString || tag`.
    fn hash_to_scalar(tag: &[u8], msg: &[&[u8]]) -> Result<Self::Scalar, Error> {
        let mut dst = [0u8; 32];
        let len = Self::CONTEXT.len() + tag.len();
        dst[..Self::CONTEXT.len()].copy_from_slice(Self::CONTEXT);
        dst[Self::CONTEXT.len()..len].copy_from_slice(tag);
        p256::hash_to_curve::hash_to_scalar(msg, &dst[..len])
    }

    fn hash(tag: &[u8], msg: &[&[u8]]) -> Bytes<MAX_DIGEST> {
        let mut hash = Sha256Context::new();
        hash.update(Self::CONTEXT);
        hash.update(tag);
        for part in msg {
            hash.update(part);
        }
        digest(&hash.finish())
    }

    /// No compressed encoding is the point at infinity.
    fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element> {
        p256::Point::from_compressed(bytes)
    }

    fn element_to_bytes(element: &Self::Element) -> Bytes<MAX_ELEMENT> {
        let mut bytes = Bytes::zeroed(Self::ELEMENT_LEN);
        bytes.as_mut().copy_from_slice(&element.to_compressed());
        bytes
    }

    fn mul_base(scalar: &Self::Scalar) -> Self::Element {
        p256::Point::mul_base(scalar)
    }

    fn public_mul_sum(terms: &[(Self::Element, Self::Scalar)]) -> Option<Self::Element> {
        p256::Point::public_mul_sum(terms.iter().map(|(element, scalar)| (element, scalar)))
    }

    fn public_mul_base_add(
        g: &Self::Scalar,
        element: &Self::Element,
        p: &Self::Scalar,
    ) -> Option<Self::Element> {
        element.public_mul_base_add(g, p)
    }
}

/// Runs `$body` with `$G` the [`Group`] of the suite `$suite`.
macro_rules! with_group {
    ($suite:expr, $G:ident => $body:expr) => {
        match $suite.id {
            SuiteId::Ed25519Sha512 => {
                type $G = Ed25519;
                $body
            }
            SuiteId::Ristretto255Sha512 => {
                type $G = Ristretto255;
                $body
            }
            SuiteId::P256Sha256 => {
                type $G = P256;
                $body
            }
        }
    };
}

/// Up to `N` bytes. Plain bytes and a length, so all-bits-zero is a value
/// it holds, and a drop can wipe it.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Bytes<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> Bytes<N> {
    fn zeroed(len: usize) -> Self {
        Self { bytes: [0; N], len }
    }

    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes[..self.len]
    }
}

impl<const N: usize> AsRef<[u8]> for Bytes<N> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl<const N: usize> low::Zeroable for Bytes<N> {}

/// `n` as a scalar, for the dealer's identifiers and polynomial powers.
fn scalar_from_u16<G: Group>(n: u16) -> G::Scalar {
    let mut bytes = [0u8; SCALAR_LEN];
    match G::LITTLE_ENDIAN {
        true => bytes[..2].copy_from_slice(&n.to_le_bytes()),
        false => bytes[SCALAR_LEN - 2..].copy_from_slice(&n.to_be_bytes()),
    }
    G::scalar_from_bytes(&bytes).expect("small integers are below the group order")
}

/// `a + b`.
fn add<G: Group>(a: &G::Scalar, b: &G::Scalar) -> G::Scalar {
    G::mul_add(a, &scalar_from_u16::<G>(1), b)
}

/// `a * b`.
fn mul<G: Group>(a: &G::Scalar, b: &G::Scalar) -> G::Scalar {
    G::mul_add(a, b, &scalar_from_u16::<G>(0))
}

/// A canonical scalar the caller already checked, such as one this module
/// encoded.
fn scalar<G: Group>(bytes: &[u8; SCALAR_LEN]) -> G::Scalar {
    G::scalar_from_bytes(bytes).expect("checked when it was loaded")
}

/// An element the caller already checked, such as one this module encoded.
fn element<G: Group>(bytes: &[u8]) -> G::Element {
    G::element_from_checked(bytes).expect("checked when it was loaded")
}

/// `DeserializeElement`, refusing a wrong length, an encoding that does not
/// decode, the identity, and a point outside the prime-order subgroup.
fn decode_element<G: Group>(bytes: &[u8]) -> Result<Bytes<MAX_ELEMENT>, Error> {
    if bytes.len() != G::ELEMENT_LEN {
        return Err(KeyFormatError::WrongLength.into());
    }
    match G::element_from_bytes(bytes) {
        Some(_) => {
            let mut out = Bytes::zeroed(bytes.len());
            out.as_mut().copy_from_slice(bytes);
            Ok(out)
        }
        None => Err(KeyFormatError::NotOnCurve.into()),
    }
}

/// The error for the identity where RFC 9591 forbids it, which no honest
/// run is known to reach.
fn identity() -> Error {
    KeyFormatError::SmallOrder.into()
}

/// A participant's identifier: a nonzero scalar, unique within a group.
///
/// Identifiers order as the integers they are, as RFC 9591 sorts its
/// commitment lists.
#[derive(Clone, Copy)]
pub struct Identifier {
    suite: ZeroableRef<Suite>,
    bytes: [u8; SCALAR_LEN],
}

impl Identifier {
    /// Loads an identifier for `suite` from its `SerializeScalar` encoding,
    /// refused unless it is from 1 to the group order less one.
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let bytes: [u8; SCALAR_LEN] = bytes
            .try_into()
            .map_err(|_| Error::from(KeyFormatError::WrongLength))?;
        with_group!(suite, G => match G::scalar_from_bytes(&bytes) {
            Some(x) if !G::is_zero(&x) => Ok(()),
            _ => Err(Error::from(KeyFormatError::ScalarOutOfRange)),
        })?;
        Ok(Self {
            suite: ZeroableRef::new(suite),
            bytes,
        })
    }

    /// `n`, the identifier RFC 9591's dealer gives the `n`th participant.
    fn from_u16<G: Group>(n: u16) -> Self {
        Self {
            suite: ZeroableRef::new(G::suite()),
            bytes: G::scalar_to_bytes(&scalar_from_u16::<G>(n)),
        }
    }

    /// Returns the identifier's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }

    fn scalar<G: Group>(&self) -> G::Scalar {
        scalar::<G>(&self.bytes)
    }

    /// The bytes, most significant first.
    fn big_endian(&self) -> [u8; SCALAR_LEN] {
        let mut bytes = self.bytes;
        if with_group!(self.suite(), G => G::LITTLE_ENDIAN) {
            bytes.reverse();
        }
        bytes
    }
}

impl AsRef<[u8]> for Identifier {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl PartialEq for Identifier {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Identifier {}

impl PartialOrd for Identifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// By suite, then as integers.
impl Ord for Identifier {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.suite().id, self.big_endian()).cmp(&(other.suite().id, other.big_endian()))
    }
}

impl core::hash::Hash for Identifier {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.suite().id.hash(state);
        self.bytes.hash(state);
    }
}

impl fmt::Debug for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Identifier").field(&self.as_ref()).finish()
    }
}

impl low::Zeroable for Identifier {}

/// A group's public key, under which its signatures verify.
#[derive(Clone, Copy)]
pub struct PublicKey {
    suite: ZeroableRef<Suite>,
    bytes: Bytes<MAX_ELEMENT>,
}

impl PublicKey {
    /// Loads a group public key for `suite` from its `SerializeElement`
    /// encoding.
    ///
    /// An encoding that does not decode, the identity, and, on Ed25519, a
    /// point outside the prime-order subgroup are refused with
    /// [`Error::KeyRejected`].
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        with_group!(suite, G => Ok(Self {
            suite: ZeroableRef::new(suite),
            bytes: decode_element::<G>(bytes)?,
        }))
    }

    /// Returns the key's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }

    /// Verifies a group's `signature` of `message`, by RFC 9591 section
    /// 6's prime-order verification, or, for FROST(Ed25519, SHA-512), as
    /// rind's Ed25519 verifies it.
    ///
    /// Fails with [`Error::BadSignature`] when it does not verify, whatever
    /// its length or encoding.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        let _entry = Entry::new_public();
        match self.suite().id {
            SuiteId::Ed25519Sha512 => Ed25519VerifyingKey::from_bytes(self.as_ref())
                .map_err(|_| Error::BadSignature)?
                .verify(signature, message),
            _ => with_group!(self.suite(), G => self.verify_prime_order::<G>(message, signature)),
        }
    }

    /// `z * G == R + c * PK`, for `c = H2(R || PK || message)`.
    fn verify_prime_order<G: Group>(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        if signature.len() != G::ELEMENT_LEN + SCALAR_LEN {
            return Err(Error::BadSignature);
        }
        let (r, z) = signature.split_at(G::ELEMENT_LEN);
        let r = G::element_from_bytes(r).ok_or(Error::BadSignature)?;
        let z = G::scalar_from_bytes(z.try_into().unwrap()).ok_or(Error::BadSignature)?;
        let c = challenge::<G>(&G::element_to_bytes(&r), self, message)?;
        check_equation::<G>(&z, &element::<G>(self.as_ref()), &c, &r)
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl PartialEq for PublicKey {
    fn eq(&self, other: &Self) -> bool {
        self.suite() == other.suite() && self.as_ref() == other.as_ref()
    }
}

impl Eq for PublicKey {}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("suite", self.suite())
            .field("bytes", &self.as_ref())
            .finish()
    }
}

impl low::Zeroable for PublicKey {}

/// `z * G - c * public == r`, for public values.
fn check_equation<G: Group>(
    z: &G::Scalar,
    public: &G::Element,
    c: &G::Scalar,
    r: &G::Element,
) -> Result<(), Error> {
    let lhs = G::public_mul_base_add(z, public, &G::neg(c)).ok_or(Error::BadSignature)?;
    match G::element_to_bytes(&lhs) == G::element_to_bytes(r) {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

/// `compute_challenge`: `H2(R || PK || message)`.
fn challenge<G: Group>(
    group_commitment: &Bytes<MAX_ELEMENT>,
    public_key: &PublicKey,
    message: &[u8],
) -> Result<G::Scalar, Error> {
    G::hash_to_scalar(
        b"chal",
        &[group_commitment.as_ref(), public_key.as_ref(), message],
    )
}

/// The dealer's commitment to its secret polynomial, RFC 9591's
/// `vss_commitment`: one element per coefficient, from which every
/// participant's public key share and the group's public key follow.
///
/// Its encoding is the coefficients' commitments, concatenated.
#[derive(Clone)]
pub struct VssCommitment {
    suite: &'static Suite,
    public_key: PublicKey,
    min_signers: u16,
    bytes: Vec<u8>,
}

impl VssCommitment {
    /// Loads a commitment for `suite`.
    ///
    /// Fails with [`Error::WrongLength`] unless it is from 2 to `2^16 - 1`
    /// whole elements, and with [`Error::KeyRejected`] when one does not
    /// decode or is the identity.
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        with_group!(suite, G => {
            let count = bytes.len() / G::ELEMENT_LEN;
            if !bytes.len().is_multiple_of(G::ELEMENT_LEN) || !(2..=usize::from(u16::MAX)).contains(&count) {
                return Err(Error::WrongLength);
            }
            for coefficient in bytes.chunks_exact(G::ELEMENT_LEN) {
                decode_element::<G>(coefficient)?;
            }
            Ok(Self::from_checked::<G>(bytes.to_vec(), count as u16))
        })
    }

    /// A commitment of `min_signers` checked elements.
    fn from_checked<G: Group>(bytes: Vec<u8>, min_signers: u16) -> Self {
        let mut public_key = Bytes::zeroed(G::ELEMENT_LEN);
        public_key
            .as_mut()
            .copy_from_slice(&bytes[..G::ELEMENT_LEN]);
        Self {
            suite: G::suite(),
            public_key: PublicKey {
                suite: ZeroableRef::new(G::suite()),
                bytes: public_key,
            },
            min_signers,
            bytes,
        }
    }

    /// Returns the commitment's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite
    }

    /// Returns the group's public key, the commitment to the secret.
    pub fn public_key(&self) -> &PublicKey {
        &self.public_key
    }

    /// Returns how many participants must sign: the number of coefficients.
    pub fn min_signers(&self) -> u16 {
        self.min_signers
    }

    /// The public key share of `identifier`, `sum(C[j] * x^j)`, or `None`
    /// at the identity, which only a zero share has.
    fn public_share<G: Group>(&self, identifier: &Identifier) -> Option<G::Element> {
        let x = identifier.scalar::<G>();
        let mut power = scalar_from_u16::<G>(1);
        let mut terms = Vec::with_capacity(usize::from(self.min_signers));
        for coefficient in self.bytes.chunks_exact(G::ELEMENT_LEN) {
            let next = mul::<G>(&power, &x);
            terms.push((element::<G>(coefficient), power));
            power = next;
        }
        G::public_mul_sum(&terms)
    }
}

impl AsRef<[u8]> for VssCommitment {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl PartialEq for VssCommitment {
    fn eq(&self, other: &Self) -> bool {
        self.suite == other.suite && self.bytes == other.bytes
    }
}

impl Eq for VssCommitment {}

impl fmt::Debug for VssCommitment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VssCommitment")
            .field("suite", self.suite)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// Splits a fresh random signing key for `suite` into `max_signers` shares,
/// any `min_signers` of which sign, by RFC 9591 Appendix C's trusted dealer,
/// returning each participant's share and the commitment they all verify
/// their shares against. The dealer forgets the key.
///
/// The `n`th share's identifier is `n`. Fails with [`Error::WrongLength`]
/// unless `2 <= min_signers <= max_signers`.
pub fn deal(
    suite: &'static Suite,
    min_signers: u16,
    max_signers: u16,
) -> Result<(Vec<SigningShare>, VssCommitment), Error> {
    let _entry = Entry::new_secret();
    if !(2 <= min_signers && min_signers <= max_signers) {
        return Err(Error::WrongLength);
    }
    with_group!(suite, G => {
        let mut coefficients = Vec::with_capacity(usize::from(min_signers));
        let mut drawn = Ok(());
        while drawn.is_ok() && coefficients.len() < usize::from(min_signers) {
            drawn = G::random_scalar().map(|c| coefficients.push(c));
        }
        let dealt = drawn.map(|()| deal_with::<G>(&coefficients, max_signers));
        // The constant coefficient is the group's signing key; the capacity
        // held every coefficient, so no push moved one, leaving a copy
        // freed unwiped.
        low::zeroise(&mut coefficients);
        dealt
    })
}

/// RFC 9591's `trusted_dealer_keygen`, for the polynomial whose
/// coefficients, constant first, are `coefficients`: the shares of
/// identifiers 1 to `max_signers`, and the commitment.
fn deal_with<G: Group>(
    coefficients: &[G::Scalar],
    max_signers: u16,
) -> (Vec<SigningShare>, VssCommitment) {
    let mut commitment = Vec::with_capacity(coefficients.len() * G::ELEMENT_LEN);
    for coefficient in coefficients {
        let element = ct::into_public(G::element_to_bytes(&G::mul_base(coefficient)));
        commitment.extend_from_slice(element.as_ref());
    }
    let commitment = VssCommitment::from_checked::<G>(commitment, coefficients.len() as u16);
    let shares = (1..=max_signers)
        .map(|n| {
            let identifier = Identifier::from_u16::<G>(n);
            let x = identifier.scalar::<G>();
            // Horner's rule, from the highest coefficient.
            let secret = coefficients
                .iter()
                .rev()
                .fold(scalar_from_u16::<G>(0), |acc, coefficient| {
                    G::mul_add(&acc, &x, coefficient)
                });
            SigningShare {
                suite: ZeroableRef::new(G::suite()),
                identifier,
                secret: G::scalar_to_bytes(&secret),
                public_key: *commitment.public_key(),
                min_signers: coefficients.len() as u16,
            }
        })
        .collect();
    (shares, commitment)
}

/// A participant's share of a group's signing key, with its identifier and
/// the group's public key, wiped on drop.
pub struct SigningShare {
    suite: ZeroableRef<Suite>,
    identifier: Identifier,
    secret: [u8; SCALAR_LEN],
    public_key: PublicKey,
    min_signers: u16,
}

impl SigningShare {
    /// Loads the share of `identifier` from its `SerializeScalar` encoding,
    /// verifying it against the dealer's `commitment` by RFC 9591's
    /// `vss_verify`.
    ///
    /// Fails with [`Error::Unsupported`] when `identifier` and `commitment`
    /// are for different suites, and with [`Error::KeyRejected`] unless the
    /// scalar is from 1 to the group order less one and matches the
    /// commitment.
    pub fn from_scalar(
        identifier: &Identifier,
        scalar: &[u8],
        commitment: &VssCommitment,
    ) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        if identifier.suite() != commitment.suite() {
            return Err(Error::Unsupported);
        }
        let secret: [u8; SCALAR_LEN] = scalar
            .try_into()
            .map_err(|_| Error::from(KeyFormatError::WrongLength))?;
        // The share's bytes are secret; their length is not.
        ct::secret_slice(&secret);
        with_group!(commitment.suite(), G => {
            let sk = match G::scalar_from_bytes(&secret) {
                Some(sk) if !ct::into_public(G::is_zero(&sk)) => sk,
                _ => return Err(KeyFormatError::ScalarOutOfRange.into()),
            };
            let public = ct::into_public(G::element_to_bytes(&G::mul_base(&sk)));
            match commitment.public_share::<G>(identifier) {
                Some(want) if G::element_to_bytes(&want) == public => {}
                _ => return Err(KeyFormatError::MismatchedPublicKey.into()),
            }
        });
        Ok(Self {
            suite: ZeroableRef::new(commitment.suite()),
            identifier: *identifier,
            secret,
            public_key: *commitment.public_key(),
            min_signers: commitment.min_signers(),
        })
    }

    /// Encodes the share as [`Self::from_scalar`] loads it.
    pub fn to_scalar(&self) -> Scalar {
        Scalar(self.secret)
    }

    /// Returns the share's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }

    /// Returns the participant's identifier.
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    /// Returns the group's public key.
    pub fn public_key(&self) -> &PublicKey {
        &self.public_key
    }

    /// Returns how many participants must sign.
    pub fn min_signers(&self) -> u16 {
        self.min_signers
    }
}

impl Drop for SigningShare {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for SigningShare {}

impl fmt::Debug for SigningShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningShare")
            .field("identifier", &self.identifier)
            .field("public_key", &self.public_key)
            .finish_non_exhaustive()
    }
}

/// An encoded signing share, wiped on drop.
pub struct Scalar([u8; SCALAR_LEN]);

impl AsRef<[u8]> for Scalar {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Drop for Scalar {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

impl fmt::Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Scalar").finish_non_exhaustive()
    }
}

/// A participant's nonces for one signature, wiped on drop.
///
/// [`Self::sign`] consumes them, and they cannot be copied or encoded, so a
/// pair of nonces signs at most once.
pub struct SigningNonces {
    suite: ZeroableRef<Suite>,
    /// The secret and group key of the share that drew them, which with the
    /// identifier in the commitments name that share: one dealer's
    /// polynomials can share a group key yet give one identifier different
    /// secrets.
    share: [u8; SCALAR_LEN],
    public_key: PublicKey,
    hiding: [u8; SCALAR_LEN],
    binding: [u8; SCALAR_LEN],
    commitments: Commitments,
}

impl SigningNonces {
    /// Draws nonces for `share` by RFC 9591's `commit`, returning them to
    /// keep and their commitments to send the coordinator.
    ///
    /// Each nonce is `nonce_generate`'s: a hash of 32 fresh bytes from the
    /// system random source and the share, which keeps a nonce secret from
    /// whoever can predict those bytes. It does not survive their repeating:
    /// the same bytes and share give the same nonces.
    pub fn commit(share: &SigningShare) -> Result<(Self, Commitments), Error> {
        let _entry = Entry::new_secret();
        let mut random = [[0u8; 32]; 2];
        // A zero nonce, with a chance of about 2^-252 a draw, would put the
        // identity in the commitments; another draw replaces it.
        for _ in 0..64 {
            for bytes in &mut random {
                SystemRandom.fill(bytes)?;
                ct::secret_slice(bytes);
            }
            let nonces = with_group!(share.suite(), G => Self::commit_with::<G>(share, &random)?);
            if let Some(nonces) = nonces {
                let commitments = nonces.commitments.clone();
                return Ok((nonces, commitments));
            }
        }
        Err(Error::RngFailed)
    }

    /// `commit` with the hiding and binding nonces' randomness, or `None`
    /// when a nonce is zero.
    fn commit_with<G: Group>(
        share: &SigningShare,
        random: &[[u8; 32]; 2],
    ) -> Result<Option<Self>, Error> {
        let secret = share.secret;
        let [hiding, binding] = [&random[0], &random[1]]
            .map(|random| G::hash_to_scalar(b"nonce", &[random.as_slice(), secret.as_slice()]));
        let (hiding, binding) = (hiding?, binding?);
        if ct::into_public(G::is_zero(&hiding) | G::is_zero(&binding)) {
            return Ok(None);
        }
        let mut commitments = Commitments {
            suite: ZeroableRef::new(G::suite()),
            bytes: Bytes::zeroed(SCALAR_LEN + 2 * G::ELEMENT_LEN),
        };
        let bytes = commitments.bytes.as_mut();
        bytes[..SCALAR_LEN].copy_from_slice(share.identifier.as_ref());
        for (nonce, out) in [&hiding, &binding]
            .into_iter()
            .zip(bytes[SCALAR_LEN..].chunks_exact_mut(G::ELEMENT_LEN))
        {
            out.copy_from_slice(ct::into_public(G::element_to_bytes(&G::mul_base(nonce))).as_ref());
        }
        Ok(Some(Self {
            suite: ZeroableRef::new(G::suite()),
            share: secret,
            public_key: share.public_key,
            hiding: G::scalar_to_bytes(&hiding),
            binding: G::scalar_to_bytes(&binding),
            commitments,
        }))
    }

    /// Signs the coordinator's `package` with `share`, by RFC 9591's
    /// `sign`, consuming the nonces.
    ///
    /// Fails with [`Error::Unsupported`] for values of different suites,
    /// with [`Error::WrongLength`] when the package has fewer commitments
    /// than the group's threshold, and with [`Error::KeyRejected`] when the
    /// package is for another group's key, lacks these nonces' commitments
    /// under the share's identifier, or the nonces are another share's.
    pub fn sign(
        self,
        share: &SigningShare,
        package: &SigningPackage,
    ) -> Result<SignatureShare, Error> {
        let _entry = Entry::new_secret();
        if self.suite() != share.suite() || share.suite() != package.suite() {
            return Err(Error::Unsupported);
        }
        if share.public_key != package.public_key {
            return Err(KeyFormatError::MismatchedPublicKey.into());
        }
        // Whether the secrets match is all the comparison publishes.
        if self.commitments.identifier() != share.identifier
            || self.public_key != share.public_key
            || !ct::into_public(low::ct_equal(&self.share, &share.secret))
        {
            return Err(KeyFormatError::MismatchedCommitments.into());
        }
        if package.commitments.len() < usize::from(share.min_signers) {
            return Err(Error::WrongLength);
        }
        let index = package.index(&share.identifier)?;
        if package.commitments[index] != self.commitments {
            return Err(KeyFormatError::MismatchedCommitments.into());
        }
        with_group!(share.suite(), G => Ok(self.sign_with::<G>(share, package, index)))
    }

    /// `hiding + binding * rho + lambda * c * sk`.
    fn sign_with<G: Group>(
        &self,
        share: &SigningShare,
        package: &SigningPackage,
        index: usize,
    ) -> SignatureShare {
        let rho = scalar::<G>(&package.binding_factors[index]);
        let c = scalar::<G>(&package.challenge);
        let lambda = package.lagrange::<G>(index);
        let z = G::mul_add(
            &mul::<G>(&lambda, &c),
            &scalar::<G>(&share.secret),
            &G::mul_add(
                &scalar::<G>(&self.binding),
                &rho,
                &scalar::<G>(&self.hiding),
            ),
        );
        let mut bytes = [0u8; SCALAR_LEN * 2];
        bytes[..SCALAR_LEN].copy_from_slice(share.identifier.as_ref());
        bytes[SCALAR_LEN..].copy_from_slice(&ct::into_public(G::scalar_to_bytes(&z)));
        SignatureShare {
            suite: G::suite(),
            bytes,
        }
    }

    /// Returns the nonces' suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }
}

impl Drop for SigningNonces {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for SigningNonces {}

impl fmt::Debug for SigningNonces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningNonces")
            .field("commitments", &self.commitments)
            .finish_non_exhaustive()
    }
}

/// A participant's nonce commitments, which it sends the coordinator: its
/// identifier, then its hiding and binding commitments, as one entry of RFC
/// 9591's `encode_group_commitment_list`.
#[derive(Clone)]
pub struct Commitments {
    suite: ZeroableRef<Suite>,
    bytes: Bytes<{ SCALAR_LEN + 2 * MAX_ELEMENT }>,
}

impl Commitments {
    /// Loads a participant's commitments for `suite`.
    ///
    /// Fails with [`Error::KeyRejected`] when the identifier is not from 1
    /// to the group order less one, or an element does not decode, is the
    /// identity, or, on Ed25519, lies outside the prime-order subgroup.
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        with_group!(suite, G => {
            if bytes.len() != SCALAR_LEN + 2 * G::ELEMENT_LEN {
                return Err(KeyFormatError::WrongLength.into());
            }
            Identifier::new(suite, &bytes[..SCALAR_LEN])?;
            for element in bytes[SCALAR_LEN..].chunks_exact(G::ELEMENT_LEN) {
                decode_element::<G>(element)?;
            }
        });
        let mut out = Bytes::zeroed(bytes.len());
        out.as_mut().copy_from_slice(bytes);
        Ok(Self {
            suite: ZeroableRef::new(suite),
            bytes: out,
        })
    }

    /// Returns the commitments' suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite.get()
    }

    /// Returns the participant's identifier.
    pub fn identifier(&self) -> Identifier {
        Identifier {
            suite: self.suite,
            bytes: self.bytes.as_ref()[..SCALAR_LEN].try_into().unwrap(),
        }
    }

    /// The hiding and binding commitments.
    fn elements<G: Group>(&self) -> [G::Element; 2] {
        let (hiding, binding) = self.bytes.as_ref()[SCALAR_LEN..].split_at(G::ELEMENT_LEN);
        [element::<G>(hiding), element::<G>(binding)]
    }
}

impl PartialEq for Commitments {
    fn eq(&self, other: &Self) -> bool {
        self.suite() == other.suite() && self.as_ref() == other.as_ref()
    }
}

impl Eq for Commitments {}

impl AsRef<[u8]> for Commitments {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl fmt::Debug for Commitments {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Commitments").field(&self.as_ref()).finish()
    }
}

impl low::Zeroable for Commitments {}

/// What every signer of one signature signs: the group's key, the message,
/// and the participants' commitments, from which RFC 9591's binding
/// factors, group commitment, and challenge follow.
///
/// The coordinator and each participant build the same package from the
/// same commitments and message; the message is not kept.
#[derive(Clone)]
pub struct SigningPackage {
    suite: &'static Suite,
    public_key: PublicKey,
    /// Sorted by identifier, each once.
    commitments: Vec<Commitments>,
    /// Each participant's binding factor, in the commitments' order.
    binding_factors: Vec<[u8; SCALAR_LEN]>,
    group_commitment: Bytes<MAX_ELEMENT>,
    challenge: [u8; SCALAR_LEN],
}

impl SigningPackage {
    /// Builds the package for signing `message` under `public_key` with the
    /// participants whose `commitments` are given, in any order.
    ///
    /// Fails with [`Error::Unsupported`] for values of different suites,
    /// with [`Error::WrongLength`] for no commitments or more than `2^16 -
    /// 1`, and with [`Error::KeyRejected`] when two share an identifier or
    /// the group commitment is the identity.
    pub fn new(
        public_key: &PublicKey,
        commitments: &[Commitments],
        message: &[u8],
    ) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        if commitments.iter().any(|c| c.suite() != public_key.suite()) {
            return Err(Error::Unsupported);
        }
        if !(1..=usize::from(u16::MAX)).contains(&commitments.len()) {
            return Err(Error::WrongLength);
        }
        let mut commitments = commitments.to_vec();
        // Unstable, as the stable sort divides; equal identifiers are refused.
        commitments.sort_unstable_by_key(Commitments::identifier);
        if commitments
            .windows(2)
            .any(|pair| pair[0].identifier() == pair[1].identifier())
        {
            return Err(KeyFormatError::DuplicateIdentifier.into());
        }
        with_group!(public_key.suite(), G => Self::new_with::<G>(public_key, commitments, message))
    }

    /// RFC 9591's `compute_binding_factors`, `compute_group_commitment`, and
    /// `compute_challenge`.
    fn new_with<G: Group>(
        public_key: &PublicKey,
        commitments: Vec<Commitments>,
        message: &[u8],
    ) -> Result<Self, Error> {
        let msg_hash = G::hash(b"msg", &[message]);
        let list: Vec<&[u8]> = commitments.iter().map(AsRef::as_ref).collect();
        let commitment_hash = G::hash(b"com", &list);
        let prefix: [&[u8]; 3] = [
            public_key.as_ref(),
            msg_hash.as_ref(),
            commitment_hash.as_ref(),
        ];
        let mut binding_factors = Vec::with_capacity(commitments.len());
        let mut terms = Vec::with_capacity(2 * commitments.len());
        for commitment in &commitments {
            let rho = G::hash_to_scalar(
                b"rho",
                &[
                    prefix[0],
                    prefix[1],
                    prefix[2],
                    commitment.identifier().as_ref(),
                ],
            )?;
            let [hiding, binding] = commitment.elements::<G>();
            terms.push((hiding, scalar_from_u16::<G>(1)));
            binding_factors.push(G::scalar_to_bytes(&rho));
            terms.push((binding, rho));
        }
        let group_commitment =
            G::element_to_bytes(&G::public_mul_sum(&terms).ok_or_else(identity)?);
        let challenge =
            G::scalar_to_bytes(&challenge::<G>(&group_commitment, public_key, message)?);
        Ok(Self {
            suite: G::suite(),
            public_key: *public_key,
            commitments,
            binding_factors,
            group_commitment,
            challenge,
        })
    }

    /// Returns the package's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite
    }

    /// Returns the group's public key.
    pub fn public_key(&self) -> &PublicKey {
        &self.public_key
    }

    /// The position of `identifier`'s commitments.
    fn index(&self, identifier: &Identifier) -> Result<usize, Error> {
        self.commitments
            .binary_search_by_key(identifier, Commitments::identifier)
            .map_err(|_| KeyFormatError::UnknownIdentifier.into())
    }

    /// RFC 9591's `derive_interpolating_value` for the participant at
    /// `index`, over public identifiers.
    fn lagrange<G: Group>(&self, index: usize) -> G::Scalar {
        let x_i = self.commitments[index].identifier().scalar::<G>();
        let mut numerator = scalar_from_u16::<G>(1);
        let mut denominator = scalar_from_u16::<G>(1);
        for (j, commitment) in self.commitments.iter().enumerate() {
            if j != index {
                let x_j = commitment.identifier().scalar::<G>();
                numerator = mul::<G>(&numerator, &x_j);
                denominator = mul::<G>(&denominator, &add::<G>(&x_j, &G::neg(&x_i)));
            }
        }
        mul::<G>(&numerator, &G::invert(&denominator))
    }

    /// Sums the participants' signature `shares`, in any order, into the
    /// group's signature, by RFC 9591's `aggregate`, and verifies it.
    ///
    /// Fails with [`Error::Unsupported`] for values of different suites,
    /// with [`Error::WrongLength`] or [`Error::KeyRejected`] unless there is
    /// one share for each participant in the package, and with
    /// [`Error::BadSignature`] when the signature does not verify: then
    /// [`Self::verify_share`] finds the shares at fault.
    pub fn aggregate(&self, shares: &[SignatureShare]) -> Result<Signature, Error> {
        let _entry = Entry::new_public();
        if shares.iter().any(|share| share.suite() != self.suite) {
            return Err(Error::Unsupported);
        }
        if shares.len() != self.commitments.len() {
            return Err(Error::WrongLength);
        }
        let mut identifiers: Vec<Identifier> =
            shares.iter().map(SignatureShare::identifier).collect();
        identifiers.sort_unstable();
        if identifiers
            .iter()
            .zip(&self.commitments)
            .any(|(share, commitment)| *share != commitment.identifier())
        {
            return Err(KeyFormatError::UnknownIdentifier.into());
        }
        with_group!(self.suite, G => self.aggregate_with::<G>(shares))
    }

    fn aggregate_with<G: Group>(&self, shares: &[SignatureShare]) -> Result<Signature, Error> {
        let z = shares.iter().fold(scalar_from_u16::<G>(0), |sum, share| {
            add::<G>(&sum, &share.z::<G>())
        });
        let r = element::<G>(self.group_commitment.as_ref());
        check_equation::<G>(
            &z,
            &element::<G>(self.public_key.as_ref()),
            &scalar::<G>(&self.challenge),
            &r,
        )?;
        let mut signature = Signature(Bytes::zeroed(G::ELEMENT_LEN + SCALAR_LEN));
        let bytes = signature.0.as_mut();
        bytes[..G::ELEMENT_LEN].copy_from_slice(self.group_commitment.as_ref());
        bytes[G::ELEMENT_LEN..].copy_from_slice(&G::scalar_to_bytes(&z));
        Ok(signature)
    }

    /// Verifies one participant's signature `share` against the dealer's
    /// `commitment`, by RFC 9591's `verify_signature_share`.
    ///
    /// Fails with [`Error::Unsupported`] for values of different suites,
    /// with [`Error::KeyRejected`] when `commitment` is another group's or
    /// the share's participant is not in the package, and with
    /// [`Error::BadSignature`] when the share is not that participant's.
    pub fn verify_share(
        &self,
        share: &SignatureShare,
        commitment: &VssCommitment,
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        if share.suite() != self.suite || commitment.suite() != self.suite {
            return Err(Error::Unsupported);
        }
        if *commitment.public_key() != self.public_key {
            return Err(KeyFormatError::MismatchedPublicKey.into());
        }
        let index = self.index(&share.identifier())?;
        with_group!(self.suite, G => self.verify_share_with::<G>(share, commitment, index))
    }

    /// `z_i * G == R_i + (c * lambda_i) * PK_i`.
    fn verify_share_with<G: Group>(
        &self,
        share: &SignatureShare,
        commitment: &VssCommitment,
        index: usize,
    ) -> Result<(), Error> {
        let public = commitment
            .public_share::<G>(&share.identifier())
            .ok_or(Error::BadSignature)?;
        let [hiding, binding] = self.commitments[index].elements::<G>();
        let rho = scalar::<G>(&self.binding_factors[index]);
        let r = G::public_mul_sum(&[(hiding, scalar_from_u16::<G>(1)), (binding, rho)])
            .ok_or(Error::BadSignature)?;
        let c = mul::<G>(&scalar::<G>(&self.challenge), &self.lagrange::<G>(index));
        check_equation::<G>(&share.z::<G>(), &public, &c, &r)
    }
}

impl fmt::Debug for SigningPackage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningPackage")
            .field("public_key", &self.public_key)
            .field("commitments", &self.commitments)
            .finish_non_exhaustive()
    }
}

/// A participant's share of a signature, which it sends the coordinator:
/// its identifier, then its scalar `z_i`.
#[derive(Clone, PartialEq, Eq)]
pub struct SignatureShare {
    suite: &'static Suite,
    bytes: [u8; SCALAR_LEN * 2],
}

impl SignatureShare {
    /// Loads a participant's signature share for `suite`.
    ///
    /// Fails with [`Error::KeyRejected`] when the identifier is not from 1
    /// to the group order less one, or the scalar is not below the order.
    pub fn new(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let bytes: [u8; SCALAR_LEN * 2] = bytes
            .try_into()
            .map_err(|_| Error::from(KeyFormatError::WrongLength))?;
        Identifier::new(suite, &bytes[..SCALAR_LEN])?;
        with_group!(suite, G => G::scalar_from_bytes(bytes[SCALAR_LEN..].try_into().unwrap())
            .map(|_| ())
            .ok_or(Error::from(KeyFormatError::ScalarOutOfRange)))?;
        Ok(Self { suite, bytes })
    }

    /// Returns the share's suite.
    pub fn suite(&self) -> &'static Suite {
        self.suite
    }

    /// Returns the participant's identifier.
    pub fn identifier(&self) -> Identifier {
        Identifier {
            suite: ZeroableRef::new(self.suite),
            bytes: self.bytes[..SCALAR_LEN].try_into().unwrap(),
        }
    }

    fn z<G: Group>(&self) -> G::Scalar {
        scalar::<G>(self.bytes[SCALAR_LEN..].try_into().unwrap())
    }
}

impl AsRef<[u8]> for SignatureShare {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl fmt::Debug for SignatureShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SignatureShare")
            .field(&self.as_ref())
            .finish()
    }
}

/// A group's signature, `SerializeElement(R) || SerializeScalar(z)`.
#[derive(Clone, PartialEq, Eq)]
pub struct Signature(Bytes<{ MAX_ELEMENT + SCALAR_LEN }>);

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;
