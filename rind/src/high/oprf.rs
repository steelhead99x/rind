// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Oblivious pseudorandom functions (RFC 9497): the OPRF mode here, and the
//! VOPRF mode in [`voprf`], over ristretto255, P-256, P-384, and P-521.
//!
//! Each suite's group is a [`Group`] over `mid`'s arithmetic, and each step
//! is RFC 9497's, written once over it. Everything holding the client's
//! input, its blind, or the server's key runs in constant time. Decoding
//! elements and verifying a DLEQ proof handle public data only, and the
//! NIST curves' verification runs their variable-time multiplications.
//!
//! The POPRF mode is left out until its first consumer, the public-metadata
//! Privacy Pass token (draft-ietf-privacypass-public-metadata-issuance), is
//! final.

pub(crate) mod voprf;

use core::fmt;

use crate::error::{Error, KeyFormatError};
use crate::low::{self, Entry, ct, ct_equal};
use crate::mid::hash_to_curve::{Xmd, expand_message_xmd};
use crate::mid::sha2::{Sha256Context, Sha384Context, Sha512Context};
use crate::mid::{p256, p384, p521, ristretto255};

/// An RFC 9497 ciphersuite: a prime-order group and a hash.
pub struct Suite {
    id: SuiteId,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum SuiteId {
    Ristretto255Sha512,
    P256Sha256,
    P384Sha384,
    P521Sha512,
}

impl PartialEq for Suite {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Suite {}

impl fmt::Debug for Suite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        with_group!(self, G => f.write_str(core::str::from_utf8(G::NAME).unwrap()))
    }
}

/// OPRF(ristretto255, SHA-512): 32-byte elements and keys, and 64-byte
/// outputs. Privacy Pass's batched tokens (type `0x0005`) use its VOPRF.
pub static RISTRETTO255_SHA512: Suite = Suite {
    id: SuiteId::Ristretto255Sha512,
};

/// OPRF(P-256, SHA-256): 33-byte compressed elements, 32-byte keys, and
/// 32-byte outputs.
pub static P256_SHA256: Suite = Suite {
    id: SuiteId::P256Sha256,
};

/// OPRF(P-384, SHA-384): 49-byte compressed elements, 48-byte keys, and
/// 48-byte outputs. Privacy Pass's privately verifiable tokens (RFC 9578,
/// type `0x0001`) use its VOPRF.
pub static P384_SHA384: Suite = Suite {
    id: SuiteId::P384Sha384,
};

/// OPRF(P-521, SHA-512): 67-byte compressed elements, 66-byte keys, and
/// 64-byte outputs.
pub static P521_SHA512: Suite = Suite {
    id: SuiteId::P521Sha512,
};

/// The protocol variant, whose value RFC 9497's context string carries.
#[derive(Clone, Copy)]
enum Mode {
    Oprf = 0,
    Voprf = 1,
}

/// A suite's prime-order group and hash, as RFC 9497 section 4 defines them.
trait Group: Sized + 'static {
    /// The suite's identifier.
    const NAME: &'static [u8];

    /// `Ne`.
    const ELEMENT_LEN: usize;

    /// `Ns`.
    const SCALAR_LEN: usize;

    /// Whether `Ne` zero bytes encode the identity, as in ristretto255; no
    /// X9.62 compressed encoding is the point at infinity.
    const ZEROS_ARE_IDENTITY: bool;

    /// The suite's hash, which `expand_message_xmd` runs too.
    type Hash: Xmd + Clone;

    type Scalar;

    /// An element other than the identity, except as a NIST curve's
    /// `Option` holds it.
    type Element: Copy;

    fn suite() -> &'static Suite;

    /// `HashToGroup`, refusing an input that hashes to the identity, which
    /// no input is known to.
    fn hash_to_group(input: &[u8], dst: &[u8]) -> Result<Self::Element, Error>;

    /// `HashToScalar` of the concatenation of `msg`.
    fn hash_to_scalar(msg: &[&[u8]], dst: &[u8]) -> Result<Self::Scalar, Error>;

    /// `RandomScalar`: from 1 to the group order less one.
    fn random_scalar() -> Result<Self::Scalar, Error>;

    /// `DeserializeScalar`: `Ns` bytes below the group order, zero included.
    fn scalar_from_bytes(bytes: &[u8]) -> Option<Self::Scalar>;

    /// `SerializeScalar`, into `Ns` bytes.
    fn scalar_to_bytes(scalar: &Self::Scalar, out: &mut [u8]);

    /// Whether `scalar` is zero, computed in constant time.
    fn is_zero(scalar: &Self::Scalar) -> bool;

    /// `ScalarInverse`, for a nonzero scalar.
    fn invert(scalar: &Self::Scalar) -> Self::Scalar;

    /// `-scalar`.
    fn neg(scalar: &Self::Scalar) -> Self::Scalar;

    /// `a * b + c`.
    fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar;

    /// `DeserializeElement` of a public encoding, refusing the identity.
    fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element>;

    /// `SerializeElement`, into `Ne` bytes, in constant time.
    fn element_to_bytes(element: &Self::Element, out: &mut [u8]);

    /// `scalar * element`, in constant time, for a nonzero scalar.
    fn mul(element: &Self::Element, scalar: &Self::Scalar) -> Self::Element;

    /// `scalar * G`, in constant time, for a nonzero scalar.
    fn mul_base(scalar: &Self::Scalar) -> Self::Element;

    /// `g * G + p * element` for public values, or `None` at the identity.
    fn public_mul_base_add(
        g: &Self::Scalar,
        element: &Self::Element,
        p: &Self::Scalar,
    ) -> Option<Self::Element>;

    /// The sum of `scalar * element` over `terms` for public values, or
    /// `None` at the identity.
    fn public_mul_sum<'a>(
        terms: impl IntoIterator<Item = (&'a Self::Element, &'a Self::Scalar)>,
    ) -> Option<Self::Element>;
}

/// ristretto255 and SHA-512, over `mid`'s ristretto255.
#[derive(Clone, Copy)]
struct Ristretto255;

impl Group for Ristretto255 {
    const NAME: &'static [u8] = b"ristretto255-SHA512";
    const ELEMENT_LEN: usize = 32;
    const SCALAR_LEN: usize = 32;
    const ZEROS_ARE_IDENTITY: bool = true;
    type Hash = Sha512Context;
    type Scalar = ristretto255::Scalar;
    type Element = ristretto255::Element;

    fn suite() -> &'static Suite {
        &RISTRETTO255_SHA512
    }

    fn hash_to_group(input: &[u8], dst: &[u8]) -> Result<Self::Element, Error> {
        let mut uniform = [0u8; 64];
        expand_message_xmd::<Sha512Context>(&[input], dst, &mut uniform)?;
        let element = ristretto255::Element::from_uniform_bytes(&uniform);
        // Only the identity encodes to zeros.
        match ct::into_public(ct_equal(&element.to_bytes(), &[0; 32])) {
            true => Err(identity()),
            false => Ok(element),
        }
    }

    fn hash_to_scalar(msg: &[&[u8]], dst: &[u8]) -> Result<Self::Scalar, Error> {
        let mut uniform = [0u8; 64];
        expand_message_xmd::<Sha512Context>(msg, dst, &mut uniform)?;
        Ok(ristretto255::Scalar::from_uniform_bytes(&uniform))
    }

    fn random_scalar() -> Result<Self::Scalar, Error> {
        ristretto255::Scalar::random()
    }

    fn scalar_from_bytes(bytes: &[u8]) -> Option<Self::Scalar> {
        ristretto255::Scalar::from_canonical_bytes(bytes.try_into().ok()?)
    }

    fn scalar_to_bytes(scalar: &Self::Scalar, out: &mut [u8]) {
        out.copy_from_slice(&scalar.to_bytes());
    }

    fn is_zero(scalar: &Self::Scalar) -> bool {
        scalar.is_zero()
    }

    fn invert(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.invert().expect("only nonzero scalars are inverted")
    }

    fn neg(scalar: &Self::Scalar) -> Self::Scalar {
        scalar.neg()
    }

    fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar {
        a.mul_add(b, c)
    }

    fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element> {
        let bytes: &[u8; 32] = bytes.try_into().ok()?;
        // The identity's only encoding is zeros.
        match *bytes == [0; 32] {
            true => None,
            false => ristretto255::Element::from_bytes(bytes),
        }
    }

    fn element_to_bytes(element: &Self::Element, out: &mut [u8]) {
        out.copy_from_slice(&element.to_bytes());
    }

    fn mul(element: &Self::Element, scalar: &Self::Scalar) -> Self::Element {
        element.mul(scalar)
    }

    fn mul_base(scalar: &Self::Scalar) -> Self::Element {
        ristretto255::Element::mul_base(scalar)
    }

    /// `None` at the identity, as the NIST curves', so every suite refuses
    /// the same proofs.
    fn public_mul_base_add(
        g: &Self::Scalar,
        element: &Self::Element,
        p: &Self::Scalar,
    ) -> Option<Self::Element> {
        not_identity(ristretto255::Element::mul_base(g).add(&element.mul(p)))
    }

    /// `None` at the identity, or for no terms, as the NIST curves'.
    fn public_mul_sum<'a>(
        terms: impl IntoIterator<Item = (&'a Self::Element, &'a Self::Scalar)>,
    ) -> Option<Self::Element> {
        terms
            .into_iter()
            .map(|(element, scalar)| element.mul(scalar))
            .reduce(|sum, product| sum.add(&product))
            .and_then(not_identity)
    }
}

/// A public ristretto255 element, or `None` for the identity, whose only
/// encoding is zeros.
fn not_identity(element: ristretto255::Element) -> Option<ristretto255::Element> {
    (element.to_bytes() != [0; 32]).then_some(element)
}

/// A NIST curve's group and its suite's hash, over `mid`'s curve.
macro_rules! nist_group {
    ($group:ident, $curve:ident, $hash:ty, $name:literal, $suite:ident, $hash_to_curve:path) => {
        #[derive(Clone, Copy)]
        struct $group;

        impl Group for $group {
            const NAME: &'static [u8] = $name;
            const ELEMENT_LEN: usize = $curve::Point::COMPRESSED_BYTES;
            const SCALAR_LEN: usize = $curve::Scalar::BYTES;
            const ZEROS_ARE_IDENTITY: bool = false;
            type Hash = $hash;
            type Scalar = $curve::Scalar;
            type Element = $curve::Point;

            fn suite() -> &'static Suite {
                &$suite
            }

            /// The point at infinity, which no input is known to reach, is
            /// refused as a small-order point.
            fn hash_to_group(input: &[u8], dst: &[u8]) -> Result<Self::Element, Error> {
                $hash_to_curve(input, dst).map(Into::into)
            }

            fn hash_to_scalar(msg: &[&[u8]], dst: &[u8]) -> Result<Self::Scalar, Error> {
                $curve::hash_to_curve::hash_to_scalar(msg, dst)
            }

            fn random_scalar() -> Result<Self::Scalar, Error> {
                $curve::Scalar::random()
            }

            fn scalar_from_bytes(bytes: &[u8]) -> Option<Self::Scalar> {
                $curve::Scalar::from_bytes_below_n(bytes.try_into().ok()?)
            }

            fn scalar_to_bytes(scalar: &Self::Scalar, out: &mut [u8]) {
                out.copy_from_slice(&scalar.as_bytes());
            }

            fn is_zero(scalar: &Self::Scalar) -> bool {
                scalar.is_zero()
            }

            fn invert(scalar: &Self::Scalar) -> Self::Scalar {
                scalar.inv()
            }

            fn neg(scalar: &Self::Scalar) -> Self::Scalar {
                scalar.neg()
            }

            fn mul_add(a: &Self::Scalar, b: &Self::Scalar, c: &Self::Scalar) -> Self::Scalar {
                a.mul_add(b, c)
            }

            /// No compressed encoding is the point at infinity.
            fn element_from_bytes(bytes: &[u8]) -> Option<Self::Element> {
                $curve::Point::from_compressed(bytes)
            }

            fn element_to_bytes(element: &Self::Element, out: &mut [u8]) {
                out.copy_from_slice(&element.to_compressed());
            }

            fn mul(element: &Self::Element, scalar: &Self::Scalar) -> Self::Element {
                element.mul(scalar)
            }

            fn mul_base(scalar: &Self::Scalar) -> Self::Element {
                $curve::Point::mul_base(scalar)
            }

            fn public_mul_base_add(
                g: &Self::Scalar,
                element: &Self::Element,
                p: &Self::Scalar,
            ) -> Option<Self::Element> {
                element.public_mul_base_add(g, p)
            }

            fn public_mul_sum<'a>(
                terms: impl IntoIterator<Item = (&'a Self::Element, &'a Self::Scalar)>,
            ) -> Option<Self::Element> {
                $curve::Point::public_mul_sum(terms)
            }
        }
    };
}

nist_group!(
    P256,
    p256,
    Sha256Context,
    b"P256-SHA256",
    P256_SHA256,
    p256::hash_to_curve::hash_to_curve
);
nist_group!(
    P384,
    p384,
    Sha384Context,
    b"P384-SHA384",
    P384_SHA384,
    p384::hash_to_curve::hash_to_curve
);
nist_group!(
    P521,
    p521,
    Sha512Context,
    b"P521-SHA512",
    P521_SHA512,
    p521::hash_to_curve::hash_to_curve
);

/// Runs `$body` with `$G` the [`Group`] of the suite `$suite`.
macro_rules! with_group {
    ($suite:expr, $G:ident => $body:expr) => {
        match $suite.id {
            SuiteId::Ristretto255Sha512 => {
                type $G = Ristretto255;
                $body
            }
            SuiteId::P256Sha256 => {
                type $G = P256;
                $body
            }
            SuiteId::P384Sha384 => {
                type $G = P384;
                $body
            }
            SuiteId::P521Sha512 => {
                type $G = P521;
                $body
            }
        }
    };
}
use with_group;

/// Defines `$name`, holding a `$inner<G>` for each suite's group `G`, with
/// a `From` for each and a [`Pick`] of each.
///
/// `repr(u8)` puts `Ristretto255` at tag zero, and each variant is plain
/// words and hash states, so all-bits-zero is a valid value, and a drop can
/// wipe the tag and any unused tail along with the rest.
macro_rules! suited {
    ($(#[$attr:meta])* $vis:vis enum $name:ident($inner:ident)) => {
        $(#[$attr])*
        #[repr(u8)]
        $vis enum $name {
            Ristretto255($inner<Ristretto255>),
            P256($inner<P256>),
            P384($inner<P384>),
            P521($inner<P521>),
        }

        impl low::Zeroable for $name {}

        suited!(@each $name $inner Ristretto255 P256 P384 P521);

        impl $name {
            fn suite(&self) -> &'static Suite {
                dispatch!($name, self, inner => inner.suite())
            }
        }
    };
    (@each $name:ident $inner:ident $($group:ident)*) => {
        $(
            impl From<$inner<$group>> for $name {
                fn from(inner: $inner<$group>) -> Self {
                    Self::$group(inner)
                }
            }

            impl Pick<$inner<$group>> for $name {
                fn pick(&self) -> Option<&$inner<$group>> {
                    match self {
                        Self::$group(inner) => Some(inner),
                        _ => None,
                    }
                }
            }
        )*
    };
}
use suited;

/// Runs `$body` with `$inner` the group's value inside `$value`, one of
/// `$name`'s variants.
macro_rules! dispatch {
    ($name:ident, $value:expr, $inner:ident => $body:expr) => {
        match $value {
            $name::Ristretto255($inner) => $body,
            $name::P256($inner) => $body,
            $name::P384($inner) => $body,
            $name::P521($inner) => $body,
        }
    };
}
use dispatch;

/// The `T` inside a [`suited`] enum, if it holds that group's.
trait Pick<T> {
    fn pick(&self) -> Option<&T>;
}

/// The longest element, P-521's.
const MAX_ELEMENT: usize = p521::Point::COMPRESSED_BYTES;

/// The longest scalar, P-521's.
const MAX_SCALAR: usize = p521::Scalar::BYTES;

/// The longest output, SHA-512's.
const MAX_OUTPUT: usize = Sha512Context::OUTPUT_SZ;

/// The longest input or key info RFC 9497 section 5.1 allows: below
/// `2^16 - 1` bytes.
const MAX_INPUT: usize = u16::MAX as usize - 1;

/// Up to `N` bytes.
#[derive(Clone)]
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

/// `SerializeElement(element)`.
fn encode<G: Group>(element: &G::Element) -> Bytes<MAX_ELEMENT> {
    let mut bytes = Bytes::zeroed(G::ELEMENT_LEN);
    G::element_to_bytes(element, bytes.as_mut());
    bytes
}

/// `DeserializeElement(bytes)`, refusing a wrong length, an encoding that
/// does not decode, and the identity.
fn decode<G: Group>(bytes: &[u8]) -> Result<G::Element, Error> {
    if bytes.len() != G::ELEMENT_LEN {
        return Err(KeyFormatError::WrongLength.into());
    }
    G::element_from_bytes(bytes).ok_or_else(|| {
        match G::ZEROS_ARE_IDENTITY && bytes.iter().all(|b| *b == 0) {
            true => KeyFormatError::SmallOrder,
            false => KeyFormatError::NotOnCurve,
        }
        .into()
    })
}

/// Refuses an input at or above RFC 9497 5.1's `2^16 - 1` bytes.
fn check_len(input: &[u8]) -> Result<(), Error> {
    match input.len() <= MAX_INPUT {
        true => Ok(()),
        false => Err(Error::WrongLength),
    }
}

/// `I2OSP(len(x), 2)`, for an `x` the caller bounded below `2^16` bytes.
fn len_prefix(x: &[u8]) -> [u8; 2] {
    debug_assert!(x.len() <= usize::from(u16::MAX));
    (x.len() as u16).to_be_bytes()
}

/// The error for the identity where RFC 9497 forbids it, which no input or
/// batch is known to reach: as the NIST curves' `hash_to_curve` refuses it.
fn identity() -> Error {
    KeyFormatError::SmallOrder.into()
}

/// A domain separation tag: `prefix || contextString`.
struct Dst(Bytes<48>);

impl Dst {
    /// `prefix || "OPRFV1-" || I2OSP(mode, 1) || "-" || identifier`.
    fn new<G: Group>(prefix: &[u8], mode: Mode) -> Self {
        let parts: [&[u8]; 5] = [prefix, b"OPRFV1-", &[mode as u8], b"-", G::NAME];
        let mut dst = Bytes::zeroed(0);
        for part in parts {
            dst.bytes[dst.len..dst.len + part.len()].copy_from_slice(part);
            dst.len += part.len();
        }
        Self(dst)
    }
}

impl AsRef<[u8]> for Dst {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// `HashToScalar` of the concatenation of `msg`, under the default DST.
fn hash_to_scalar<G: Group>(mode: Mode, msg: &[&[u8]]) -> Result<G::Scalar, Error> {
    G::hash_to_scalar(msg, Dst::new::<G>(b"HashToScalar-", mode).as_ref())
}

/// RFC 9497 3.2.1's `DeriveKeyPair(seed, info)`'s private key.
fn derive_scalar<G: Group>(mode: Mode, seed: &[u8], info: &[u8]) -> Result<G::Scalar, Error> {
    check_len(info)?;
    let dst = Dst::new::<G>(b"DeriveKeyPair", mode);
    for counter in 0..=u8::MAX {
        let msg = [seed, &len_prefix(info), info, &[counter]];
        let scalar = G::hash_to_scalar(&msg, dst.as_ref())?;
        // Each counter's hash is zero with a chance of about 2^-252.
        if !ct::into_public(G::is_zero(&scalar)) {
            return Ok(scalar);
        }
    }
    Err(KeyFormatError::ScalarOutOfRange.into())
}

/// `SerializeScalar(scalar)`.
fn scalar_bytes<G: Group>(scalar: &G::Scalar) -> Bytes<MAX_SCALAR> {
    let mut bytes = Bytes::zeroed(G::SCALAR_LEN);
    G::scalar_to_bytes(scalar, bytes.as_mut());
    bytes
}

/// Loads a private key: `Ns` bytes below the group order, and not zero.
fn scalar_from_key<G: Group>(bytes: &[u8]) -> Result<G::Scalar, Error> {
    if bytes.len() != G::SCALAR_LEN {
        return Err(KeyFormatError::WrongLength.into());
    }
    let mut secret = Bytes::<MAX_SCALAR>::zeroed(bytes.len());
    secret.as_mut().copy_from_slice(bytes);
    // The key's bytes are secret; their length is not.
    ct::secret_slice(secret.as_ref());
    match G::scalar_from_bytes(secret.as_ref()) {
        Some(scalar) if !ct::into_public(G::is_zero(&scalar)) => Ok(scalar),
        _ => Err(KeyFormatError::ScalarOutOfRange.into()),
    }
}

/// The client's state between `Blind` and `Finalize`.
struct ClientState<G: Group> {
    blind: G::Scalar,
    /// `Finalize`'s hash, past `I2OSP(len(input), 2) || input`.
    hash: G::Hash,
}

impl<G: Group> ClientState<G> {
    fn suite(&self) -> &'static Suite {
        G::suite()
    }

    /// RFC 9497 3.3.1's `Blind(input)` with the scalar `blind`, returning
    /// this state and the blinded element, made public.
    fn blind(
        mode: Mode,
        input: &[u8],
        blind: G::Scalar,
    ) -> Result<(Self, G::Element, Bytes<MAX_ELEMENT>), Error> {
        check_len(input)?;
        let dst = Dst::new::<G>(b"HashToGroup-", mode);
        let blinded = ct::into_public(G::mul(&G::hash_to_group(input, dst.as_ref())?, &blind));
        let encoded = encode::<G>(&blinded);
        let mut hash = G::Hash::new();
        hash.update(&len_prefix(input));
        hash.update(input);
        Ok((Self { blind, hash }, blinded, encoded))
    }

    /// `Finalize`, for an encoded evaluated element.
    fn finalize_encoded(&self, evaluated_element: &[u8]) -> Result<Output, Error> {
        Ok(self.finalize(&decode::<G>(evaluated_element)?))
    }

    /// RFC 9497 3.3.1's `Finalize`, for the evaluated element.
    fn finalize(&self, evaluated: &G::Element) -> Output {
        let unblinded = G::mul(evaluated, &G::invert(&self.blind));
        finish::<G>(self.hash.clone(), encode::<G>(&unblinded).as_ref())
    }
}

/// `Hash(... || I2OSP(len(element), 2) || element || "Finalize")`, for
/// `hash` past the input.
fn finish<G: Group>(mut hash: G::Hash, element: &[u8]) -> Output {
    hash.update(&len_prefix(element));
    hash.update(element);
    hash.update(b"Finalize");
    let mut output = Output(Bytes::zeroed(G::Hash::OUTPUT));
    let mut full = [0u8; MAX_OUTPUT];
    hash.finish_into(&mut full);
    output.0.as_mut().copy_from_slice(&full[..G::Hash::OUTPUT]);
    output
}

/// RFC 9497 3.3.1's `Evaluate(k, input)`.
fn evaluate<G: Group>(mode: Mode, k: &G::Scalar, input: &[u8]) -> Result<Output, Error> {
    check_len(input)?;
    let dst = Dst::new::<G>(b"HashToGroup-", mode);
    let issued = encode::<G>(&G::mul(&G::hash_to_group(input, dst.as_ref())?, k));
    let mut hash = G::Hash::new();
    hash.update(&len_prefix(input));
    hash.update(input);
    Ok(finish::<G>(hash, issued.as_ref()))
}

/// The server's private key, nonzero.
struct Key<G: Group> {
    k: G::Scalar,
}

impl<G: Group> Key<G> {
    fn suite(&self) -> &'static Suite {
        G::suite()
    }
}

suited!(
    /// A server's key, for one suite.
    enum KeyInner(Key)
);

suited!(
    /// A client's state, for one suite.
    enum BlindInner(ClientState)
);

/// The server's key in the OPRF mode, which evaluates blinded elements for
/// clients, wiped on drop under the `wipe` feature.
///
/// Its outputs differ from a [`voprf::ServerKey`]'s with the same scalar, as
/// RFC 9497 separates the modes.
pub struct ServerKey(KeyInner);

impl ServerKey {
    /// Generates a key for `suite` from the system random source.
    pub fn generate(suite: &'static Suite) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => Ok(Self(Key::<G> { k: G::random_scalar()? }.into())))
    }

    /// Derives a key for `suite` from `seed` and the public `info`, by RFC
    /// 9497 section 3.2.1's `DeriveKeyPair`.
    ///
    /// RFC 9497 calls for a 32-byte seed from a secure random source; RFC
    /// 9807's OPAQUE derives one per user. An `info` of `2^16 - 1` bytes or
    /// more is refused with [`Error::WrongLength`].
    pub fn derive(suite: &'static Suite, seed: &[u8], info: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => Ok(Self(Key::<G> {
            k: derive_scalar::<G>(Mode::Oprf, seed, info)?,
        }
        .into())))
    }

    /// Loads a key for `suite` from its `SerializeScalar` encoding, refused
    /// unless it is from 1 to the group order less one.
    pub fn from_bytes(suite: &'static Suite, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => Ok(Self(Key::<G> { k: scalar_from_key::<G>(bytes)? }.into())))
    }

    /// Encodes the key as [`Self::from_bytes`] loads it.
    pub fn to_bytes(&self) -> ServerKeyBytes {
        dispatch!(KeyInner, &self.0, key => key.to_bytes())
    }

    /// Returns the key's suite.
    pub fn suite(&self) -> &'static Suite {
        self.0.suite()
    }

    /// Evaluates a client's blinded element by RFC 9497 3.3.1's
    /// `BlindEvaluate`, returning the evaluated element to send it.
    ///
    /// An element that does not decode, or is the identity, is refused with
    /// [`Error::KeyRejected`].
    pub fn blind_evaluate(&self, blinded_element: &[u8]) -> Result<EvaluatedElement, Error> {
        let _entry = Entry::new_secret();
        dispatch!(KeyInner, &self.0, key => key.evaluate_element(blinded_element))
    }

    /// Computes the output for `input` directly, by RFC 9497's `Evaluate`,
    /// as a client that blinds `input` would finalize it.
    ///
    /// An `input` of `2^16 - 1` bytes or more is refused with
    /// [`Error::WrongLength`].
    pub fn evaluate(&self, input: &[u8]) -> Result<Output, Error> {
        let _entry = Entry::new_secret();
        dispatch!(KeyInner, &self.0, key => key.evaluate(Mode::Oprf, input))
    }
}

impl<G: Group> Key<G> {
    /// `k * element`.
    fn mul(&self, element: &G::Element) -> G::Element {
        G::mul(element, &self.k)
    }

    fn to_bytes(&self) -> ServerKeyBytes {
        ServerKeyBytes(scalar_bytes::<G>(&self.k))
    }

    /// `BlindEvaluate` of an encoded blinded element, in the OPRF mode.
    fn evaluate_element(&self, blinded_element: &[u8]) -> Result<EvaluatedElement, Error> {
        let blinded = decode::<G>(blinded_element)?;
        let evaluated = ct::into_public(encode::<G>(&self.mul(&blinded)));
        Ok(EvaluatedElement(evaluated))
    }

    fn evaluate(&self, mode: Mode, input: &[u8]) -> Result<Output, Error> {
        evaluate::<G>(mode, &self.k, input)
    }
}

impl Drop for ServerKey {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl low::Zeroable for ServerKey {}

impl fmt::Debug for ServerKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ServerKey")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// A client's secret for one input in the OPRF mode, which turns the
/// server's evaluated element into the output, wiped on drop under the
/// `wipe` feature.
pub struct Blind(BlindInner);

impl Blind {
    /// Blinds `input` for `suite` by RFC 9497 3.3.1's `Blind`, returning the
    /// blind to keep and the blinded element to send the server.
    ///
    /// An `input` of `2^16 - 1` bytes or more is refused with
    /// [`Error::WrongLength`].
    pub fn new(suite: &'static Suite, input: &[u8]) -> Result<(Self, BlindedElement), Error> {
        let _entry = Entry::new_secret();
        with_group!(suite, G => {
            let (state, _, blinded) =
                ClientState::<G>::blind(Mode::Oprf, input, G::random_scalar()?)?;
            Ok((Self(state.into()), BlindedElement(blinded)))
        })
    }

    /// Finalizes the server's evaluated element into the output for the
    /// blinded input, by RFC 9497 3.3.1's `Finalize`.
    ///
    /// An element that does not decode, or is the identity, is refused with
    /// [`Error::KeyRejected`]. A server that evaluated with another key, or
    /// not at all, goes unnoticed: [`voprf`] detects it.
    pub fn finalize(self, evaluated_element: &[u8]) -> Result<Output, Error> {
        let _entry = Entry::new_secret();
        dispatch!(BlindInner, &self.0, state => state.finalize_encoded(evaluated_element))
    }

    /// Returns the blind's suite.
    pub fn suite(&self) -> &'static Suite {
        self.0.suite()
    }
}

impl Drop for Blind {
    fn drop(&mut self) {
        // The hash holds the client's input.
        low::zeroise_value(self);
    }
}

impl low::Zeroable for Blind {}

impl fmt::Debug for Blind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Blind")
            .field("suite", self.suite())
            .finish_non_exhaustive()
    }
}

/// A blinded input, which the client sends the server.
#[derive(Clone)]
pub struct BlindedElement(Bytes<MAX_ELEMENT>);

impl AsRef<[u8]> for BlindedElement {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for BlindedElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("BlindedElement")
            .field(&self.as_ref())
            .finish()
    }
}

/// A blinded input the server evaluated, which it returns to the client.
#[derive(Clone)]
pub struct EvaluatedElement(Bytes<MAX_ELEMENT>);

impl AsRef<[u8]> for EvaluatedElement {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for EvaluatedElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EvaluatedElement")
            .field(&self.as_ref())
            .finish()
    }
}

/// An OPRF output, the suite's hash length, wiped on drop under the `wipe`
/// feature.
pub struct Output(Bytes<MAX_OUTPUT>);

impl AsRef<[u8]> for Output {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl Drop for Output {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

impl fmt::Debug for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Output").finish_non_exhaustive()
    }
}

/// An encoded server key, wiped on drop under the `wipe` feature.
pub struct ServerKeyBytes(Bytes<MAX_SCALAR>);

impl AsRef<[u8]> for ServerKeyBytes {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl Drop for ServerKeyBytes {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

impl fmt::Debug for ServerKeyBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ServerKeyBytes").finish_non_exhaustive()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;
