// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ECDSA's public API: key pairs, public keys, and the algorithms each is
//! bound to.

use core::fmt;

use super::{Buffer, HashId, Pkcs8, Sec1, Sign, Spki, Verify, Write, signed_digest, with_hash};
use crate::error::Error;
use crate::high::asn1;
use crate::high::curve::{
    Curve, MAX_SCALAR_LEN, MAX_UNCOMPRESSED_PUBLIC_KEY_LEN, P256, P384, P521,
};
use crate::high::digest::Digest;
use crate::high::ecdsa::{self, EncodedPoint};
use crate::high::hash::SignatureHash;
use crate::high::{sec1, spki};
use crate::low::{self, Zeroable};
use crate::mid::{p256, p384, p521};

#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
enum CurveId {
    P256,
    P384,
    P521,
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
enum EcdsaEncoding {
    /// A DER `Ecdsa-Sig-Value`, as X.509 and TLS use.
    Asn1,
    /// `r || s`, each the curve's scalar length, as JWS uses.
    Fixed,
}

/// A curve, a hash, and a signature encoding.
#[derive(Clone, Copy, Debug)]
struct Ecdsa {
    curve: CurveId,
    hash: HashId,
    encoding: EcdsaEncoding,
}

/// Runs `$body` with `$C`, `$H`, and `$E` naming the curve, hash, and
/// encoding types of the [`Ecdsa`] `$ecdsa`.
///
/// Only constant functions use it, so a static names only its own
/// algorithm's code: called at run time, it would name every algorithm's.
macro_rules! with_ecdsa {
    ($ecdsa:expr, |$C:ident, $H:ident, $E:ident| $body:expr) => {{
        let ecdsa: Ecdsa = $ecdsa;
        with_hash!(ecdsa.hash, |$H| match ecdsa.encoding {
            EcdsaEncoding::Asn1 => {
                type $E = Asn1;
                with_curve!(ecdsa.curve, |$C| $body)
            }
            EcdsaEncoding::Fixed => {
                type $E = Fixed;
                with_curve!(ecdsa.curve, |$C| $body)
            }
        })
    }};
}

/// Runs `$body` with `$C` naming the curve type for `$curve`.
macro_rules! with_curve {
    ($curve:expr, |$C:ident| $body:expr) => {
        match $curve {
            CurveId::P256 => {
                type $C = P256;
                $body
            }
            CurveId::P384 => {
                type $C = P384;
                $body
            }
            CurveId::P521 => {
                type $C = P521;
                $body
            }
        }
    };
}

/// An ECDSA signature encoding.
trait Encoding {
    fn verify<C: Curve, H: SignatureHash>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error>;

    fn sign<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error>;

    fn verify_digest<C: Curve>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        digest: &[u8],
    ) -> Result<(), Error>;

    /// Signs `digest`, drawing the nonce through `H`.
    fn sign_digest<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        digest: &[u8],
    ) -> Result<&'a [u8], Error>;
}

/// [`EcdsaEncoding::Asn1`].
struct Asn1;

impl Encoding for Asn1 {
    fn verify<C: Curve, H: SignatureHash>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        key.verify_asn1::<H>(message, signature)
    }

    fn sign<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        key.sign_asn1::<H>(message, output)
    }

    fn verify_digest<C: Curve>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        digest: &[u8],
    ) -> Result<(), Error> {
        key.verify_asn1_digest(digest, signature)
    }

    fn sign_digest<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        digest: &[u8],
    ) -> Result<&'a [u8], Error> {
        key.sign_asn1_digest::<H>(digest, output)
    }
}

/// [`EcdsaEncoding::Fixed`].
struct Fixed;

impl Encoding for Fixed {
    fn verify<C: Curve, H: SignatureHash>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        message: &[u8],
    ) -> Result<(), Error> {
        key.verify::<H>(message, signature)
    }

    fn sign<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        message: &[u8],
    ) -> Result<&'a [u8], Error> {
        key.sign::<H>(message, output)
    }

    fn verify_digest<C: Curve>(
        key: &ecdsa::VerifyingKey<C>,
        signature: &[u8],
        digest: &[u8],
    ) -> Result<(), Error> {
        key.verify_digest(digest, signature)
    }

    fn sign_digest<'a, C: Curve, H: SignatureHash>(
        key: &ecdsa::SigningKey<C>,
        output: &'a mut [u8],
        digest: &[u8],
    ) -> Result<&'a [u8], Error> {
        key.sign_digest::<H>(digest, output)
    }
}

/// A curve's place in [`Key`] and [`EcdsaKey`].
trait EcdsaCurve: Curve<PublicKey: Clone> + Sized + 'static {
    fn key(key: EcdsaVerifier<Self>) -> Key;

    fn pair(pair: EcdsaPair<Self>) -> EcdsaKey;
}

macro_rules! ecdsa_curve {
    ($curve:ident) => {
        impl EcdsaCurve for $curve {
            fn key(key: EcdsaVerifier<Self>) -> Key {
                Key::$curve(key)
            }

            fn pair(pair: EcdsaPair<Self>) -> EcdsaKey {
                EcdsaKey::$curve(pair)
            }
        }
    };
}

ecdsa_curve!(P256);
ecdsa_curve!(P384);
ecdsa_curve!(P521);

/// A parsed public key on whichever curve its algorithm names.
// `repr(u8)` puts `P256` at tag zero, and every key is plain words beside a
// `ZeroableRef`, so all-bits-zero is a valid value, as a key pair's wipe
// needs.
#[allow(clippy::large_enum_variant)]
#[repr(u8)]
enum Key {
    P256(EcdsaVerifier<P256>),
    P384(EcdsaVerifier<P384>),
    P521(EcdsaVerifier<P521>),
}

impl Clone for Key {
    fn clone(&self) -> Self {
        match self {
            Self::P256(key) => Self::P256(key.clone()),
            Self::P384(key) => Self::P384(key.clone()),
            Self::P521(key) => Self::P521(key.clone()),
        }
    }
}

/// An ECDSA key and the functions that verify a message and a digest with
/// it, which it reaches only through `ops`: matching on [`Key`] then names no
/// algorithm's code.
struct EcdsaVerifier<C: EcdsaCurve> {
    key: ecdsa::VerifyingKey<C>,
    ops: low::ZeroableRef<VerifyOps<C>>,
}

impl<C: EcdsaCurve> Clone for EcdsaVerifier<C> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            ops: self.ops,
        }
    }
}

struct VerifyOps<C: EcdsaCurve> {
    verify: Verify<ecdsa::VerifyingKey<C>>,
    verify_digest: Verify<ecdsa::VerifyingKey<C>>,
}

impl<C: EcdsaCurve> EcdsaVerifier<C> {
    /// Parses `point` for the encoding and hash `E` and `H`.
    fn parse<H: SignatureHash, E: Encoding>(point: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: ecdsa::VerifyingKey::from_x962_uncompressed(point)?,
            ops: low::ZeroableRef::new(
                const {
                    &VerifyOps {
                        verify: E::verify::<C, H>,
                        verify_digest: E::verify_digest::<C>,
                    }
                },
            ),
        })
    }

    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.ops.get().verify)(&self.key, signature, message)
    }

    fn verify_digest(&self, digest: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.ops.get().verify_digest)(&self.key, signature, digest)
    }
}

/// Runs `$body` with `$key` bound to whichever curve's [`EcdsaVerifier`]
/// `$key_enum` holds.
macro_rules! on_key {
    ($key_enum:expr, |$key:ident| $body:expr) => {
        match $key_enum {
            Key::P256($key) => $body,
            Key::P384($key) => $body,
            Key::P521($key) => $body,
        }
    };
}

fn parse_ecdsa<C: EcdsaCurve, H: SignatureHash, E: Encoding>(point: &[u8]) -> Result<Key, Error> {
    EcdsaVerifier::<C>::parse::<H, E>(point).map(C::key)
}

/// An ECDSA verification algorithm: a curve, a hash, and a signature
/// encoding, which a [`PublicKey`] is bound to.
pub struct VerificationAlgorithm {
    ecdsa: Ecdsa,
    // The only path to the algorithm's code: a binary links only the
    // algorithms it names.
    parse: fn(&[u8]) -> Result<Key, Error>,
    decompress: sec1::Decompress,
}

impl fmt::Debug for VerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VerificationAlgorithm")
            .field(&self.ecdsa)
            .finish()
    }
}

#[cfg_attr(coverage_nightly, coverage(off))] // const-evaluated only
const fn ecdsa_verification(
    curve: CurveId,
    hash: HashId,
    encoding: EcdsaEncoding,
) -> VerificationAlgorithm {
    let ecdsa = Ecdsa {
        curve,
        hash,
        encoding,
    };
    let parse = with_ecdsa!(ecdsa, |C, H, E| parse_ecdsa::<C, H, E> as _);
    let decompress: sec1::Decompress = match curve {
        CurveId::P256 => p256::PublicKey::decompress,
        CurveId::P384 => p384::PublicKey::decompress,
        CurveId::P521 => p521::PublicKey::decompress,
    };
    VerificationAlgorithm {
        ecdsa,
        parse,
        decompress,
    }
}

/// The OID naming `curve`.
fn curve_oid(curve: CurveId) -> asn1::ObjectId {
    match curve {
        CurveId::P256 => P256::oid(),
        CurveId::P384 => P384::oid(),
        CurveId::P521 => P521::oid(),
    }
}

/// An ECDSA public key, bound to the one algorithm it verifies signatures
/// with.
///
/// Its bytes are its X9.62 uncompressed point.
#[derive(Clone)]
pub struct PublicKey {
    key: Key,
    algorithm: Ecdsa,
    point: EncodedPoint,
}

// A `Key`, a descriptor of `repr(u8)` enums each with a variant at zero, and
// bytes and a length.
impl Zeroable for PublicKey {}

impl PublicKey {
    /// Parses an X9.62 uncompressed point for `algorithm`, refusing a
    /// malformed key before any signature arrives.
    ///
    /// A compressed point is refused, which
    /// [`agreement::PublicKey::new`](crate::agreement::PublicKey::new)
    /// decompresses, and [`Self::from_spki`] takes inside a
    /// `SubjectPublicKeyInfo`.
    pub fn new(algorithm: &VerificationAlgorithm, point: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: (algorithm.parse)(point)?,
            algorithm: algorithm.ecdsa,
            point: EncodedPoint::copy_from(point)?,
        })
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, refusing one that names another algorithm or curve.
    ///
    /// It names `id-ecPublicKey` and the algorithm's curve, and its point
    /// may be compressed (RFC 5480), which this decompresses.
    pub fn from_spki(algorithm: &VerificationAlgorithm, der: &[u8]) -> Result<Self, Error> {
        let curve = Some(asn1::Any::ObjectId(curve_oid(algorithm.ecdsa.curve)));
        let point = spki::decode(der, &[&asn1::oid::id_ecPublicKey], curve)?;
        let mut decompressed = [0; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
        Self::new(
            algorithm,
            sec1::uncompressed(point, algorithm.decompress, &mut decompressed)?,
        )
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: `id-ecPublicKey`
    /// on its curve, with its uncompressed point.
    pub fn to_spki(&self) -> Spki {
        let curve = Some(asn1::Any::ObjectId(curve_oid(self.algorithm.curve)));
        Spki(Buffer::encode(|output| {
            spki::encode(self.as_ref(), &asn1::oid::id_ecPublicKey, curve, output)
        }))
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    ///
    /// ECDSA signatures are malleable: `(r, s)` and `(r, n - s)` both verify,
    /// so don't identify a message by its signature's bytes.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        on_key!(&self.key, |key| key.verify(message, signature))
    }

    /// Verifies `signature` over the message `digest` hashes.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the curve and the signature's encoding.
    /// Another hash is refused as [`Error::Unsupported`].
    ///
    /// So unlike [`Self::verify`], this does not pin the hash: hash with the
    /// one your protocol names, never one the signed data or its sender
    /// picks. A signature over one SHA-2 hash verifies over another only
    /// for a message whose digest collides with it, which no one can find.
    pub fn verify_digest(&self, digest: &Digest, signature: &[u8]) -> Result<(), Error> {
        let digest = signed_digest(digest)?;
        on_key!(&self.key, |key| key.verify_digest(digest, signature))
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.point.as_ref()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", &self.algorithm)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// An ECDSA signature: DER for an `ASN1` algorithm, `r || s` for a `FIXED`
/// one.
#[derive(Clone, Copy)]
pub struct Signature(Buffer<SIGNATURE_MAX_LEN>);

// A DER `SEQUENCE`, whose length takes two bytes, of two P-521 `INTEGER`s,
// each with a sign byte, which is longer than `r || s`.
const SIGNATURE_MAX_LEN: usize = 3 + 2 * (2 + MAX_SCALAR_LEN + 1);

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

/// An ECDSA private key as a big-endian scalar exactly the curve's length,
/// wiped on drop.
pub struct Scalar(Buffer<MAX_SCALAR_LEN>);

impl AsRef<[u8]> for Scalar {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Scalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Scalar").finish_non_exhaustive()
    }
}

impl Drop for Scalar {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

/// Signs as `verification` verifies: checked when a static is compiled,
/// never at run time.
const fn ecdsa_signing(verification: &VerificationAlgorithm) -> SigningAlgorithm {
    let ecdsa = verification.ecdsa;
    SigningAlgorithm {
        ecdsa,
        load: with_ecdsa!(ecdsa, |C, H, E| KeyPair::load::<C, H, E> as _),
    }
}

/// An ECDSA signing algorithm, which a [`KeyPair`] is bound to.
pub struct SigningAlgorithm {
    ecdsa: Ecdsa,
    // The only path to the algorithm's code, as `VerificationAlgorithm`'s.
    load: fn(Ecdsa, EcdsaSource<'_>) -> Result<KeyPair, Error>,
}

impl fmt::Debug for SigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SigningAlgorithm")
            .field(&self.ecdsa)
            .finish()
    }
}

/// Where a [`KeyPair`]'s private key comes from.
enum EcdsaSource<'a> {
    Generate,
    Pkcs8(&'a [u8]),
    Sec1(&'a [u8]),
    Scalar {
        scalar: &'a [u8],
        public_key: &'a [u8],
    },
}

/// An ECDSA private key and its public key, bound to one signing algorithm.
pub struct KeyPair {
    key: EcdsaKey,
    public: PublicKey,
}

// `repr(u8)` puts `P256` at tag zero, and every key is plain words beside a
// `ZeroableRef`, so all-bits-zero is a valid value.
#[allow(clippy::large_enum_variant)]
#[repr(u8)]
enum EcdsaKey {
    P256(EcdsaPair<P256>),
    P384(EcdsaPair<P384>),
    P521(EcdsaPair<P521>),
}

/// A private key on curve `C`, with the code that runs it, which it reaches
/// only through `ops`: matching on [`EcdsaKey`] then names no curve's code.
struct EcdsaPair<C: EcdsaCurve> {
    signing: ecdsa::SigningKey<C>,
    ops: low::ZeroableRef<EcdsaOps<C>>,
}

struct EcdsaOps<C: EcdsaCurve> {
    sign: Sign<ecdsa::SigningKey<C>>,
    sign_digest: Sign<ecdsa::SigningKey<C>>,
    to_pkcs8: Write<ecdsa::SigningKey<C>>,
    to_scalar: Write<ecdsa::SigningKey<C>>,
}

/// Runs `$body` with `$pair` bound to whichever curve's [`EcdsaPair`]
/// `$key_pair` holds.
macro_rules! on_ecdsa {
    ($key_pair:expr, |$pair:ident| $body:expr) => {
        match &$key_pair.key {
            EcdsaKey::P256($pair) => $body,
            EcdsaKey::P384($pair) => $body,
            EcdsaKey::P521($pair) => $body,
        }
    };
}

impl KeyPair {
    /// Generates a key pair for `algorithm` from the system random source.
    pub fn generate(algorithm: &'static SigningAlgorithm) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Generate)
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve.
    pub fn from_pkcs8(algorithm: &'static SigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Pkcs8(der))
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve.
    ///
    /// This refuses PKCS#8, which [`Self::from_pkcs8`] takes: a caller always
    /// knows which of the two it holds.
    pub fn from_sec1(algorithm: &'static SigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Sec1(der))
    }

    /// Loads a fixed-length big-endian private scalar, refused unless
    /// `public_key`, an X9.62 uncompressed or compressed point, is its public
    /// key.
    ///
    /// This suits a JWK's `d` and `x`/`y`; prefer [`Self::from_pkcs8`] for
    /// stored keys.
    pub fn from_scalar_and_public_key(
        algorithm: &'static SigningAlgorithm,
        scalar: &[u8],
        public_key: &[u8],
    ) -> Result<Self, Error> {
        let source = EcdsaSource::Scalar { scalar, public_key };
        (algorithm.load)(algorithm.ecdsa, source)
    }

    /// Loads a key pair for `ecdsa`, whose curve, hash, and encoding are `C`,
    /// `H`, and `E`, and derives its public key.
    fn load<C: EcdsaCurve, H: SignatureHash, E: Encoding>(
        ecdsa: Ecdsa,
        source: EcdsaSource<'_>,
    ) -> Result<Self, Error> {
        let signing = match source {
            EcdsaSource::Generate => ecdsa::SigningKey::<C>::generate(),
            EcdsaSource::Pkcs8(der) => ecdsa::SigningKey::from_pkcs8_der(der),
            EcdsaSource::Sec1(der) => ecdsa::SigningKey::from_sec1_der(der),
            EcdsaSource::Scalar { scalar, public_key } => {
                ecdsa::SigningKey::from_private_key_and_public_key(scalar, public_key)
            }
        }?;
        // A loader that checked a given public key kept it, so only a key
        // without one costs a scalar multiplication here.
        let point = signing.public_key_uncompressed();
        let public = PublicKey {
            key: C::key(EcdsaVerifier::parse::<H, E>(point.as_ref()).expect("its own point")),
            algorithm: ecdsa,
            point,
        };
        let ops = const {
            &EcdsaOps {
                sign: E::sign::<C, H>,
                sign_digest: E::sign_digest::<C, H>,
                to_pkcs8: ecdsa::SigningKey::to_pkcs8_der,
                to_scalar: ecdsa::SigningKey::to_scalar,
            }
        };
        Ok(Self {
            key: C::pair(EcdsaPair {
                signing,
                ops: low::ZeroableRef::new(ops),
            }),
            public,
        })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Signs `message` with a fresh nonce.
    pub fn sign(&self, message: &[u8]) -> Result<Signature, Error> {
        Buffer::write(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().sign)(
                &pair.signing,
                output,
                message
            ))
        })
        .map(Signature)
    }

    /// Signs the message `digest` hashes, with a fresh nonce.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the signature's encoding, so
    /// [`PublicKey::verify`] verifies the signature over the message only if
    /// the hashes match; [`PublicKey::verify_digest`] verifies it in any
    /// case. Another hash is refused as [`Error::Unsupported`].
    pub fn sign_digest(&self, digest: &Digest) -> Result<Signature, Error> {
        let digest = signed_digest(digest)?;
        Buffer::write(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().sign_digest)(
                &pair.signing,
                output,
                digest
            ))
        })
        .map(Signature)
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_pkcs8)(
                &pair.signing,
                output
            ))
        }))
    }

    /// Encodes the private key as a big-endian scalar exactly the curve's
    /// length, as a JWK's `d` and SEC1's `privateKey` hold it.
    ///
    /// This is what [`Self::from_scalar_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_scalar(&self) -> Scalar {
        Scalar(Buffer::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_scalar)(
                &pair.signing,
                output
            ))
        }))
    }

    /// Encodes the private key as a SEC1 (RFC 5915) `ECPrivateKey` naming
    /// its curve and holding its public key, as OpenSSL writes it.
    ///
    /// This is what [`Self::from_sec1`] loads; [`Self::to_pkcs8`] holds the
    /// same `ECPrivateKey` without its curve, which PKCS#8 names instead.
    pub fn to_sec1(&self) -> Sec1 {
        let _entry = low::Entry::new_secret();
        // A copy inside the call, so unwiped, unlike `to_scalar`'s.
        let scalar = Buffer::<MAX_SCALAR_LEN>::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_scalar)(
                &pair.signing,
                output
            ))
        });
        let curve = curve_oid(self.public.algorithm.curve);
        Sec1(Buffer::encode(|output| {
            sec1::encode(scalar.as_ref(), self.public.as_ref(), Some(curve), output)
        }))
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", &self.public.algorithm)
            .field("public_key", &self.public.as_ref())
            .finish_non_exhaustive()
    }
}

// Every field is plain words or a `repr(u8)` enum with a variant at zero.
impl Zeroable for KeyPair {}

impl Drop for KeyPair {
    fn drop(&mut self) {
        // Wipes the scalar, which the curve's key leaves to its owner. Wiping
        // the rest, which is not secret, lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(self);
    }
}

/// Algorithms a key pair signs with.
pub(crate) mod sign {
    use super::*;

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static P256_SHA256_ASN1: SigningAlgorithm = ecdsa_signing(&verify::P256_SHA256_ASN1);

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static P384_SHA384_ASN1: SigningAlgorithm = ecdsa_signing(&verify::P384_SHA384_ASN1);

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static P521_SHA512_ASN1: SigningAlgorithm = ecdsa_signing(&verify::P521_SHA512_ASN1);

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static P256_SHA256_FIXED: SigningAlgorithm = ecdsa_signing(&verify::P256_SHA256_FIXED);

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static P384_SHA384_FIXED: SigningAlgorithm = ecdsa_signing(&verify::P384_SHA384_FIXED);

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static P521_SHA512_FIXED: SigningAlgorithm = ecdsa_signing(&verify::P521_SHA512_FIXED);
}

/// Algorithms a public key verifies with.
pub(crate) mod verify {
    use super::*;

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static P256_SHA256_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha256, EcdsaEncoding::Asn1);

    /// ECDSA on P-256 with SHA-384, ASN.1 signatures.
    pub static P256_SHA384_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha384, EcdsaEncoding::Asn1);

    /// ECDSA on P-256 with SHA-512, ASN.1 signatures.
    pub static P256_SHA512_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha512, EcdsaEncoding::Asn1);

    /// ECDSA on P-384 with SHA-256, ASN.1 signatures.
    pub static P384_SHA256_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha256, EcdsaEncoding::Asn1);

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static P384_SHA384_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha384, EcdsaEncoding::Asn1);

    /// ECDSA on P-384 with SHA-512, ASN.1 signatures.
    pub static P384_SHA512_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha512, EcdsaEncoding::Asn1);

    /// ECDSA on P-521 with SHA-256, ASN.1 signatures.
    pub static P521_SHA256_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha256, EcdsaEncoding::Asn1);

    /// ECDSA on P-521 with SHA-384, ASN.1 signatures.
    pub static P521_SHA384_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha384, EcdsaEncoding::Asn1);

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static P521_SHA512_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha512, EcdsaEncoding::Asn1);

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static P256_SHA256_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha256, EcdsaEncoding::Fixed);

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static P384_SHA384_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha384, EcdsaEncoding::Fixed);

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static P521_SHA512_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha512, EcdsaEncoding::Fixed);
}

#[cfg(test)]
impl SigningAlgorithm {
    /// Signs as `verification` verifies, for tests that sign with a
    /// verify-only constant, such as a cross-hash pair.
    pub(crate) fn signing(verification: &VerificationAlgorithm) -> Self {
        ecdsa_signing(verification)
    }

    /// The length of the curve's scalar.
    pub(crate) fn scalar_len(&self) -> usize {
        match self.ecdsa.curve {
            CurveId::P256 => 32,
            CurveId::P384 => 48,
            CurveId::P521 => 66,
        }
    }

    /// The OID of the curve.
    pub(crate) fn curve_oid(&self) -> asn1::ObjectId {
        curve_oid(self.ecdsa.curve)
    }

    /// The hash this signs messages with.
    pub(crate) fn hash(&self) -> &'static crate::high::digest::Algorithm {
        with_hash!(self.ecdsa.hash, |H| {
            <H as crate::high::hash::Hash>::ALGORITHM
        })
    }
}
