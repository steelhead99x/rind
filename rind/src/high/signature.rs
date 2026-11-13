// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::asn1::{self, Type, pkix};
use super::curve::{Curve, MAX_SCALAR_LEN, MAX_UNCOMPRESSED_PUBLIC_KEY_LEN, P256, P384, P521};
use super::digest::Digest;
use super::ecdsa;
use super::ed25519::{Ed25519SigningKey, Ed25519VerifyingKey};
use super::hash::{Sha256, Sha384, Sha512, SignatureHash};
use super::rsa::{self, PssSalt};
use super::{pkcs8, sec1, spki};
use crate::error::{Error, KeyFormatError};
use crate::low::{self, Zeroable};
use crate::mid::mldsa::{self, MlDsa44, MlDsa65, MlDsa87, Params as MlDsaParams};
use crate::mid::rsa_key_size::RsaKeySize;
use crate::mid::rsa_pub::MAX_PUBLIC_MODULUS_BYTES;
use crate::mid::{p256, p384, p521};

/// The hash a signature algorithm applies to the message.
///
/// No variant is SHA-1, so SHA-1 never reaches signing or ECDSA: only
/// [`RsaVerification::Pkcs1Sha1`] takes it.
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
enum HashId {
    Sha256,
    Sha384,
    Sha512,
}

impl HashId {
    /// The hash's output length, in bytes.
    const fn len(self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha384 => 48,
            Self::Sha512 => 64,
        }
    }
}

/// Runs `$body` with `$H` naming the hash type for `$hash`.
macro_rules! with_hash {
    ($hash:expr, |$H:ident| $body:expr) => {
        match $hash {
            HashId::Sha256 => {
                type $H = Sha256;
                $body
            }
            HashId::Sha384 => {
                type $H = Sha384;
                $body
            }
            HashId::Sha512 => {
                type $H = Sha512;
                $body
            }
        }
    };
}

/// Up to `N` bytes, as the owned encodings and signatures hold them.
#[derive(Clone, Copy)]
pub(super) struct Buffer<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> Buffer<N> {
    fn new() -> Self {
        Self {
            bytes: [0; N],
            len: 0,
        }
    }

    // `let else` rather than `ok_or(..)?` on the `&mut` span, whose
    // translation `proofs/` cannot check. The compiled code is the same.
    fn copy_from(bytes: &[u8]) -> Result<Self, Error> {
        let mut buffer = Self::new();
        let Some(span) = buffer.bytes.get_mut(..bytes.len()) else {
            return Err(Error::WrongLength);
        };
        span.copy_from_slice(bytes);
        buffer.len = bytes.len();
        Ok(buffer)
    }

    /// Runs `write`, which writes to the start of its argument and returns
    /// the written span.
    pub(super) fn write(
        write: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>,
    ) -> Result<Self, Error> {
        let mut buffer = Self::new();
        buffer.len = write(&mut buffer.bytes)?.len();
        Ok(buffer)
    }

    /// Copies into a buffer at least as large.
    fn widen<const M: usize>(&self) -> Buffer<M> {
        const { assert!(M >= N) };
        let mut wide = Buffer::new();
        wide.bytes[..N].copy_from_slice(&self.bytes);
        wide.len = self.len;
        wide
    }

    /// Runs `encode` as [`Self::write`] does, for an encoder `N` is sized
    /// for.
    ///
    /// Every `N` holds the encoding of the largest key a loader accepts, so
    /// an encoder that runs out of room is a bug in rind, not bad input.
    pub(super) fn encode(encode: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>) -> Self {
        Self::write(encode).expect("sized for the largest key")
    }
}

impl<const N: usize> From<[u8; N]> for Buffer<N> {
    fn from(bytes: [u8; N]) -> Self {
        Self { bytes, len: N }
    }
}

impl<const N: usize> AsRef<[u8]> for Buffer<N> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

// Bytes and a length, both valid at zero.
impl<const N: usize> Zeroable for Buffer<N> {}

/// A signature verification algorithm, which a [`PublicKey`] is bound to.
pub struct VerificationAlgorithm(Verification);

/// An algorithm and the function that parses its keys, which is the only
/// path to its code: a binary links only the algorithms it names. ECDSA's
/// also holds its curve's [`sec1::Decompress`].
#[derive(Clone, Copy)]
enum Verification {
    Ecdsa(
        Ecdsa,
        fn(Ecdsa, &[u8]) -> Result<Parsed, Error>,
        sec1::Decompress,
    ),
    Rsa(Rsa),
    Ed25519(fn(&[u8]) -> Result<Parsed, Error>),
    MlDsa(MlDsaAlgorithm),
}

impl fmt::Debug for Verification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ecdsa(ecdsa, ..) => f.debug_tuple("Ecdsa").field(ecdsa).finish(),
            Self::Rsa(rsa) => f.debug_tuple("Rsa").field(rsa).finish(),
            Self::Ed25519(_) => f.write_str("Ed25519"),
            Self::MlDsa(algorithm) => f.write_str(algorithm.name),
        }
    }
}

/// Verifies with a key: `(key, signature, message)`.
type Verify<K> = fn(&K, &[u8], &[u8]) -> Result<(), Error>;

/// Signs a message into the start of an output and returns the signature:
/// `(key, output, message)`.
type Sign<K> = for<'a> fn(&K, &'a mut [u8], &[u8]) -> Result<&'a [u8], Error>;

/// A parsed key and the function that verifies with it, which only its
/// algorithm's static names: matching on [`Parsed`] then names no
/// algorithm's code.
struct Verifier<K> {
    key: K,
    verify: Verify<K>,
}

impl<K> Verifier<K> {
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.verify)(&self.key, signature, message)
    }
}

impl fmt::Debug for VerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl AsRef<Self> for VerificationAlgorithm {
    fn as_ref(&self) -> &Self {
        self
    }
}

/// An RSA signature verification algorithm, which
/// [`PublicKey::from_components`] also takes.
pub struct RsaVerificationAlgorithm {
    rsa: Rsa,
    algorithm: VerificationAlgorithm,
}

impl AsRef<VerificationAlgorithm> for RsaVerificationAlgorithm {
    fn as_ref(&self) -> &VerificationAlgorithm {
        &self.algorithm
    }
}

impl fmt::Debug for RsaVerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.rsa.fmt(f)
    }
}

/// A public key, bound to the one algorithm it verifies signatures with.
///
/// Its bytes are its encoding, as [`PublicKey::new`] takes it, but an RSA
/// key's are always its PKCS#1 `RSAPublicKey` DER.
pub struct PublicKey {
    key: Parsed,
    encoding: Buffer<MAX_PUBLIC_KEY_LEN>,
}

/// The longest public key encoding: ML-DSA-87's, longer than RSA's largest.
const MAX_PUBLIC_KEY_LEN: usize = max(rsa::MAX_PUBLIC_KEY_LEN, mldsa::public_key_len::<MlDsa87>());

/// The longest `SubjectPublicKeyInfo`: the longest key in a bit string,
/// after its algorithm identifier.
const MAX_SPKI_LEN: usize = MAX_PUBLIC_KEY_LEN + 32;

/// The longest PKCS#8 private key: RSA's, or an ML-DSA-87 key in its
/// expanded form.
const MAX_PKCS8_LEN: usize = max(rsa::MAX_PKCS8_LEN, MAX_ML_DSA_PRIVATE_KEY_LEN + 64);

const fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

#[allow(clippy::large_enum_variant)]
enum Parsed {
    EcdsaP256(EcdsaVerifier<P256>, Ecdsa),
    EcdsaP384(EcdsaVerifier<P384>, Ecdsa),
    EcdsaP521(EcdsaVerifier<P521>, Ecdsa),
    Rsa(RsaVerifier, RsaVerification),
    Ed25519(Verifier<Ed25519VerifyingKey>),
    MlDsa(MlDsaVerifier),
}

impl PublicKey {
    /// Parses a public key for `algorithm`, any `verify` constant,
    /// refusing a malformed key before any signature arrives.
    ///
    /// ECDSA keys are X9.62 uncompressed points, RSA keys are PKCS#1
    /// `RSAPublicKey` or `SubjectPublicKeyInfo` DER, Ed25519 keys are their
    /// 32 bytes, and ML-DSA keys are FIPS 204's encoding. A compressed ECDSA
    /// point is refused, which
    /// [`agreement::PublicKey::new`](crate::agreement::PublicKey::new)
    /// decompresses. So is an Ed25519 point of small order, which verifies
    /// signatures nobody made.
    pub fn new(algorithm: &impl AsRef<VerificationAlgorithm>, bytes: &[u8]) -> Result<Self, Error> {
        let key = match algorithm.as_ref().0 {
            Verification::Ecdsa(ecdsa, parse, _) => parse(ecdsa, bytes)?,
            Verification::Rsa(rsa) => return (rsa.parse)(rsa, bytes),
            Verification::Ed25519(parse) => parse(bytes)?,
            Verification::MlDsa(algorithm) => algorithm.parse(bytes)?,
        };
        Ok(Self {
            key,
            encoding: Buffer::copy_from(bytes)?,
        })
    }

    /// Loads an RSA key for `algorithm` from its big-endian modulus and
    /// exponent, as a JWK carries them.
    pub fn from_components(
        algorithm: &RsaVerificationAlgorithm,
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        let key = rsa::VerifyingKey::from_components(components.n.as_ref(), components.e.as_ref())?;
        Self::rsa(algorithm.rsa, key)
    }

    /// Parses a public key for `algorithm` from its `SubjectPublicKeyInfo`
    /// DER, refusing one that names another algorithm or curve.
    ///
    /// An ECDSA key names `id-ecPublicKey` and the algorithm's curve, and
    /// its point may be compressed (RFC 5480), which this decompresses. An
    /// RSA key names `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa`, an
    /// Ed25519 key `id-Ed25519`, and an ML-DSA key its parameter set's OID
    /// (RFC 9881).
    pub fn from_spki(
        algorithm: &impl AsRef<VerificationAlgorithm>,
        der: &[u8],
    ) -> Result<Self, Error> {
        match algorithm.as_ref().0 {
            Verification::Ecdsa(ecdsa, _, decompress) => {
                let curve = Some(asn1::Any::ObjectId(curve_oid(ecdsa.curve)));
                let point = spki::decode(der, &[&asn1::oid::id_ecPublicKey], curve)?;
                let mut decompressed = [0; MAX_UNCOMPRESSED_PUBLIC_KEY_LEN];
                Self::new(
                    algorithm,
                    sec1::uncompressed(point, decompress, &mut decompressed)?,
                )
            }
            // RSA's parser takes PKCS#1 too, which this refuses.
            Verification::Rsa(rsa) => {
                pkix::SubjectPublicKeyInfo::from_bytes(der).map_err(KeyFormatError::Asn1)?;
                (rsa.parse)(rsa, der)
            }
            Verification::Ed25519(_) => Self::new(
                algorithm,
                spki::decode(der, &[&asn1::oid::id_ed25519], None)?,
            ),
            Verification::MlDsa(ml_dsa) => {
                Self::new(algorithm, spki::decode(der, &[ml_dsa.oid], None)?)
            }
        }
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`: ECDSA's
    /// `id-ecPublicKey` on its curve, with its uncompressed point, RSA's
    /// `rsaEncryption`, Ed25519's `id-Ed25519`, or ML-DSA's parameter set.
    pub fn to_spki(&self) -> Spki {
        let ec = |curve| (&asn1::oid::id_ecPublicKey, Some(asn1::Any::ObjectId(curve)));
        let (algorithm, parameters) = match &self.key {
            Parsed::EcdsaP256(..) => ec(P256::oid()),
            Parsed::EcdsaP384(..) => ec(P384::oid()),
            Parsed::EcdsaP521(..) => ec(P521::oid()),
            Parsed::Rsa(..) => (&asn1::oid::rsaEncryption, Some(asn1::Any::Null(asn1::Null))),
            Parsed::Ed25519(_) => (&asn1::oid::id_ed25519, None),
            Parsed::MlDsa(key) => (key.algorithm.oid, None),
        };
        Spki(Buffer::encode(|output| {
            spki::encode(self.as_ref(), algorithm, parameters, output)
        }))
    }

    /// Parses an RSA key's PKCS#1 or SPKI DER for `rsa`.
    fn parse_rsa(rsa: Rsa, bytes: &[u8]) -> Result<Self, Error> {
        Self::rsa(rsa, rsa::VerifyingKey::from_der(bytes)?)
    }

    /// Binds an RSA key to `rsa`, refusing it below the algorithm's floor.
    ///
    /// The encoding is the key's PKCS#1 DER, whether it came as PKCS#1,
    /// SPKI, or components.
    fn rsa(rsa: Rsa, key: rsa::VerifyingKey) -> Result<Self, Error> {
        let key = rsa.check(key)?;
        Ok(Self {
            encoding: Buffer::write(|output| key.to_pkcs1_der(output))?,
            key: Parsed::Rsa(
                RsaVerifier {
                    key,
                    verify: rsa.verify,
                },
                rsa.verification,
            ),
        })
    }

    /// Verifies `signature` over `message`, refusing a malformed signature.
    ///
    /// ECDSA signatures are malleable: `(r, s)` and `(r, n - s)` both verify,
    /// unlike Ed25519, PKCS#1, and PSS signatures, so don't identify a message
    /// by its ECDSA signature's bytes.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        match &self.key {
            Parsed::EcdsaP256(key, _) => key.verify(message, signature),
            Parsed::EcdsaP384(key, _) => key.verify(message, signature),
            Parsed::EcdsaP521(key, _) => key.verify(message, signature),
            Parsed::Rsa(key, verification) => {
                (key.verify)(&key.key, verification.salt(), signature, message)
            }
            Parsed::Ed25519(key) => key.verify(message, signature),
            Parsed::MlDsa(key) => key.verify(self.as_ref(), message, signature),
        }
    }

    /// Verifies an ECDSA `signature` over the message `digest` hashes.
    ///
    /// The digest's hash, SHA-256, SHA-384, or SHA-512, replaces the
    /// algorithm's, which still fixes the curve and the signature's encoding.
    /// Another hash, or a key other than ECDSA, is refused as
    /// [`Error::Unsupported`].
    ///
    /// So unlike [`Self::verify`], this does not pin the hash: hash with the
    /// one your protocol names, never one the signed data or its sender
    /// picks. A signature over one SHA-2 hash verifies over another only
    /// for a message whose digest collides with it, which no one can find.
    pub fn verify_digest(&self, digest: &Digest, signature: &[u8]) -> Result<(), Error> {
        let digest = signed_digest(digest)?;
        match &self.key {
            Parsed::EcdsaP256(key, _) => key.verify_digest(digest, signature),
            Parsed::EcdsaP384(key, _) => key.verify_digest(digest, signature),
            Parsed::EcdsaP521(key, _) => key.verify_digest(digest, signature),
            Parsed::Rsa(..) | Parsed::Ed25519(_) | Parsed::MlDsa(_) => Err(Error::Unsupported),
        }
    }
}

#[cfg(any(test, rind_fips))]
impl PublicKey {
    /// An RSA key's modulus length in bits, or `None` for another kind of
    /// key: what the FIPS module checks against FIPS 186-5's sizes.
    pub(crate) fn rsa_modulus_bits(&self) -> Option<usize> {
        match &self.key {
            Parsed::Rsa(key, _) => Some(key.key.modulus_len_bits()),
            _ => None,
        }
    }
}

/// The bytes of `digest`, refused unless a signature takes its hash.
fn signed_digest(digest: &Digest) -> Result<&[u8], Error> {
    match digest.signs() {
        true => Ok(digest.as_ref()),
        false => Err(Error::Unsupported),
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.encoding.as_ref()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("PublicKey");
        match &self.key {
            Parsed::EcdsaP256(_, algorithm)
            | Parsed::EcdsaP384(_, algorithm)
            | Parsed::EcdsaP521(_, algorithm) => f.field("algorithm", algorithm),
            Parsed::Rsa(_, verification) => f.field("algorithm", verification),
            Parsed::Ed25519(_) => f.field("algorithm", &format_args!("Ed25519")),
            Parsed::MlDsa(key) => f.field("algorithm", &format_args!("{}", key.algorithm.name)),
        };
        f.field("bytes", &self.as_ref()).finish()
    }
}

/// A signature from any key pair.
#[derive(Clone, Copy)]
pub struct Signature(Buffer<SIGNATURE_MAX_LEN>);

// RSA's, as long as the largest modulus, is longer than any ECDSA DER
// signature: a `SEQUENCE`, whose length takes two bytes, of two P-521
// `INTEGER`s, each with a sign byte.
const SIGNATURE_MAX_LEN: usize = MAX_PUBLIC_MODULUS_BYTES;
const _: () = assert!(3 + 2 * (2 + MAX_SCALAR_LEN + 1) <= SIGNATURE_MAX_LEN);

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

/// A private key encoded as PKCS#8 DER, wiped on drop under the `wipe` feature.
pub struct Pkcs8(pub(super) Buffer<MAX_PKCS8_LEN>);

impl AsRef<[u8]> for Pkcs8 {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Pkcs8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Pkcs8").finish_non_exhaustive()
    }
}

impl Drop for Pkcs8 {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

/// A public key encoded as a `SubjectPublicKeyInfo` in DER.
#[derive(Clone)]
pub struct Spki(pub(super) Buffer<MAX_SPKI_LEN>);

impl AsRef<[u8]> for Spki {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Spki {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Spki").field(&self.as_ref()).finish()
    }
}

/// An ECDSA private key encoded as a SEC1 (RFC 5915) `ECPrivateKey` in
/// DER, wiped on drop under the `wipe` feature.
pub struct Sec1(Buffer<{ sec1::MAX_LEN }>);

impl AsRef<[u8]> for Sec1 {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Sec1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Sec1").finish_non_exhaustive()
    }
}

impl Drop for Sec1 {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

/// An ECDSA private key as a big-endian scalar exactly the curve's length,
/// wiped on drop under the `wipe` feature.
pub struct EcdsaScalar(Buffer<MAX_SCALAR_LEN>);

impl AsRef<[u8]> for EcdsaScalar {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for EcdsaScalar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EcdsaScalar").finish_non_exhaustive()
    }
}

impl Drop for EcdsaScalar {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

/// An Ed25519 private key as its 32-byte seed, wiped on drop under the `wipe` feature.
pub struct Ed25519Seed([u8; 32]);

impl AsRef<[u8]> for Ed25519Seed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Ed25519Seed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ed25519Seed").finish_non_exhaustive()
    }
}

impl Drop for Ed25519Seed {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

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

/// A curve's place in [`Parsed`] and [`EcdsaKey`].
trait EcdsaCurve: Curve<PublicKey: Clone> + Sized + 'static {
    fn parsed(key: EcdsaVerifier<Self>, ecdsa: Ecdsa) -> Parsed;

    fn key(pair: EcdsaPair<Self>) -> EcdsaKey;
}

macro_rules! ecdsa_curve {
    ($curve:ident, $parsed:ident) => {
        impl EcdsaCurve for $curve {
            fn parsed(key: EcdsaVerifier<Self>, ecdsa: Ecdsa) -> Parsed {
                Parsed::$parsed(key, ecdsa)
            }

            fn key(pair: EcdsaPair<Self>) -> EcdsaKey {
                EcdsaKey::$curve(pair)
            }
        }
    };
}

ecdsa_curve!(P256, EcdsaP256);
ecdsa_curve!(P384, EcdsaP384);
ecdsa_curve!(P521, EcdsaP521);

/// An ECDSA key and the functions that verify a message and a digest with
/// it, as [`Verifier`]'s.
struct EcdsaVerifier<C: Curve> {
    key: ecdsa::VerifyingKey<C>,
    verify: Verify<ecdsa::VerifyingKey<C>>,
    verify_digest: Verify<ecdsa::VerifyingKey<C>>,
}

impl<C: Curve> EcdsaVerifier<C> {
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.verify)(&self.key, signature, message)
    }

    fn verify_digest(&self, digest: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.verify_digest)(&self.key, signature, digest)
    }
}

fn parse_ecdsa<C: EcdsaCurve, H: SignatureHash, E: Encoding>(
    ecdsa: Ecdsa,
    bytes: &[u8],
) -> Result<Parsed, Error> {
    let key = EcdsaVerifier {
        key: ecdsa::VerifyingKey::from_x962_uncompressed(bytes)?,
        verify: E::verify::<C, H>,
        verify_digest: E::verify_digest::<C>,
    };
    Ok(C::parsed(key, ecdsa))
}

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
    VerificationAlgorithm(Verification::Ecdsa(ecdsa, parse, decompress))
}

/// The OID naming `curve`.
fn curve_oid(curve: CurveId) -> asn1::ObjectId {
    match curve {
        CurveId::P256 => P256::oid(),
        CurveId::P384 => P384::oid(),
        CurveId::P521 => P521::oid(),
    }
}

/// Signs as `verification` verifies, which must be ECDSA: checked when a
/// static is compiled, never at run time.
const fn ecdsa_signing(verification: &VerificationAlgorithm) -> EcdsaSigningAlgorithm {
    match verification.0 {
        Verification::Ecdsa(ecdsa, ..) => EcdsaSigningAlgorithm {
            ecdsa,
            load: with_ecdsa!(ecdsa, |C, H, E| EcdsaKeyPair::load::<C, H, E> as _),
        },
        _ => panic!("not an ECDSA algorithm"),
    }
}

/// An ECDSA signing algorithm, which an [`EcdsaKeyPair`] is bound to.
pub struct EcdsaSigningAlgorithm {
    ecdsa: Ecdsa,
    // The only path to the algorithm's code, as `Verification`'s.
    load: fn(Ecdsa, EcdsaSource<'_>) -> Result<EcdsaKeyPair, Error>,
}

impl fmt::Debug for EcdsaSigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EcdsaSigningAlgorithm")
            .field(&self.ecdsa)
            .finish()
    }
}

/// Where an [`EcdsaKeyPair`]'s private key comes from.
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
///
/// Generating one draws only the private key: the public key, which
/// signing never reads, is derived when it is first read, and kept.
pub struct EcdsaKeyPair {
    key: EcdsaKey,
    algorithm: Ecdsa,
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

/// A key pair on curve `C`, with the code that runs it, which it reaches
/// only through `ops`: matching on [`EcdsaKey`] then names no curve's code.
struct EcdsaPair<C: EcdsaCurve> {
    signing: ecdsa::SigningKey<C>,
    ops: low::ZeroableRef<EcdsaOps<C>>,
}

/// Writes to the start of an output and returns the written span.
type Write<K> = for<'a> fn(&K, &'a mut [u8]) -> Result<&'a [u8], Error>;

struct EcdsaOps<C: EcdsaCurve> {
    public_key: fn(&ecdsa::SigningKey<C>) -> ecdsa::EncodedPoint,
    parse: fn(&[u8]) -> Result<ecdsa::VerifyingKey<C>, Error>,
    sign: Sign<ecdsa::SigningKey<C>>,
    sign_digest: Sign<ecdsa::SigningKey<C>>,
    verify: Verify<ecdsa::VerifyingKey<C>>,
    verify_digest: Verify<ecdsa::VerifyingKey<C>>,
    to_pkcs8: Write<ecdsa::SigningKey<C>>,
    to_scalar: Write<ecdsa::SigningKey<C>>,
    to_spki: Write<ecdsa::SigningKey<C>>,
}

impl<C: EcdsaCurve> EcdsaPair<C> {
    fn point(&self) -> ecdsa::EncodedPoint {
        (self.ops.get().public_key)(&self.signing)
    }

    fn public_key(&self, ecdsa: Ecdsa) -> PublicKey {
        let point = self.point();
        let key = EcdsaVerifier {
            key: (self.ops.get().parse)(point.as_ref()).expect("a key pair's own point"),
            verify: self.ops.get().verify,
            verify_digest: self.ops.get().verify_digest,
        };
        PublicKey {
            key: C::parsed(key, ecdsa),
            encoding: Buffer::copy_from(point.as_ref()).expect("sized for the largest key"),
        }
    }
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

impl EcdsaKeyPair {
    /// Generates a key pair for `algorithm` from the system random source.
    pub fn generate(algorithm: &'static EcdsaSigningAlgorithm) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Generate)
    }

    /// Loads a PKCS#8 v1 `ECPrivateKey` on `algorithm`'s curve.
    pub fn from_pkcs8(
        algorithm: &'static EcdsaSigningAlgorithm,
        der: &[u8],
    ) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Pkcs8(der))
    }

    /// Loads a SEC1 (RFC 5915) `ECPrivateKey` on `algorithm`'s curve.
    ///
    /// This refuses PKCS#8, which [`Self::from_pkcs8`] takes: a caller always
    /// knows which of the two it holds.
    pub fn from_sec1(algorithm: &'static EcdsaSigningAlgorithm, der: &[u8]) -> Result<Self, Error> {
        (algorithm.load)(algorithm.ecdsa, EcdsaSource::Sec1(der))
    }

    /// Loads a fixed-length big-endian private scalar, refused unless
    /// `public_key`, an X9.62 uncompressed or compressed point, is its public
    /// key.
    ///
    /// This suits a JWK's `d` and `x`/`y`; prefer [`Self::from_pkcs8`] for
    /// stored keys.
    pub fn from_scalar_and_public_key(
        algorithm: &'static EcdsaSigningAlgorithm,
        scalar: &[u8],
        public_key: &[u8],
    ) -> Result<Self, Error> {
        let source = EcdsaSource::Scalar { scalar, public_key };
        (algorithm.load)(algorithm.ecdsa, source)
    }

    /// Loads a key pair for `ecdsa`, whose curve, hash, and encoding are `C`,
    /// `H`, and `E`.
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
        let ops = const {
            &EcdsaOps {
                public_key: ecdsa::SigningKey::public_key_uncompressed,
                parse: ecdsa::VerifyingKey::from_x962_uncompressed,
                sign: E::sign::<C, H>,
                sign_digest: E::sign_digest::<C, H>,
                verify: E::verify::<C, H>,
                verify_digest: E::verify_digest::<C>,
                to_pkcs8: ecdsa::SigningKey::to_pkcs8_der,
                to_scalar: ecdsa::SigningKey::to_scalar,
                to_spki: ecdsa::SigningKey::to_spki_der,
            }
        };
        Ok(Self {
            key: C::key(EcdsaPair {
                signing,
                ops: low::ZeroableRef::new(ops),
            }),
            algorithm: ecdsa,
        })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        on_ecdsa!(self, |pair| pair.public_key(self.algorithm))
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
    /// [`Self::public_key`] verifies the signature over the message only if
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
    pub fn to_scalar(&self) -> EcdsaScalar {
        EcdsaScalar(Buffer::encode(|output| {
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
        let scalar = self.to_scalar();
        let point = on_ecdsa!(self, |pair| pair.point());
        let curve = curve_oid(self.algorithm.curve);
        Sec1(Buffer::encode(|output| {
            sec1::encode(scalar.as_ref(), point.as_ref(), Some(curve), output)
        }))
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            on_ecdsa!(self, |pair| (pair.ops.get().to_spki)(&pair.signing, output))
        }))
    }
}

impl fmt::Debug for EcdsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let point = on_ecdsa!(self, |pair| pair.point());
        f.debug_struct("EcdsaKeyPair")
            .field("algorithm", &self.algorithm)
            .field("public_key", &point.as_ref())
            .finish_non_exhaustive()
    }
}

// Every field is plain words or a `repr(u8)` enum with a variant at zero.
impl Zeroable for EcdsaKeyPair {}

impl Drop for EcdsaKeyPair {
    fn drop(&mut self) {
        // Wipes the scalar, which the curve's key leaves to its owner. Wiping
        // the rest, which is not secret, lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(self);
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum RsaPadding {
    /// RSASSA-PKCS1-v1_5.
    Pkcs1,
    /// RSASSA-PSS, with MGF1 on the same hash and a salt of this length.
    Pss(PssSalt),
}

#[derive(Clone, Copy, Debug)]
struct RsaScheme {
    padding: RsaPadding,
    hash: HashId,
}

/// Signs with an RSA key, taking a PSS salt length that PKCS#1 v1.5
/// ignores: `(key, salt, output, message)`.
type RsaSign =
    for<'a> fn(&rsa::SigningKey, PssSalt, &'a mut [u8], &[u8]) -> Result<&'a [u8], Error>;

/// Verifies with an RSA key, taking a PSS salt length, or `None` for any,
/// that PKCS#1 v1.5 ignores: `(key, salt, signature, message)`.
type RsaVerify = fn(&rsa::VerifyingKey, Option<PssSalt>, &[u8], &[u8]) -> Result<(), Error>;

/// An RSA key and the function that verifies with it, as [`Verifier`]'s.
struct RsaVerifier {
    key: rsa::VerifyingKey,
    verify: RsaVerify,
}

// Only constant functions call these, so a static names only its own
// scheme's code, as `with_ecdsa!` does.
impl RsaScheme {
    const fn pss(hash: HashId, salt: PssSalt) -> Self {
        Self {
            padding: RsaPadding::Pss(salt),
            hash,
        }
    }

    /// The PSS salt length, which PKCS#1 v1.5 ignores.
    const fn salt(self) -> PssSalt {
        match self.padding {
            RsaPadding::Pkcs1 => PssSalt::Hash,
            RsaPadding::Pss(salt) => salt,
        }
    }

    const fn signer(self) -> RsaSign {
        match (self.padding, self.hash) {
            (RsaPadding::Pkcs1, HashId::Sha256) => |key, _, out, m| key.sign_pkcs1_sha256(out, m),
            (RsaPadding::Pkcs1, HashId::Sha384) => |key, _, out, m| key.sign_pkcs1_sha384(out, m),
            (RsaPadding::Pkcs1, HashId::Sha512) => |key, _, out, m| key.sign_pkcs1_sha512(out, m),
            (RsaPadding::Pss(_), HashId::Sha256) => rsa::SigningKey::sign_pss_sha256,
            (RsaPadding::Pss(_), HashId::Sha384) => rsa::SigningKey::sign_pss_sha384,
            (RsaPadding::Pss(_), HashId::Sha512) => rsa::SigningKey::sign_pss_sha512,
        }
    }

    const fn verifier(self) -> RsaVerify {
        match (self.padding, self.hash) {
            (RsaPadding::Pkcs1, HashId::Sha256) => |key, _, s, m| key.verify_pkcs1_sha256(s, m),
            (RsaPadding::Pkcs1, HashId::Sha384) => |key, _, s, m| key.verify_pkcs1_sha384(s, m),
            (RsaPadding::Pkcs1, HashId::Sha512) => |key, _, s, m| key.verify_pkcs1_sha512(s, m),
            (RsaPadding::Pss(_), HashId::Sha256) => rsa::VerifyingKey::verify_pss_sha256,
            (RsaPadding::Pss(_), HashId::Sha384) => rsa::VerifyingKey::verify_pss_sha384,
            (RsaPadding::Pss(_), HashId::Sha512) => rsa::VerifyingKey::verify_pss_sha512,
        }
    }

    /// The smallest modulus whose PSS encoding fits the salt, if over
    /// `min_bits`: RFC 8017 section 9.1.1 needs `ceil((bits - 1) / 8)`
    /// bytes for the hash, the salt, and two more.
    const fn min_bits(self, min_bits: usize) -> usize {
        let salt = match self.padding {
            RsaPadding::Pkcs1 => return min_bits,
            RsaPadding::Pss(PssSalt::Hash) => self.hash.len(),
            RsaPadding::Pss(PssSalt::Max) => 0,
            RsaPadding::Pss(PssSalt::Len(len)) => len as usize,
        };
        let fits = 8 * (self.hash.len() + salt + 1) + 2;
        if fits > min_bits { fits } else { min_bits }
    }
}

/// How long an RSASSA-PSS salt is, beside the hash's length that the
/// `RSA_PSS_*` algorithms use.
///
/// A signature verifies only with the salt length it was made with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RsaPssSaltLength {
    /// The longest the modulus allows: the encoded message's length, a byte
    /// shorter than the modulus when its bit length is one more than a
    /// multiple of eight, less the hash's length and two.
    Max,
    /// This many bytes. A modulus too short for them is refused when a key
    /// is parsed for verifying or used for signing, not here.
    Custom(u16),
}

impl RsaPssSaltLength {
    const fn salt(self) -> PssSalt {
        match self {
            Self::Max => PssSalt::Max,
            Self::Custom(len) => PssSalt::Len(len),
        }
    }
}

/// What an RSA verification algorithm verifies: a scheme rind also signs
/// with, or PKCS#1 v1.5 with SHA-1 or PSS with any salt length, which it
/// only verifies.
#[derive(Clone, Copy, Debug)]
enum RsaVerification {
    Scheme(RsaScheme),
    Pkcs1Sha1,
    PssAnySalt(HashId),
}

impl RsaVerification {
    const fn verifier(self) -> RsaVerify {
        match self {
            Self::Scheme(scheme) => scheme.verifier(),
            Self::Pkcs1Sha1 => |key, _, s, m| key.verify_pkcs1_sha1(s, m),
            Self::PssAnySalt(hash) => RsaScheme::pss(hash, PssSalt::Hash).verifier(),
        }
    }

    /// The PSS salt length to verify, `None` for any.
    fn salt(self) -> Option<PssSalt> {
        match self {
            Self::Scheme(scheme) => Some(scheme.salt()),
            Self::Pkcs1Sha1 | Self::PssAnySalt(_) => None,
        }
    }
}

/// An RSA verification algorithm: a padding, a hash, and the smallest
/// modulus it accepts, with the functions that are the only paths to its
/// code, as `Verification`'s.
#[derive(Clone, Copy)]
struct Rsa {
    verification: RsaVerification,
    min_bits: usize,
    verify: RsaVerify,
    parse: fn(Self, &[u8]) -> Result<PublicKey, Error>,
}

impl fmt::Debug for Rsa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Rsa")
            .field("verification", &self.verification)
            .field("min_bits", &self.min_bits)
            .finish()
    }
}

impl Rsa {
    /// Refuses `key` if its modulus is below this algorithm's floor.
    fn check(self, key: rsa::VerifyingKey) -> Result<rsa::VerifyingKey, Error> {
        match key.modulus_len_bits() >= self.min_bits {
            true => Ok(key),
            false => Err(KeyFormatError::RsaModulus.into()),
        }
    }
}

const fn rsa_verification(scheme: RsaScheme, min_bits: usize) -> RsaVerificationAlgorithm {
    rsa_algorithm(RsaVerification::Scheme(scheme), scheme.min_bits(min_bits))
}

const fn rsa_sha1_verification(min_bits: usize) -> RsaVerificationAlgorithm {
    rsa_algorithm(RsaVerification::Pkcs1Sha1, min_bits)
}

const fn rsa_algorithm(verification: RsaVerification, min_bits: usize) -> RsaVerificationAlgorithm {
    let rsa = Rsa {
        verification,
        min_bits,
        verify: verification.verifier(),
        parse: PublicKey::parse_rsa,
    };
    RsaVerificationAlgorithm {
        rsa,
        algorithm: VerificationAlgorithm(Verification::Rsa(rsa)),
    }
}

/// An RSA public key as its big-endian modulus and exponent, as a JWK
/// carries it, rather than DER.
#[derive(Clone, Copy, Debug)]
pub struct PublicKeyComponents<B> {
    /// The modulus, without leading zero bytes.
    pub n: B,
    /// The public exponent, without leading zero bytes.
    pub e: B,
}

/// An RSA signing algorithm: a padding and a hash, for [`RsaKeyPair::sign`].
pub struct RsaSigningAlgorithm {
    scheme: RsaScheme,
    // The only paths to the scheme's code, as `Verification`'s.
    sign: RsaSign,
    verify: RsaVerify,
}

impl RsaSigningAlgorithm {
    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt of `salt_length`.
    pub const fn pss_sha256(salt_length: RsaPssSaltLength) -> Self {
        rsa_signing(RsaScheme::pss(HashId::Sha256, salt_length.salt()))
    }

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt of `salt_length`.
    pub const fn pss_sha384(salt_length: RsaPssSaltLength) -> Self {
        rsa_signing(RsaScheme::pss(HashId::Sha384, salt_length.salt()))
    }

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt of `salt_length`.
    pub const fn pss_sha512(salt_length: RsaPssSaltLength) -> Self {
        rsa_signing(RsaScheme::pss(HashId::Sha512, salt_length.salt()))
    }
}

impl RsaVerificationAlgorithm {
    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt of `salt_length`,
    /// for moduli of 2048 to 8192 bits long enough for it.
    pub const fn pss_sha256(salt_length: RsaPssSaltLength) -> Self {
        rsa_verification(
            RsaScheme::pss(HashId::Sha256, salt_length.salt()),
            RSA_MIN_BITS,
        )
    }

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt of `salt_length`,
    /// for moduli of 2048 to 8192 bits long enough for it.
    pub const fn pss_sha384(salt_length: RsaPssSaltLength) -> Self {
        rsa_verification(
            RsaScheme::pss(HashId::Sha384, salt_length.salt()),
            RSA_MIN_BITS,
        )
    }

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt of `salt_length`,
    /// for moduli of 2048 to 8192 bits long enough for it.
    pub const fn pss_sha512(salt_length: RsaPssSaltLength) -> Self {
        rsa_verification(
            RsaScheme::pss(HashId::Sha512, salt_length.salt()),
            RSA_MIN_BITS,
        )
    }
}

impl fmt::Debug for RsaSigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("RsaSigningAlgorithm")
            .field(&self.scheme)
            .finish()
    }
}

const fn rsa_signing(scheme: RsaScheme) -> RsaSigningAlgorithm {
    RsaSigningAlgorithm {
        scheme,
        sign: scheme.signer(),
        verify: scheme.verifier(),
    }
}

const PKCS1_SHA256: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha256,
};
const PKCS1_SHA384: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha384,
};
const PKCS1_SHA512: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha512,
};
const PSS_SHA256: RsaScheme = RsaScheme::pss(HashId::Sha256, PssSalt::Hash);
const PSS_SHA384: RsaScheme = RsaScheme::pss(HashId::Sha384, PssSalt::Hash);
const PSS_SHA512: RsaScheme = RsaScheme::pss(HashId::Sha512, PssSalt::Hash);

/// The smallest modulus a verification algorithm accepts, unless it is
/// under [`verify::legacy`], and the smallest a key pair loads.
pub(super) const RSA_MIN_BITS: usize = 2048;

/// A two-prime RSA private key, with a modulus of 2048 to 8192 bits, and its public key.
pub struct RsaKeyPair {
    key: rsa::SigningKey,
    public_key: RsaPublicKeyDer,
}

/// The public key's PKCS#1 DER.
// The empty array aligns it like the private key's `u64` words (to 8 bytes on
// armv7, 4 on i686), so the key pair's padding falls inside this value, which
// `RsaKeyPair`'s drop wipes whole, rather than after it, where
// `tests/zeroing.rs` finds stale bytes.
#[derive(Clone, Copy)]
struct RsaPublicKeyDer(Buffer<{ rsa::MAX_PUBLIC_KEY_LEN }>, [u64; 0]);

impl Zeroable for RsaPublicKeyDer {}

impl RsaKeyPair {
    /// Generates a key pair of `size` from the system random source.
    ///
    /// This is slow: about 30 milliseconds for 2048 bits, and 15 seconds or
    /// more for 8192 bits, with no upper bound. Its timing reveals only which
    /// candidate primes it discards.
    pub fn generate(size: RsaKeySize) -> Result<Self, Error> {
        Self::new(rsa::SigningKey::generate(size)?)
    }

    /// Loads a PKCS#8 v1 RSA private key, named `rsaEncryption`,
    /// `id-RSAES-OAEP`, or `id-ea-rsa`.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        Self::new(rsa::SigningKey::from_pkcs8_der(der)?)
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_pkcs1(der: &[u8]) -> Result<Self, Error> {
        Self::new(rsa::SigningKey::from_pkcs1_der(der)?)
    }

    fn new(key: rsa::SigningKey) -> Result<Self, Error> {
        let public_key = Buffer::write(|output| key.public_key().to_pkcs1_der(output))?;
        Ok(Self {
            key,
            public_key: RsaPublicKeyDer(public_key, []),
        })
    }

    /// Returns the public key, which verifies what this key pair signs with
    /// `algorithm`.
    ///
    /// Unlike an ECDSA key pair, an RSA key pair signs with any padding and
    /// hash, so the public key needs the one it verifies.
    pub fn public_key(&self, algorithm: &RsaSigningAlgorithm) -> PublicKey {
        // A key pair's modulus is at least `RSA_MIN_BITS`, the floor of the
        // algorithm that verifies `algorithm`'s signatures. A PSS salt too
        // long for the modulus raises that floor, which this does not check:
        // `sign` refuses such a salt, and this key refuses every signature,
        // as EMSA-PSS-VERIFY refuses the length.
        PublicKey {
            key: Parsed::Rsa(
                RsaVerifier {
                    key: self.key.public_key(),
                    verify: algorithm.verify,
                },
                RsaVerification::Scheme(algorithm.scheme),
            ),
            encoding: self.public_key.0.widen(),
        }
    }

    /// Signs `message` with `algorithm`, as long as the modulus.
    ///
    /// A PSS salt too long for the modulus is refused as the key's size.
    pub fn sign(
        &self,
        algorithm: &RsaSigningAlgorithm,
        message: &[u8],
    ) -> Result<Signature, Error> {
        Buffer::write(|output| {
            let output = output
                .get_mut(..self.key.modulus_len_bytes())
                .ok_or(Error::WrongLength)?;
            (algorithm.sign)(&self.key, algorithm.scheme.salt(), output, message)
        })
        .map(Signature)
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(output)))
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            self.key.public_key().to_spki_der(output)
        }))
    }
}

impl fmt::Debug for RsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RsaKeyPair")
            .field("public_key", &self.public_key.0.as_ref())
            .finish_non_exhaustive()
    }
}

impl Drop for RsaKeyPair {
    fn drop(&mut self) {
        // Not secret, but wiping it lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(&mut self.public_key);
    }
}

/// An Ed25519 private key and its public key.
pub struct Ed25519KeyPair {
    key: Ed25519SigningKey,
    public_key: [u8; 32],
}

impl Ed25519KeyPair {
    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::generate()?))
    }

    /// Loads a PKCS#8 Ed25519 key, refused if it carries a public key
    /// (v2, RFC 5958) that does not match.
    ///
    /// This also takes PKCS#8 v1, which carries no public key: common tools
    /// write v1, and such a key is no less valid.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::from_pkcs8_der(der)?))
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    ///
    /// Prefer [`Self::from_seed_and_public_key`] when the public key is at
    /// hand, which checks it.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(Ed25519SigningKey::from_bytes(seed)?))
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    ///
    /// This suits a JWK's `d` and `x`.
    pub fn from_seed_and_public_key(seed: &[u8], public_key: &[u8]) -> Result<Self, Error> {
        let pair = Self::new(Ed25519SigningKey::from_bytes(seed)?);
        match pair.public_key.as_slice() == public_key {
            true => Ok(pair),
            false => Err(KeyFormatError::MismatchedPublicKey.into()),
        }
    }

    fn new(key: Ed25519SigningKey) -> Self {
        let public_key = key.public_key().as_bytes();
        Self { key, public_key }
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        PublicKey {
            key: Parsed::Ed25519(Verifier {
                key: self.key.public_key(),
                verify: Ed25519VerifyingKey::verify,
            }),
            encoding: Buffer::from(self.public_key).widen(),
        }
    }

    /// Signs `message`.
    pub fn sign(&self, message: &[u8]) -> Signature {
        Signature(Buffer::from(self.key.sign(message)).widen())
    }

    /// Encodes the key pair as PKCS#8 v2 (RFC 5958).
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(true, output)))
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 8410), its seed without its
    /// public key, as OpenSSL and BoringSSL write it.
    pub fn to_pkcs8v1(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| {
            self.key.to_pkcs8_der(false, output)
        }))
    }

    /// Returns the private key's 32-byte seed, as a JWK's `d` holds it.
    ///
    /// This is what [`Self::from_seed_and_public_key`] loads; prefer
    /// [`Self::to_pkcs8`] for stored keys.
    pub fn to_seed(&self) -> Ed25519Seed {
        Ed25519Seed(*self.key.seed())
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            self.key.public_key().to_spki_der(output)
        }))
    }
}

impl fmt::Debug for Ed25519KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ed25519KeyPair")
            .field("public_key", &self.public_key)
            .finish_non_exhaustive()
    }
}

impl Drop for Ed25519KeyPair {
    fn drop(&mut self) {
        // Not secret, but wiping it lets `tests/zeroing.rs` check every byte.
        low::zeroise(&mut self.public_key);
    }
}

fn parse_ed25519(bytes: &[u8]) -> Result<Parsed, Error> {
    Ok(Parsed::Ed25519(Verifier {
        key: Ed25519VerifyingKey::from_bytes(bytes)?,
        verify: Ed25519VerifyingKey::verify,
    }))
}

/// An ML-DSA parameter set, as FIPS 204 standardises them: [`MlDsa44`],
/// [`MlDsa65`], or [`MlDsa87`], which fixes the sizes of its keys and
/// signatures.
pub trait MlDsaParameterSet: MlDsaParams {
    #[doc(hidden)]
    const ALGORITHM: MlDsaAlgorithm;
}

impl MlDsaParameterSet for MlDsa44 {
    const ALGORITHM: MlDsaAlgorithm =
        MlDsaAlgorithm::new::<Self>("ML-DSA-44", &asn1::oid::id_ml_dsa_44);
}

impl MlDsaParameterSet for MlDsa65 {
    const ALGORITHM: MlDsaAlgorithm =
        MlDsaAlgorithm::new::<Self>("ML-DSA-65", &asn1::oid::id_ml_dsa_65);
}

impl MlDsaParameterSet for MlDsa87 {
    const ALGORITHM: MlDsaAlgorithm =
        MlDsaAlgorithm::new::<Self>("ML-DSA-87", &asn1::oid::id_ml_dsa_87);
}

/// An ML-DSA parameter set's name, its OID (RFC 9881), and the function that
/// verifies its signatures.
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct MlDsaAlgorithm {
    name: &'static str,
    oid: &'static asn1::ObjectId,
    public_key_len: usize,
    verify: MlDsaVerify,
}

/// Verifies with an ML-DSA public key and its hash `tr`:
/// `(key, tr, message, signature)`.
type MlDsaVerify = fn(&[u8], &[u8; mldsa::TR_LEN], &[u8], &[u8]) -> Result<(), Error>;

impl MlDsaAlgorithm {
    const fn new<P: MlDsaParams>(name: &'static str, oid: &'static asn1::ObjectId) -> Self {
        Self {
            name,
            oid,
            public_key_len: mldsa::public_key_len::<P>(),
            // Pure ML-DSA with the empty context, as TLS and X.509 sign.
            verify: |pk, tr, message, signature| {
                mldsa::verify::<P>(pk, tr, &[], message, signature)
            },
        }
    }

    /// Parses a public key: any encoding of the right length is one.
    fn parse(self, bytes: &[u8]) -> Result<Parsed, Error> {
        match bytes.len() == self.public_key_len {
            true => Ok(Parsed::MlDsa(MlDsaVerifier {
                algorithm: self,
                tr: mldsa::tr(bytes),
            })),
            false => Err(KeyFormatError::WrongLength.into()),
        }
    }
}

/// An ML-DSA public key's algorithm and hash `tr`, which every signature it
/// verifies binds in. Its encoding is the [`PublicKey`]'s.
struct MlDsaVerifier {
    algorithm: MlDsaAlgorithm,
    tr: [u8; mldsa::TR_LEN],
}

impl MlDsaVerifier {
    fn verify(&self, public_key: &[u8], message: &[u8], signature: &[u8]) -> Result<(), Error> {
        (self.algorithm.verify)(public_key, &self.tr, message, signature)
    }
}

/// The longest ML-DSA private key, ML-DSA-87's expanded form in its
/// `OCTET STRING`.
const MAX_ML_DSA_PRIVATE_KEY_LEN: usize = mldsa::secret_key_len::<MlDsa87>() + 4;

/// An ML-DSA private key and its public key, of parameter set `P`.
///
/// It signs pure ML-DSA (FIPS 204) with the empty context, as TLS and X.509
/// use it, hedged with fresh randomness, as [`verify::ML_DSA_44`],
/// [`verify::ML_DSA_65`], and [`verify::ML_DSA_87`] verify.
///
/// It keeps FIPS 204's encodings, expanding them as each signature needs, as
/// mldsa-native and aws-lc do.
pub struct MlDsaKeyPair<P: MlDsaParameterSet>(mldsa::KeyPair<P>);

impl<P: MlDsaParameterSet> MlDsaKeyPair<P> {
    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Error> {
        mldsa::KeyPair::generate().map(Self)
    }

    /// Expands a 32-byte seed, FIPS 204's `xi`, into its key pair.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        let seed = seed.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        Ok(Self(mldsa::KeyPair::from_seed(seed)))
    }

    /// Returns the private key's 32-byte seed, which [`Self::from_seed`]
    /// loads, unless the key was loaded from its expanded form, which has
    /// none.
    pub fn to_seed(&self) -> Option<MlDsaSeed> {
        self.0.seed().map(|seed| MlDsaSeed(*seed))
    }

    /// Loads a PKCS#8 ML-DSA key (RFC 9881), refused if it carries a public
    /// key (v2, RFC 5958) that does not match.
    ///
    /// Its private key may be any of RFC 9881's forms: the seed, the expanded
    /// key, which must be consistent as FIPS 204's key generation writes it,
    /// or both, which must agree.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let p8 = pkcs8::Key::decode(der, &[P::ALGORITHM.oid], None)?;
        let private_key =
            pkix::MlDsaPrivateKey::from_bytes(p8.private_key()).map_err(KeyFormatError::Asn1)?;
        let key = match private_key {
            pkix::MlDsaPrivateKey::Seed(seed) => Self::from_seed(seed.as_octets())?,
            pkix::MlDsaPrivateKey::ExpandedKey(key) => {
                Self(mldsa::KeyPair::from_secret_key(key.as_octets())?)
            }
            pkix::MlDsaPrivateKey::Both(both) => {
                let key = Self::from_seed(both.seed.as_octets())?;
                let expanded = key.0.secret_key().as_ref();
                if !low::ct::into_public(low::ct_equal(expanded, both.expandedKey.as_octets())) {
                    return Err(KeyFormatError::MismatchedMlDsaSeed.into());
                }
                key
            }
        };
        match p8.public_key() {
            Some(public_key) if public_key != key.0.public_key().as_ref() => {
                Err(KeyFormatError::MismatchedPkcs8PublicKey.into())
            }
            _ => Ok(key),
        }
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 9881): its seed, as aws-lc
    /// writes it, or its expanded form if it was loaded from that and has no
    /// seed.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        let _entry = low::Entry::new_secret();
        let private_key = match self.0.seed() {
            Some(seed) => pkix::MlDsaPrivateKey::Seed(asn1::OctetString::new(seed)),
            None => pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(
                self.0.secret_key().as_ref(),
            )),
        };
        let mut private_key_buf = [0u8; MAX_ML_DSA_PRIVATE_KEY_LEN];
        let len = private_key
            .encode(&mut asn1::Encoder::new(&mut private_key_buf))
            .expect("sized for the largest key");
        let pkcs8 = Pkcs8(Buffer::encode(|output| {
            pkcs8::Key::construct(
                &private_key_buf[..len],
                None,
                P::ALGORITHM.oid.clone(),
                None,
            )
            .encode(output)
        }));
        low::ct::public_slice(pkcs8.as_ref());
        pkcs8
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> PublicKey {
        // `tr` is the public key's hash, which the private key stores.
        let tr = low::ct::into_public(*self.0.tr());
        PublicKey {
            key: Parsed::MlDsa(MlDsaVerifier {
                algorithm: P::ALGORITHM,
                tr,
            }),
            encoding: Buffer::encode(|output| {
                let public_key = self.0.public_key().as_ref();
                let output = &mut output[..public_key.len()];
                output.copy_from_slice(public_key);
                Ok(output)
            }),
        }
    }

    /// Signs `message`, with fresh randomness from the system random source.
    pub fn sign(&self, message: &[u8]) -> Result<MlDsaSignature<P>, Error> {
        self.0.sign(&[], message).map(MlDsaSignature)
    }
}

impl<P: MlDsaParameterSet> fmt::Debug for MlDsaKeyPair<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MlDsaKeyPair")
            .field("algorithm", &format_args!("{}", P::ALGORITHM.name))
            .finish_non_exhaustive()
    }
}

/// An ML-DSA signature of parameter set `P`, FIPS 204's encoding.
pub struct MlDsaSignature<P: MlDsaParameterSet>(P::Signature);

impl<P: MlDsaParameterSet> Clone for MlDsaSignature<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: MlDsaParameterSet> AsRef<[u8]> for MlDsaSignature<P> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<P: MlDsaParameterSet> fmt::Debug for MlDsaSignature<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MlDsaSignature")
            .field(&self.as_ref())
            .finish()
    }
}

/// An ML-DSA private key's 32-byte seed, wiped on drop under the `wipe`
/// feature.
pub struct MlDsaSeed([u8; mldsa::SEED_LEN]);

impl AsRef<[u8]> for MlDsaSeed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for MlDsaSeed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MlDsaSeed").finish_non_exhaustive()
    }
}

impl Drop for MlDsaSeed {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

/// Algorithms a key pair signs with.
pub(crate) mod sign {
    use super::*;

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P256_SHA256_ASN1: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P256_SHA256_ASN1);

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P384_SHA384_ASN1: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P384_SHA384_ASN1);

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P521_SHA512_ASN1: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P521_SHA512_ASN1);

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static ECDSA_P256_SHA256_FIXED: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P256_SHA256_FIXED);

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static ECDSA_P384_SHA384_FIXED: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P384_SHA384_FIXED);

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static ECDSA_P521_SHA512_FIXED: EcdsaSigningAlgorithm =
        ecdsa_signing(&verify::ECDSA_P521_SHA512_FIXED);

    /// RSASSA-PKCS1-v1_5 with SHA-256.
    pub static RSA_PKCS1_SHA256: RsaSigningAlgorithm = rsa_signing(PKCS1_SHA256);

    /// RSASSA-PKCS1-v1_5 with SHA-384.
    pub static RSA_PKCS1_SHA384: RsaSigningAlgorithm = rsa_signing(PKCS1_SHA384);

    /// RSASSA-PKCS1-v1_5 with SHA-512.
    pub static RSA_PKCS1_SHA512: RsaSigningAlgorithm = rsa_signing(PKCS1_SHA512);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt.
    pub static RSA_PSS_SHA256: RsaSigningAlgorithm = rsa_signing(PSS_SHA256);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt.
    pub static RSA_PSS_SHA384: RsaSigningAlgorithm = rsa_signing(PSS_SHA384);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt.
    pub static RSA_PSS_SHA512: RsaSigningAlgorithm = rsa_signing(PSS_SHA512);
}

/// Algorithms a public key verifies with.
pub(crate) mod verify {
    use super::*;

    /// ECDSA on P-256 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P256_SHA256_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha256, EcdsaEncoding::Asn1);

    /// ECDSA on P-256 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P256_SHA384_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha384, EcdsaEncoding::Asn1);

    /// ECDSA on P-256 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P256_SHA512_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha512, EcdsaEncoding::Asn1);

    /// ECDSA on P-384 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P384_SHA256_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha256, EcdsaEncoding::Asn1);

    /// ECDSA on P-384 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P384_SHA384_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha384, EcdsaEncoding::Asn1);

    /// ECDSA on P-384 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P384_SHA512_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha512, EcdsaEncoding::Asn1);

    /// ECDSA on P-521 with SHA-256, ASN.1 signatures.
    pub static ECDSA_P521_SHA256_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha256, EcdsaEncoding::Asn1);

    /// ECDSA on P-521 with SHA-384, ASN.1 signatures.
    pub static ECDSA_P521_SHA384_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha384, EcdsaEncoding::Asn1);

    /// ECDSA on P-521 with SHA-512, ASN.1 signatures.
    pub static ECDSA_P521_SHA512_ASN1: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha512, EcdsaEncoding::Asn1);

    /// ECDSA on P-256 with SHA-256, fixed-length `r || s` signatures (JWS's ES256).
    pub static ECDSA_P256_SHA256_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P256, HashId::Sha256, EcdsaEncoding::Fixed);

    /// ECDSA on P-384 with SHA-384, fixed-length `r || s` signatures (JWS's ES384).
    pub static ECDSA_P384_SHA384_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P384, HashId::Sha384, EcdsaEncoding::Fixed);

    /// ECDSA on P-521 with SHA-512, fixed-length `r || s` signatures (JWS's ES512).
    pub static ECDSA_P521_SHA512_FIXED: VerificationAlgorithm =
        ecdsa_verification(CurveId::P521, HashId::Sha512, EcdsaEncoding::Fixed);

    /// RSASSA-PKCS1-v1_5 with SHA-256, for moduli of 2048 to 8192 bits.
    pub static RSA_PKCS1_SHA256: RsaVerificationAlgorithm =
        rsa_verification(PKCS1_SHA256, RSA_MIN_BITS);

    /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 2048 to 8192 bits.
    pub static RSA_PKCS1_SHA384: RsaVerificationAlgorithm =
        rsa_verification(PKCS1_SHA384, RSA_MIN_BITS);

    /// RSASSA-PKCS1-v1_5 with SHA-512, for moduli of 2048 to 8192 bits.
    pub static RSA_PKCS1_SHA512: RsaVerificationAlgorithm =
        rsa_verification(PKCS1_SHA512, RSA_MIN_BITS);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA256: RsaVerificationAlgorithm =
        rsa_verification(PSS_SHA256, RSA_MIN_BITS);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA384: RsaVerificationAlgorithm =
        rsa_verification(PSS_SHA384, RSA_MIN_BITS);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA512: RsaVerificationAlgorithm =
        rsa_verification(PSS_SHA512, RSA_MIN_BITS);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt of any length, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA256_ANY_SALT: RsaVerificationAlgorithm =
        rsa_algorithm(RsaVerification::PssAnySalt(HashId::Sha256), RSA_MIN_BITS);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt of any length, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA384_ANY_SALT: RsaVerificationAlgorithm =
        rsa_algorithm(RsaVerification::PssAnySalt(HashId::Sha384), RSA_MIN_BITS);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt of any length, for moduli of 2048 to 8192 bits.
    pub static RSA_PSS_SHA512_ANY_SALT: RsaVerificationAlgorithm =
        rsa_algorithm(RsaVerification::PssAnySalt(HashId::Sha512), RSA_MIN_BITS);

    /// Ed25519, with 32-byte public keys and 64-byte signatures.
    ///
    /// See [RFC8032](https://datatracker.ietf.org/doc/html/rfc8032).
    pub static ED25519: VerificationAlgorithm =
        VerificationAlgorithm(Verification::Ed25519(parse_ed25519));

    /// ML-DSA-44 (FIPS 204), pure with the empty context: 1312-byte public
    /// keys and 2420-byte signatures.
    pub static ML_DSA_44: VerificationAlgorithm =
        VerificationAlgorithm(Verification::MlDsa(MlDsa44::ALGORITHM));

    /// ML-DSA-65 (FIPS 204), pure with the empty context: 1952-byte public
    /// keys and 3309-byte signatures.
    pub static ML_DSA_65: VerificationAlgorithm =
        VerificationAlgorithm(Verification::MlDsa(MlDsa65::ALGORITHM));

    /// ML-DSA-87 (FIPS 204), pure with the empty context: 2592-byte public
    /// keys and 4627-byte signatures.
    pub static ML_DSA_87: VerificationAlgorithm =
        VerificationAlgorithm(Verification::MlDsa(MlDsa87::ALGORITHM));

    /// Verification algorithms with a modulus floor other than 2048 bits, or SHA-1.
    pub(crate) mod legacy {
        use super::super::*;

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures only: SHA-1 collisions are practical.
        pub static RSA_PKCS1_SHA1: RsaVerificationAlgorithm = rsa_sha1_verification(RSA_MIN_BITS);

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures by keys with moduli down to 1024 bits.
        pub static RSA_PKCS1_1024_SHA1: RsaVerificationAlgorithm = rsa_sha1_verification(1024);

        /// RSASSA-PKCS1-v1_5 with SHA-256, for old keys with moduli down to 1024 bits.
        pub static RSA_PKCS1_1024_SHA256: RsaVerificationAlgorithm =
            rsa_verification(PKCS1_SHA256, 1024);

        /// RSASSA-PKCS1-v1_5 with SHA-512, for old keys with moduli down to 1024 bits.
        pub static RSA_PKCS1_1024_SHA512: RsaVerificationAlgorithm =
            rsa_verification(PKCS1_SHA512, 1024);

        /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 3072 to 8192 bits.
        pub static RSA_PKCS1_3072_SHA384: RsaVerificationAlgorithm =
            rsa_verification(PKCS1_SHA384, 3072);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::asn1::{self, Type, pkix};

    const ECDSA_SIGNING: [&EcdsaSigningAlgorithm; 6] = [
        &sign::ECDSA_P256_SHA256_ASN1,
        &sign::ECDSA_P256_SHA256_FIXED,
        &sign::ECDSA_P384_SHA384_ASN1,
        &sign::ECDSA_P384_SHA384_FIXED,
        &sign::ECDSA_P521_SHA512_ASN1,
        &sign::ECDSA_P521_SHA512_FIXED,
    ];

    fn rejected(result: Result<impl fmt::Debug, Error>) -> Error {
        result.expect_err("accepted")
    }

    // A generated key pair derives its public key on the first read, so
    // each reader must see the same key whichever reads first.
    #[test]
    fn ecdsa_generated_public_key_agrees_whichever_reads_first() {
        type Reader = fn(&'static EcdsaSigningAlgorithm, &EcdsaKeyPair) -> Vec<u8>;
        let readers: [Reader; 4] = [
            |_, pair| pair.public_key().as_ref().to_vec(),
            |_, pair| pair.to_spki().as_ref().to_vec(),
            |signing, pair| {
                let pkcs8 = pair.to_pkcs8();
                let loaded = EcdsaKeyPair::from_pkcs8(signing, pkcs8.as_ref()).unwrap();
                loaded.to_spki().as_ref().to_vec()
            },
            |signing, pair| {
                let sec1 = pair.to_sec1();
                let loaded = EcdsaKeyPair::from_sec1(signing, sec1.as_ref()).unwrap();
                loaded.to_spki().as_ref().to_vec()
            },
        ];
        for signing in ECDSA_SIGNING {
            for first in 0..readers.len() {
                let pair = EcdsaKeyPair::generate(signing).unwrap();
                readers[first](signing, &pair);
                let point = pair.public_key().as_ref().to_vec();
                let spki = pair.to_spki().as_ref().to_vec();
                for (i, reader) in readers.iter().enumerate() {
                    let read = reader(signing, &pair);
                    let expected = if i == 0 { &point } else { &spki };
                    assert_eq!(&read, expected, "{signing:?}, {first} first, {i}");
                }
            }
        }
    }

    #[test]
    fn ecdsa_verifies_only_under_its_algorithm() {
        let verification = [
            &verify::ECDSA_P256_SHA256_ASN1,
            &verify::ECDSA_P256_SHA256_FIXED,
            &verify::ECDSA_P384_SHA384_ASN1,
            &verify::ECDSA_P384_SHA384_FIXED,
            &verify::ECDSA_P521_SHA512_ASN1,
            &verify::ECDSA_P521_SHA512_FIXED,
        ];
        for (i, signing) in ECDSA_SIGNING.into_iter().enumerate() {
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let signature = pair.sign(b"message").unwrap();
            let encoded = pair.public_key();
            for (j, algorithm) in verification.into_iter().enumerate() {
                let result = PublicKey::new(algorithm, encoded.as_ref())
                    .and_then(|key| key.verify(b"message", signature.as_ref()));
                assert_eq!(result.is_ok(), i == j, "{signing:?} {algorithm:?}");
            }
            encoded.verify(b"message", signature.as_ref()).unwrap();
            assert_eq!(
                encoded.verify(b"other", signature.as_ref()),
                Err(Error::BadSignature)
            );
        }
    }

    // Signing as a verify-only constant, such as a cross-hash pair, needs
    // crate access, so this differential test lives here rather than in
    // `tests/crosschecks.rs`. Wycheproof has no P-256 with SHA-384 vectors,
    // nor P-521 with SHA-256 or SHA-384.
    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn ecdsa_verification_matches_aws_lc_rs() {
        use aws_lc_rs::signature as theirs;

        let algorithms: [(_, &'static theirs::EcdsaVerificationAlgorithm); 12] = [
            (
                &verify::ECDSA_P256_SHA256_ASN1,
                &theirs::ECDSA_P256_SHA256_ASN1,
            ),
            (
                &verify::ECDSA_P256_SHA384_ASN1,
                &theirs::ECDSA_P256_SHA384_ASN1,
            ),
            (
                &verify::ECDSA_P256_SHA512_ASN1,
                &theirs::ECDSA_P256_SHA512_ASN1,
            ),
            (
                &verify::ECDSA_P384_SHA256_ASN1,
                &theirs::ECDSA_P384_SHA256_ASN1,
            ),
            (
                &verify::ECDSA_P384_SHA384_ASN1,
                &theirs::ECDSA_P384_SHA384_ASN1,
            ),
            (
                &verify::ECDSA_P384_SHA512_ASN1,
                &theirs::ECDSA_P384_SHA512_ASN1,
            ),
            (
                &verify::ECDSA_P521_SHA256_ASN1,
                &theirs::ECDSA_P521_SHA256_ASN1,
            ),
            (
                &verify::ECDSA_P521_SHA384_ASN1,
                &theirs::ECDSA_P521_SHA384_ASN1,
            ),
            (
                &verify::ECDSA_P521_SHA512_ASN1,
                &theirs::ECDSA_P521_SHA512_ASN1,
            ),
            (
                &verify::ECDSA_P256_SHA256_FIXED,
                &theirs::ECDSA_P256_SHA256_FIXED,
            ),
            (
                &verify::ECDSA_P384_SHA384_FIXED,
                &theirs::ECDSA_P384_SHA384_FIXED,
            ),
            (
                &verify::ECDSA_P521_SHA512_FIXED,
                &theirs::ECDSA_P521_SHA512_FIXED,
            ),
        ];
        for (ours, theirs) in algorithms {
            let signing = Box::leak(Box::new(ecdsa_signing(ours)));
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let signature = pair.sign(b"message").unwrap();
            let encoded = pair.public_key();
            theirs::UnparsedPublicKey::new(theirs, encoded.as_ref())
                .verify(b"message", signature.as_ref())
                .unwrap_or_else(|_| panic!("aws-lc-rs refused {ours:?}"));

            let verifier = PublicKey::new(ours, encoded.as_ref()).unwrap();
            verifier.verify(b"message", signature.as_ref()).unwrap();
            assert_eq!(
                verifier.verify(b"other", signature.as_ref()),
                Err(Error::BadSignature)
            );
        }
    }

    #[test]
    fn ecdsa_signs_and_verifies_any_digest() {
        use crate::high::digest::{self, SHA256, SHA384, SHA512};
        use crate::low::ct;

        for signing in ECDSA_SIGNING {
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let encoded = pair.public_key();
            for algorithm in [&SHA256, &SHA384, &SHA512] {
                // Under `admin/ctgrind`, nothing may branch on or index by
                // the digest, nor the key, which its hooks mark secret.
                let message = [0xa5; 100];
                ct::secret_slice(&message);
                let digest = digest::digest(algorithm, &message);
                let signature = ct::into_public(pair.sign_digest(&digest).unwrap());
                let digest = ct::into_public(digest);

                encoded
                    .verify_digest(&digest, signature.as_ref())
                    .unwrap_or_else(|_| panic!("{signing:?} {algorithm:?}"));
                let other = digest::digest(algorithm, b"other");
                assert_eq!(
                    encoded.verify_digest(&other, signature.as_ref()),
                    Err(Error::BadSignature)
                );

                // The key pair's own hash verifies a message only if the
                // digest was of that hash.
                let hash = with_hash!(signing.ecdsa.hash, |H| {
                    <H as crate::high::hash::Hash>::ALGORITHM
                });
                let message = ct::into_public(message);
                assert_eq!(
                    encoded.verify(&message, signature.as_ref()).is_ok(),
                    core::ptr::eq(algorithm, hash),
                    "{signing:?} {algorithm:?}"
                );
            }

            // A signature over a message verifies over its digest.
            let signature = pair.sign(b"message").unwrap();
            let hash = with_hash!(signing.ecdsa.hash, |H| {
                <H as crate::high::hash::Hash>::ALGORITHM
            });
            encoded
                .verify_digest(&digest::digest(hash, b"message"), signature.as_ref())
                .unwrap();
        }
    }

    #[test]
    fn digests_refused_as_unsupported() {
        use crate::high::digest::{self, SHA1, SHA3_256, SHA3_384, SHA3_512, SHA256, SHA512_256};

        let sha256 = digest::digest(&SHA256, b"message");
        for signing in ECDSA_SIGNING {
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let signature = pair.sign_digest(&sha256).unwrap();
            for algorithm in [&SHA1, &SHA512_256, &SHA3_256, &SHA3_384, &SHA3_512] {
                let digest = digest::digest(algorithm, b"message");
                assert_eq!(rejected(pair.sign_digest(&digest)), Error::Unsupported);
                assert_eq!(
                    pair.public_key().verify_digest(&digest, signature.as_ref()),
                    Err(Error::Unsupported)
                );
            }
        }

        // Ed25519 signs messages, not digests, and RSA has no digest API yet.
        let ed25519 = Ed25519KeyPair::generate().unwrap().public_key();
        let rsa = RsaKeyPair::from_pkcs1(include_bytes!("rsa/rsa2048.der"))
            .unwrap()
            .public_key(&sign::RSA_PKCS1_SHA256);
        for key in [ed25519, rsa] {
            assert_eq!(
                key.verify_digest(&sha256, &[0; 64]),
                Err(Error::Unsupported)
            );
        }
    }

    #[test]
    fn public_key_refuses_malformed_keys() {
        let pair = EcdsaKeyPair::generate(&sign::ECDSA_P256_SHA256_ASN1).unwrap();
        let encoded = pair.public_key();
        let point = encoded.as_ref();

        let malformed: [(&'static VerificationAlgorithm, &[u8]); 4] = [
            (&verify::ECDSA_P256_SHA256_ASN1, &point[1..]),
            (&verify::ECDSA_P384_SHA384_ASN1, point),
            (&verify::ED25519, &point[..31]),
            (verify::RSA_PKCS1_SHA256.as_ref(), point),
        ];
        for (algorithm, bytes) in malformed {
            assert!(PublicKey::new(algorithm, bytes).is_err(), "{algorithm:?}");
        }

        // An Ed25519 encoding of the right length but off the curve.
        let off_curve = PublicKey::new(&verify::ED25519, &[0xff; 32]);
        assert_eq!(off_curve.err(), Some(KeyFormatError::NotOnCurve.into()));
    }

    #[test]
    fn ecdsa_private_key_round_trips() {
        for signing in ECDSA_SIGNING {
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let len = match signing.ecdsa.curve {
                CurveId::P256 => 32,
                CurveId::P384 => 48,
                CurveId::P521 => 66,
            };
            // The scalar stays secret, so ctgrind checks the copy out and the
            // load back in.
            let scalar = pair.to_scalar();
            let scalar = scalar.as_ref();
            assert_eq!(scalar.len(), len);

            let encoded = pair.public_key();
            let public = encoded.as_ref();
            let reloaded =
                EcdsaKeyPair::from_scalar_and_public_key(signing, scalar, public).unwrap();
            assert_eq!(reloaded.public_key().as_ref(), public);
            assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());

            // The scalar must be exactly the curve's length, even with a zero
            // byte added or removed.
            let padded = [&[0][..], scalar].concat();
            assert_eq!(
                rejected(EcdsaKeyPair::from_scalar_and_public_key(
                    signing, &padded, public
                )),
                KeyFormatError::WrongLength.into()
            );
            assert_eq!(
                rejected(EcdsaKeyPair::from_scalar_and_public_key(
                    signing,
                    &scalar[1..],
                    public
                )),
                KeyFormatError::WrongLength.into()
            );

            // Zero and anything at or above the order are refused.
            let zero = [0u8; MAX_SCALAR_LEN];
            assert_eq!(
                rejected(EcdsaKeyPair::from_scalar_and_public_key(
                    signing,
                    &zero[..len],
                    public
                )),
                KeyFormatError::ScalarOutOfRange.into()
            );
            let ones = [0xffu8; MAX_SCALAR_LEN];
            assert_eq!(
                rejected(EcdsaKeyPair::from_scalar_and_public_key(
                    signing,
                    &ones[..len],
                    public
                )),
                KeyFormatError::ScalarOutOfRange.into()
            );

            // Another key's point, or the point truncated, is refused.
            let other = EcdsaKeyPair::generate(signing).unwrap().public_key();
            for public in [other.as_ref(), &public[..public.len() - 1]] {
                assert_eq!(
                    rejected(EcdsaKeyPair::from_scalar_and_public_key(
                        signing, scalar, public
                    )),
                    KeyFormatError::MismatchedPublicKey.into()
                );
            }
        }
    }

    /// A scalar with its negation's point, which has the same x and the
    /// other y, is refused: n - d's point is -(dG).
    #[test]
    fn ecdsa_p256_refuses_the_negated_point() {
        const N: [u8; 32] = [
            0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2,
            0xfc, 0x63, 0x25, 0x51,
        ];
        let signing = &sign::ECDSA_P256_SHA256_FIXED;
        let pair = EcdsaKeyPair::generate(signing).unwrap();
        // The subtraction below branches on the scalar in a debug build.
        let scalar = pair.to_scalar();
        low::ct::public_slice(scalar.as_ref());
        let mut negated = [0u8; 32];
        let mut borrow = 0;
        for i in (0..32).rev() {
            let difference = i16::from(N[i]) - i16::from(scalar.as_ref()[i]) - borrow;
            negated[i] = difference as u8;
            borrow = i16::from(difference < 0);
        }
        let public = pair.public_key();
        assert_eq!(
            rejected(EcdsaKeyPair::from_scalar_and_public_key(
                signing,
                &negated,
                public.as_ref()
            )),
            KeyFormatError::MismatchedPublicKey.into()
        );
    }

    #[test]
    fn ecdsa_key_is_bound_to_its_curve() {
        let p256 = include_bytes!("ecdsa/secp256r1.pkcs8.der");
        let p384 = include_bytes!("ecdsa/secp384r1.pkcs8.der");
        let p521 = include_bytes!("ecdsa/secp521r1.pkcs8.der");
        EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P256_SHA256_ASN1, p256).unwrap();
        EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P384_SHA384_ASN1, p384).unwrap();
        EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P521_SHA512_ASN1, p521).unwrap();
        assert!(EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P256_SHA256_ASN1, p384).is_err());
        assert!(EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P384_SHA384_ASN1, p256).is_err());
        assert!(EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P384_SHA384_ASN1, p521).is_err());
        assert!(EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P521_SHA512_ASN1, p384).is_err());

        let p256 = include_bytes!("ecdsa/secp256r1.der");
        let p384 = include_bytes!("ecdsa/secp384r1.der");
        EcdsaKeyPair::from_sec1(&sign::ECDSA_P256_SHA256_ASN1, p256).unwrap();
        assert!(EcdsaKeyPair::from_sec1(&sign::ECDSA_P256_SHA256_ASN1, p384).is_err());

        // A P-384 point is the wrong length for a P-256 key.
        let pair = EcdsaKeyPair::from_pkcs8(
            &sign::ECDSA_P384_SHA384_ASN1,
            include_bytes!("ecdsa/secp384r1.pkcs8.der"),
        )
        .unwrap();
        assert_eq!(
            rejected(PublicKey::new(
                &verify::ECDSA_P256_SHA384_ASN1,
                pair.public_key().as_ref()
            )),
            KeyFormatError::WrongLength.into()
        );
    }

    #[test]
    fn key_loaders_refuse_trailing_bytes() {
        type Load = fn(&[u8]) -> Result<(), Error>;
        let cases: [(&[u8], Load); 8] = [
            (include_bytes!("ecdsa/secp256r1.pkcs8.der"), |der| {
                EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P256_SHA256_ASN1, der).map(drop)
            }),
            (include_bytes!("ecdsa/secp384r1.pkcs8.der"), |der| {
                EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P384_SHA384_ASN1, der).map(drop)
            }),
            (include_bytes!("ecdsa/secp521r1.pkcs8.der"), |der| {
                EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P521_SHA512_ASN1, der).map(drop)
            }),
            (include_bytes!("ecdsa/secp256r1.der"), |der| {
                EcdsaKeyPair::from_sec1(&sign::ECDSA_P256_SHA256_ASN1, der).map(drop)
            }),
            (include_bytes!("rsa/rsa2048.pkcs8.der"), |der| {
                RsaKeyPair::from_pkcs8(der).map(drop)
            }),
            (include_bytes!("rsa/rsa2048.der"), |der| {
                RsaKeyPair::from_pkcs1(der).map(drop)
            }),
            (include_bytes!("rsa/rsa2047.pub.der"), |der| {
                PublicKey::new(&verify::legacy::RSA_PKCS1_1024_SHA256, der).map(drop)
            }),
            (include_bytes!("asn1/testdata/ed25519-p8v2.bin"), |der| {
                Ed25519KeyPair::from_pkcs8(der).map(drop)
            }),
        ];
        for (der, load) in cases {
            load(der).unwrap();
            assert_eq!(
                rejected(load(&[der, &[0x00]].concat())),
                KeyFormatError::Asn1(asn1::Error::UnexpectedTrailingData).into(),
                "{der:02x?}",
            );
        }
    }

    #[test]
    fn rsa_signs_as_long_as_the_modulus() {
        let pair = RsaKeyPair::from_pkcs1(include_bytes!("rsa/rsa2048.der")).unwrap();
        let signature = pair.sign(&sign::RSA_PSS_SHA256, b"message").unwrap();
        assert_eq!(signature.as_ref().len(), 256);

        let public_key = pair.public_key(&sign::RSA_PSS_SHA256);
        public_key.verify(b"message", signature.as_ref()).unwrap();
        assert_eq!(
            public_key.verify(b"other", signature.as_ref()),
            Err(Error::BadSignature)
        );
        assert_eq!(
            pair.public_key(&sign::RSA_PKCS1_SHA256)
                .verify(b"message", signature.as_ref()),
            Err(Error::BadSignature)
        );

        // The encoding parses for the verification algorithm of the same name.
        PublicKey::new(&verify::RSA_PSS_SHA256, public_key.as_ref())
            .unwrap()
            .verify(b"message", signature.as_ref())
            .unwrap();
    }

    #[test]
    fn rsa_public_key_components() {
        let pair = RsaKeyPair::from_pkcs1(include_bytes!("rsa/rsa2048.der")).unwrap();
        let signature = pair.sign(&sign::RSA_PKCS1_SHA256, b"message").unwrap();
        let signature = signature.as_ref();

        let der = pair.public_key(&sign::RSA_PKCS1_SHA256);
        let parsed = pkix::RSAPublicKey::from_bytes(der.as_ref()).unwrap();
        let n = parsed.modulus.as_ref().strip_prefix(&[0]).unwrap();
        let e = parsed.publicExponent.as_ref();
        let key = PublicKeyComponents { n, e };
        for algorithm in [
            &verify::RSA_PKCS1_SHA256,
            &verify::legacy::RSA_PKCS1_1024_SHA256,
        ] {
            let public_key = PublicKey::from_components(algorithm, &key).unwrap();
            assert_eq!(public_key.as_ref(), der.as_ref());
            public_key.verify(b"message", signature).unwrap();
            assert_eq!(
                public_key.verify(b"other", signature),
                Err(Error::BadSignature)
            );
        }
        for algorithm in [
            &verify::legacy::RSA_PKCS1_SHA1,
            &verify::legacy::RSA_PKCS1_1024_SHA512,
        ] {
            assert_eq!(
                PublicKey::from_components(algorithm, &key)
                    .unwrap()
                    .verify(b"message", signature),
                Err(Error::BadSignature)
            );
        }

        // A 2048-bit key is below this algorithm's floor, in either form.
        assert_eq!(
            rejected(PublicKey::from_components(
                &verify::legacy::RSA_PKCS1_3072_SHA384,
                &key
            )),
            KeyFormatError::RsaModulus.into()
        );
        assert_eq!(
            rejected(PublicKey::new(
                &verify::legacy::RSA_PKCS1_3072_SHA384,
                der.as_ref()
            )),
            KeyFormatError::RsaModulus.into()
        );

        let n0 = [&[0], n].concat();
        let e0 = [&[0], e].concat();
        let malformed: [(&[u8], &[u8], Error); 5] = [
            (&n0, e, KeyFormatError::LeadingZero.into()),
            (n, &e0, KeyFormatError::LeadingZero.into()),
            (n, &[2, 0, 0, 0, 1], KeyFormatError::RsaExponent.into()),
            (&[], e, KeyFormatError::RsaModulus.into()),
            (n, &[], KeyFormatError::RsaExponent.into()),
        ];
        for (n, e, expected) in malformed {
            let key = PublicKeyComponents { n, e };
            assert_eq!(
                rejected(PublicKey::from_components(&verify::RSA_PKCS1_SHA256, &key)),
                expected
            );
        }
    }

    /// A PKCS#8 ML-DSA key of `oid` holding `private_key`, and `public_key`
    /// if given (v2).
    fn ml_dsa_pkcs8(
        oid: &asn1::ObjectId,
        private_key: pkix::MlDsaPrivateKey<'_>,
        public_key: Option<&[u8]>,
    ) -> Vec<u8> {
        let mut inner = vec![0; 10_000];
        let len = private_key
            .encode(&mut asn1::Encoder::new(&mut inner))
            .unwrap();
        assert_eq!(private_key.encoded_len(), len);
        let mut out = vec![0; 20_000];
        let der = pkcs8::Key::construct(&inner[..len], public_key, oid.clone(), None)
            .encode(&mut out)
            .unwrap();
        der.to_vec()
    }

    #[test]
    fn ml_dsa_encodings() {
        fn check<P: MlDsaParameterSet>(other: &asn1::ObjectId) {
            // This compares encodings of the key, so declassifies them.
            let pair = MlDsaKeyPair::<P>::generate().unwrap();
            let seed = low::ct::into_public(pair.to_seed().unwrap().0);
            let seed = asn1::OctetString::new(&seed);
            let sk = low::ct::into_public(pair.0.secret_key().clone());
            let sk = sk.as_ref();
            let expanded = asn1::OctetString::new(sk);
            let pk = pair.0.public_key().as_ref();
            let oid = P::ALGORITHM.oid;
            let load = |der: &[u8]| MlDsaKeyPair::<P>::from_pkcs8(der);
            let seed_form = ml_dsa_pkcs8(oid, pkix::MlDsaPrivateKey::Seed(seed.clone()), None);
            assert_eq!(pair.to_pkcs8().as_ref(), seed_form);

            // Each form loads, and a key without its seed writes the
            // expanded form.
            let both = |expanded| {
                pkix::MlDsaPrivateKey::Both(pkix::MlDsaSeedAndKey {
                    seed: seed.clone(),
                    expandedKey: expanded,
                })
            };
            let expanded_form = ml_dsa_pkcs8(
                oid,
                pkix::MlDsaPrivateKey::ExpandedKey(expanded.clone()),
                None,
            );
            for (der, has_seed) in [
                (seed_form.clone(), true),
                (expanded_form.clone(), false),
                (ml_dsa_pkcs8(oid, both(expanded.clone()), None), true),
                (ml_dsa_pkcs8(oid, both(expanded.clone()), Some(pk)), true),
            ] {
                let key = load(&der).unwrap();
                assert_eq!(key.public_key().as_ref(), pk);
                assert_eq!(key.to_seed().is_some(), has_seed);
                let written = key.to_pkcs8();
                let want = if has_seed { &seed_form } else { &expanded_form };
                assert_eq!(written.as_ref(), want);
            }

            // A seed and expanded key that disagree.
            let mut wrong = sk.to_vec();
            wrong[sk.len() - 1] ^= 1;
            let der = ml_dsa_pkcs8(oid, both(asn1::OctetString::new(&wrong)), None);
            assert_eq!(
                rejected(load(&der)),
                KeyFormatError::MismatchedMlDsaSeed.into()
            );
            let der = ml_dsa_pkcs8(oid, both(asn1::OctetString::new(&sk[1..])), None);
            assert_eq!(
                rejected(load(&der)),
                KeyFormatError::MismatchedMlDsaSeed.into()
            );

            // An expanded key whose parts disagree: its `t0`, its `tr`.
            let der = ml_dsa_pkcs8(
                oid,
                pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(&wrong)),
                None,
            );
            assert_eq!(rejected(load(&der)), KeyFormatError::MlDsaSecretKey.into());
            let mut wrong = sk.to_vec();
            wrong[2 * 32] ^= 1;
            let der = ml_dsa_pkcs8(
                oid,
                pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(&wrong)),
                None,
            );
            assert_eq!(rejected(load(&der)), KeyFormatError::MlDsaSecretKey.into());

            // A public key (v2) that does not match.
            let other_pair = MlDsaKeyPair::<P>::generate().unwrap();
            let der = ml_dsa_pkcs8(
                oid,
                pkix::MlDsaPrivateKey::Seed(seed.clone()),
                Some(other_pair.0.public_key().as_ref()),
            );
            assert_eq!(
                rejected(load(&der)),
                KeyFormatError::MismatchedPkcs8PublicKey.into()
            );

            // Lengths, another parameter set, and trailing bytes.
            for bad in [&sk[..31], &[0; 33][..]] {
                let der = ml_dsa_pkcs8(
                    oid,
                    pkix::MlDsaPrivateKey::Seed(asn1::OctetString::new(bad)),
                    None,
                );
                assert_eq!(rejected(load(&der)), KeyFormatError::WrongLength.into());
                assert_eq!(
                    rejected(MlDsaKeyPair::<P>::from_seed(bad)),
                    KeyFormatError::WrongLength.into()
                );
            }
            let der = ml_dsa_pkcs8(
                oid,
                pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(&sk[1..])),
                None,
            );
            assert_eq!(rejected(load(&der)), KeyFormatError::WrongLength.into());
            let der = ml_dsa_pkcs8(other, pkix::MlDsaPrivateKey::Seed(seed.clone()), None);
            assert_eq!(
                rejected(load(&der)),
                KeyFormatError::MismatchedPkcs8Algorithm.into()
            );
            let mut der = seed_form.clone();
            der.push(0);
            assert!(load(&der).is_err());
            // A private key of another tag, such as an explicit `[0]`.
            let mut der = seed_form.clone();
            let tag = der.len() - 34;
            assert_eq!(der[tag], 0x80);
            der[tag] = 0xa0;
            assert!(load(&der).is_err());

            // Public keys: lengths, another parameter set's SPKI, and no
            // digest signing.
            let public = pair.public_key();
            let algorithm = VerificationAlgorithm(Verification::MlDsa(P::ALGORITHM));
            let spki = public.to_spki();
            let parsed = PublicKey::from_spki(&algorithm, spki.as_ref()).unwrap();
            assert_eq!(parsed.as_ref(), pk);
            for bad in [&pk[1..], &[pk, &[0]].concat()] {
                assert_eq!(
                    rejected(PublicKey::new(&algorithm, bad)),
                    KeyFormatError::WrongLength.into()
                );
            }
            let mut out = vec![0; 4096];
            let other_spki = spki::encode(pk, other, None, &mut out).unwrap();
            assert_eq!(
                rejected(PublicKey::from_spki(&algorithm, other_spki)),
                KeyFormatError::MismatchedSpkiAlgorithm.into()
            );
            let signature = pair.sign(b"message").unwrap();
            parsed.verify(b"message", signature.as_ref()).unwrap();
            let digest = crate::high::digest::digest(&crate::high::digest::SHA256, b"message");
            assert_eq!(
                parsed.verify_digest(&digest, signature.as_ref()),
                Err(Error::Unsupported)
            );
        }
        check::<MlDsa44>(&asn1::oid::id_ml_dsa_65);
        check::<MlDsa65>(&asn1::oid::id_ml_dsa_87);
        check::<MlDsa87>(&asn1::oid::id_ml_dsa_44);
    }

    #[test]
    fn ed25519_seed_and_public_key() {
        let seed = [7u8; 32];
        let public = Ed25519SigningKey::from_bytes(&seed)
            .unwrap()
            .public_key()
            .as_bytes();
        let pair = Ed25519KeyPair::from_seed_and_public_key(&seed, &public).unwrap();
        let encoded = pair.public_key();
        assert_eq!(encoded.as_ref(), public);
        let signature = pair.sign(b"message");
        assert_eq!(signature.as_ref().len(), 64);
        encoded.verify(b"message", signature.as_ref()).unwrap();

        let other = Ed25519KeyPair::generate().unwrap().public_key();
        for public in [other.as_ref(), &public[..31]] {
            assert_eq!(
                rejected(Ed25519KeyPair::from_seed_and_public_key(&seed, public)),
                KeyFormatError::MismatchedPublicKey.into()
            );
        }
        for seed in [&seed[..31], &[seed.as_slice(), &[0]].concat()] {
            assert_eq!(
                rejected(Ed25519KeyPair::from_seed_and_public_key(seed, &public)),
                KeyFormatError::WrongLength.into()
            );
        }
    }

    #[test]
    fn ed25519_seed_round_trips() {
        // The seed stays secret, so ctgrind checks the copy out and the load
        // back in.
        let pair = Ed25519KeyPair::generate().unwrap();
        let seed = pair.to_seed();
        let public = pair.public_key();
        let reloaded =
            Ed25519KeyPair::from_seed_and_public_key(seed.as_ref(), public.as_ref()).unwrap();
        assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());
    }

    #[test]
    fn ed25519_seed_loads_alone() {
        // The seed stays secret, so ctgrind checks the load and both
        // PKCS#8 encodings.
        let pair = Ed25519KeyPair::generate().unwrap();
        let seed = pair.to_seed();
        let reloaded = Ed25519KeyPair::from_seed(seed.as_ref()).unwrap();
        assert_eq!(reloaded.public_key().as_ref(), pair.public_key().as_ref());
        assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());

        // v1 is RFC 8410's fixed prefix and the seed, which loads back.
        let v1 = pair.to_pkcs8v1();
        assert_eq!(v1.as_ref().len(), 48);
        assert_eq!(
            v1.as_ref()[..16],
            include_bytes!("asn1/testdata/ed25519-p8v1.bin")[..16]
        );
        let reloaded = Ed25519KeyPair::from_pkcs8(v1.as_ref()).unwrap();
        assert_eq!(reloaded.public_key().as_ref(), pair.public_key().as_ref());

        for seed in [&[0; 31][..], &[0; 33]] {
            assert_eq!(
                rejected(Ed25519KeyPair::from_seed(seed)),
                KeyFormatError::WrongLength.into()
            );
        }
    }

    #[test]
    fn ecdsa_sec1_round_trips() {
        for signing in ECDSA_SIGNING {
            // The key is secret, so ctgrind checks the encoding.
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let sec1 = pair.to_sec1();
            let reloaded = EcdsaKeyPair::from_sec1(signing, sec1.as_ref()).unwrap();
            assert_eq!(reloaded.to_pkcs8().as_ref(), pair.to_pkcs8().as_ref());

            // It names its curve and holds its public key, as the
            // `ECPrivateKey` inside PKCS#8 does, which names neither.
            let decoded = pkix::EcPrivateKey::from_bytes(sec1.as_ref()).unwrap();
            assert_eq!(
                decoded.parameters.inner(),
                &Some(curve_oid(signing.ecdsa.curve))
            );
            assert_eq!(
                decoded
                    .publicKey
                    .inner()
                    .as_ref()
                    .map(|key| key.as_octets()),
                Some(pair.public_key().as_ref())
            );
        }
    }

    #[test]
    fn public_keys_round_trip_through_spki() {
        let rsa = RsaKeyPair::from_pkcs1(include_bytes!("rsa/rsa2048.der")).unwrap();
        let ed25519 = Ed25519KeyPair::generate().unwrap();
        // Each key, and the kind of key its algorithm takes.
        let mut keys = vec![
            (
                verify::RSA_PSS_SHA256.as_ref(),
                "RSA",
                rsa.public_key(&sign::RSA_PSS_SHA256),
                rsa.to_spki(),
            ),
            (
                &verify::ED25519,
                "Ed25519",
                ed25519.public_key(),
                ed25519.to_spki(),
            ),
        ];
        let verification = [
            &verify::ECDSA_P256_SHA256_ASN1,
            &verify::ECDSA_P256_SHA256_FIXED,
            &verify::ECDSA_P384_SHA384_ASN1,
            &verify::ECDSA_P384_SHA384_FIXED,
            &verify::ECDSA_P521_SHA512_ASN1,
            &verify::ECDSA_P521_SHA512_FIXED,
        ];
        for (signing, verification) in ECDSA_SIGNING.into_iter().zip(verification) {
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let curve = match signing.ecdsa.curve {
                CurveId::P256 => "P-256",
                CurveId::P384 => "P-384",
                CurveId::P521 => "P-521",
            };
            keys.push((verification, curve, pair.public_key(), pair.to_spki()));
        }

        for (algorithm, kind, key, spki) in &keys {
            assert_eq!(key.to_spki().as_ref(), spki.as_ref(), "{algorithm:?}");
            let parsed = PublicKey::from_spki(*algorithm, spki.as_ref()).unwrap();
            assert_eq!(parsed.as_ref(), key.as_ref());

            // The bare key is no SPKI.
            assert!(PublicKey::from_spki(*algorithm, key.as_ref()).is_err());
            // Nor is another kind's.
            for (other, other_kind, _, other_spki) in &keys {
                let result = PublicKey::from_spki(*algorithm, other_spki.as_ref());
                assert_eq!(
                    kind == other_kind,
                    result.is_ok(),
                    "{algorithm:?} {other:?}"
                );
            }
        }
    }

    #[test]
    fn ecdsa_spki_decompresses() {
        for (signing, verification) in [
            (
                &sign::ECDSA_P256_SHA256_ASN1,
                &verify::ECDSA_P256_SHA256_ASN1,
            ),
            (
                &sign::ECDSA_P384_SHA384_ASN1,
                &verify::ECDSA_P384_SHA384_ASN1,
            ),
            (
                &sign::ECDSA_P521_SHA512_ASN1,
                &verify::ECDSA_P521_SHA512_ASN1,
            ),
        ] {
            let pair = EcdsaKeyPair::generate(signing).unwrap();
            let point = pair.public_key();
            let point = point.as_ref();
            let (x, y) = point[1..].split_at(point.len() / 2);
            let curve = Some(asn1::Any::ObjectId(curve_oid(signing.ecdsa.curve)));
            let spki = |key: &[u8]| {
                let mut der = [0; 256];
                let der = spki::encode(key, &asn1::oid::id_ecPublicKey, curve.clone(), &mut der);
                der.unwrap().to_vec()
            };

            let compressed = [&[2 | (y[y.len() - 1] & 1)][..], x].concat();
            let parsed = PublicKey::from_spki(verification, &spki(&compressed)).unwrap();
            assert_eq!(parsed.as_ref(), point);
            let signature = pair.sign(b"message").unwrap();
            parsed.verify(b"message", signature.as_ref()).unwrap();

            // `new` takes it uncompressed only, and a hybrid point is
            // refused either way.
            assert_eq!(
                rejected(PublicKey::new(verification, &compressed)),
                KeyFormatError::Compressed.into()
            );
            let hybrid = [&[6 | (y[y.len() - 1] & 1)][..], &point[1..]].concat();
            assert_eq!(
                rejected(PublicKey::from_spki(verification, &spki(&hybrid))),
                KeyFormatError::PointEncoding.into()
            );

            // `id-ecDH` names an ECDH key, not an ECDSA one.
            let mut der = [0; 256];
            let ecdh = spki::encode(point, &asn1::oid::id_ecDH, curve.clone(), &mut der).unwrap();
            assert_eq!(
                rejected(PublicKey::from_spki(verification, ecdh)),
                KeyFormatError::MismatchedSpkiAlgorithm.into()
            );
        }
    }

    // The owned encodings are sized for the largest key each loader takes,
    // so encoding one must not run out of room.
    #[test]
    fn encodings_fit_the_largest_keys() {
        let rsa = RsaKeyPair::from_pkcs1(include_bytes!("rsa/rsa8192.der")).unwrap();
        let pkcs8 = rsa.to_pkcs8();
        assert_eq!(pkcs8.as_ref(), include_bytes!("rsa/rsa8192.pkcs8.der"));
        let spki = rsa.to_spki();
        let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
        let encoded = rsa.public_key(&sign::RSA_PSS_SHA512);
        assert_eq!(parsed.subjectPublicKey.as_octets(), encoded.as_ref());
        let signature = rsa.sign(&sign::RSA_PSS_SHA512, b"message").unwrap();
        assert_eq!(signature.as_ref().len(), 1024);
        encoded.verify(b"message", signature.as_ref()).unwrap();

        let p521 = include_bytes!("ecdsa/secp521r1.pkcs8.der");
        let ecdsa = EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P521_SHA512_ASN1, p521).unwrap();
        let reloaded =
            EcdsaKeyPair::from_pkcs8(&sign::ECDSA_P521_SHA512_ASN1, ecdsa.to_pkcs8().as_ref())
                .unwrap();
        assert_eq!(reloaded.public_key().as_ref(), ecdsa.public_key().as_ref());
        let spki = ecdsa.to_spki();
        let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
        assert_eq!(
            parsed.subjectPublicKey.as_octets(),
            ecdsa.public_key().as_ref()
        );

        let ed25519 = Ed25519KeyPair::generate().unwrap();
        let reloaded = Ed25519KeyPair::from_pkcs8(ed25519.to_pkcs8().as_ref()).unwrap();
        assert_eq!(
            reloaded.public_key().as_ref(),
            ed25519.public_key().as_ref()
        );
        let spki = ed25519.to_spki();
        let parsed = pkix::SubjectPublicKeyInfo::from_bytes(spki.as_ref()).unwrap();
        assert_eq!(
            parsed.subjectPublicKey.as_octets(),
            ed25519.public_key().as_ref()
        );
    }
}
