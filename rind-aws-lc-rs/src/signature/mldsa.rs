//! ML-DSA-44, ML-DSA-65, and ML-DSA-87, as aws-lc-rs names them.
//!
//! aws-lc-rs picks the parameter set at run time. rind's key pair takes it
//! as a type, so [`PqdsaKeyPair`] holds an enum of the three and dispatches
//! on the [`PqdsaSigningAlgorithm`] it was given.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use zeroize::Zeroize;

use rind::signature::sign::{MlDsa44, MlDsa65, MlDsa87, MlDsaKeyPair};

use crate::encoding::{AsDer, Pkcs8V1Der, PublicKeyX509Der};
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::pkcs8::Document;
use crate::{der, signature};

/// Which ML-DSA parameter set a key uses. The names are aws-lc-rs's `Debug`
/// text.
#[allow(non_camel_case_types, clippy::upper_case_acronyms)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AlgorithmId {
    ML_DSA_44,
    ML_DSA_65,
    ML_DSA_87,
}

impl AlgorithmId {
    const fn public_key_len(self) -> usize {
        match self {
            Self::ML_DSA_44 => 1312,
            Self::ML_DSA_65 => 1952,
            Self::ML_DSA_87 => 2592,
        }
    }

    const fn signature_len(self) -> usize {
        match self {
            Self::ML_DSA_44 => 2420,
            Self::ML_DSA_65 => 3309,
            Self::ML_DSA_87 => 4627,
        }
    }

    /// Every parameter set's seed is 32 bytes.
    const fn seed_len(self) -> usize {
        match self {
            Self::ML_DSA_44 | Self::ML_DSA_65 | Self::ML_DSA_87 => 32,
        }
    }

    /// FIPS 204's expanded private key.
    const fn raw_private_len(self) -> usize {
        match self {
            Self::ML_DSA_44 => 2560,
            Self::ML_DSA_65 => 4032,
            Self::ML_DSA_87 => 4896,
        }
    }

    fn verify(self) -> &'static rind::signature::VerificationAlgorithm {
        match self {
            Self::ML_DSA_44 => &rind::signature::verify::ML_DSA_44,
            Self::ML_DSA_65 => &rind::signature::verify::ML_DSA_65,
            Self::ML_DSA_87 => &rind::signature::verify::ML_DSA_87,
        }
    }

    /// The parameter set whose expanded private key is `len` bytes, as
    /// aws-lc-rs selects it before checking the caller's algorithm.
    fn from_raw_len(len: usize) -> Option<Self> {
        [Self::ML_DSA_44, Self::ML_DSA_65, Self::ML_DSA_87]
            .into_iter()
            .find(|id| id.raw_private_len() == len)
    }

    /// The parameter set whose object identifier's contents are `oid`.
    fn from_oid(oid: &[u8]) -> Option<Self> {
        [Self::ML_DSA_44, Self::ML_DSA_65, Self::ML_DSA_87]
            .into_iter()
            .find(|id| id.oid() == oid)
    }

    /// The object identifier's contents, without its tag and length.
    fn oid(self) -> &'static [u8] {
        &algorithm_identifier(self)[4..]
    }
}

/// An ML-DSA verification algorithm.
#[derive(Debug, Eq, PartialEq)]
pub struct PqdsaVerificationAlgorithm {
    id: &'static AlgorithmId,
}

impl PqdsaVerificationAlgorithm {
    fn id(&self) -> AlgorithmId {
        *self.id
    }
}

impl signature::private::Verify for PqdsaVerificationAlgorithm {
    fn parse(&self, public_key: &[u8]) -> Result<rind::signature::PublicKey, KeyRejected> {
        let algorithm = self.id().verify();
        // aws-lc-rs tries a `SubjectPublicKeyInfo` first, then the raw key.
        // A raw key has this parameter set's length. Any other length makes
        // the raw parse fail with `Unspecified`, and that error replaces the
        // SPKI failure (`Result::or`).
        if let Ok(key) = rind::signature::PublicKey::from_spki(algorithm, public_key) {
            return Ok(key);
        }
        if public_key.len() == self.id().public_key_len() {
            return rind::signature::PublicKey::new(algorithm, public_key)
                .map_err(KeyRejected::rind);
        }
        Err(KeyRejected::unspecified())
    }

    fn verify_parsed(
        &self,
        key: &rind::signature::PublicKey,
        msg: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        key.verify(msg, signature).map_err(unspecified)
    }

    fn verify_parsed_digest(
        &self,
        _: &rind::signature::PublicKey,
        _: &crate::digest::Digest,
        _: &[u8],
    ) -> Result<(), Unspecified> {
        // Pure ML-DSA signs the message. A digest is not FIPS 204's `mu`.
        Err(Unspecified)
    }
}

signature::verification_algorithm!(PqdsaVerificationAlgorithm);

/// An ML-DSA signing algorithm.
#[derive(Debug, Eq, PartialEq)]
pub struct PqdsaSigningAlgorithm(pub(crate) &'static PqdsaVerificationAlgorithm);

impl PqdsaSigningAlgorithm {
    /// The signature's length, in bytes.
    #[must_use]
    pub fn signature_len(&self) -> usize {
        self.0.id().signature_len()
    }

    /// The raw public key's length, in bytes.
    #[must_use]
    pub fn public_key_len(&self) -> usize {
        self.0.id().public_key_len()
    }

    /// The seed's length, in bytes. Every ML-DSA parameter set uses 32.
    #[must_use]
    pub fn seed_len(&self) -> usize {
        self.0.id().seed_len()
    }

    fn id(&self) -> AlgorithmId {
        self.0.id()
    }
}

/// Verification of ML-DSA-44 signatures.
pub const ML_DSA_44: PqdsaVerificationAlgorithm = PqdsaVerificationAlgorithm {
    id: &AlgorithmId::ML_DSA_44,
};

/// Verification of ML-DSA-65 signatures.
pub const ML_DSA_65: PqdsaVerificationAlgorithm = PqdsaVerificationAlgorithm {
    id: &AlgorithmId::ML_DSA_65,
};

/// Verification of ML-DSA-87 signatures.
pub const ML_DSA_87: PqdsaVerificationAlgorithm = PqdsaVerificationAlgorithm {
    id: &AlgorithmId::ML_DSA_87,
};

/// Signing with ML-DSA-44.
pub const ML_DSA_44_SIGNING: PqdsaSigningAlgorithm = PqdsaSigningAlgorithm(&ML_DSA_44);

/// Signing with ML-DSA-65.
pub const ML_DSA_65_SIGNING: PqdsaSigningAlgorithm = PqdsaSigningAlgorithm(&ML_DSA_65);

/// Signing with ML-DSA-87.
pub const ML_DSA_87_SIGNING: PqdsaSigningAlgorithm = PqdsaSigningAlgorithm(&ML_DSA_87);

/// An ML-DSA public key's raw bytes, and its `SubjectPublicKeyInfo`.
///
/// A [`PqdsaKeyPair`] wipes the copy it holds when dropped, under the `wipe`
/// feature, as a key type wipes its whole value. A copy cloned out of it is
/// the caller's.
#[derive(Clone)]
pub struct PqdsaPublicKey {
    octets: Box<[u8]>,
    spki: Box<[u8]>,
}

impl PqdsaPublicKey {
    fn new(key: &rind::signature::PublicKey) -> Self {
        Self {
            octets: key.as_ref().into(),
            spki: key.to_spki().as_ref().into(),
        }
    }
}

impl AsRef<[u8]> for PqdsaPublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.octets
    }
}

impl AsDer<PublicKeyX509Der<'static>> for PqdsaPublicKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        Ok(PublicKeyX509Der::new(self.spki.to_vec()))
    }
}

impl fmt::Debug for PqdsaPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PqdsaPublicKey(\"")?;
        crate::write_hex(f, &self.octets)?;
        f.write_str("\")")
    }
}

/// One parameter set's key pair. Boxed so the enum stays small.
enum Key {
    MlDsa44(Box<MlDsaKeyPair<MlDsa44>>),
    MlDsa65(Box<MlDsaKeyPair<MlDsa65>>),
    MlDsa87(Box<MlDsaKeyPair<MlDsa87>>),
}

/// Builds a [`Key`] of parameter set `$id` by calling `MlDsaKeyPair::$ctor`.
macro_rules! build {
    ($id:expr, $ctor:ident($($arg:expr),*)) => {
        match $id {
            AlgorithmId::ML_DSA_44 => MlDsaKeyPair::$ctor($($arg),*).map(|k| Key::MlDsa44(Box::new(k))),
            AlgorithmId::ML_DSA_65 => MlDsaKeyPair::$ctor($($arg),*).map(|k| Key::MlDsa65(Box::new(k))),
            AlgorithmId::ML_DSA_87 => MlDsaKeyPair::$ctor($($arg),*).map(|k| Key::MlDsa87(Box::new(k))),
        }
    };
}

/// Evaluates `$body` with `$key` bound to whichever parameter set's key
/// pair `$self` holds.
macro_rules! each {
    ($self:expr, $key:ident => $body:expr) => {
        match $self {
            Key::MlDsa44($key) => $body,
            Key::MlDsa65($key) => $body,
            Key::MlDsa87($key) => $body,
        }
    };
}

impl Key {
    fn generate(id: AlgorithmId) -> Result<Self, rind::Error> {
        build!(id, generate())
    }

    fn from_seed(id: AlgorithmId, seed: &[u8]) -> Result<Self, rind::Error> {
        build!(id, from_seed(seed))
    }

    fn from_pkcs8(id: AlgorithmId, pkcs8: &[u8]) -> Result<Self, rind::Error> {
        build!(id, from_pkcs8(pkcs8))
    }

    fn public_key(&self) -> rind::signature::PublicKey {
        each!(self, key => key.public_key())
    }

    fn has_seed(&self) -> bool {
        each!(self, key => key.has_seed())
    }

    fn to_pkcs8(&self) -> rind::encoding::Pkcs8 {
        each!(self, key => key.to_pkcs8())
    }

    fn sign_into(&self, message: &[u8], out: &mut [u8]) -> Result<(), rind::Error> {
        each!(self, key => out.copy_from_slice(key.sign(message)?.as_ref()));
        Ok(())
    }
}

/// An ML-DSA private key and its public key.
///
/// Signing is hedged, so two signatures of the same message are not the same
/// bytes. Each signature verifies under the public key.
#[derive(Clone)]
pub struct PqdsaKeyPair {
    algorithm: &'static PqdsaSigningAlgorithm,
    key: Arc<Key>,
    pubkey: PqdsaPublicKey,
}

impl PqdsaKeyPair {
    fn new(algorithm: &'static PqdsaSigningAlgorithm, key: Key) -> Self {
        let pubkey = PqdsaPublicKey::new(&key.public_key());
        Self {
            algorithm,
            key: Arc::new(key),
            pubkey,
        }
    }

    /// Generates a key pair for `algorithm`.
    pub fn generate(algorithm: &'static PqdsaSigningAlgorithm) -> Result<Self, Unspecified> {
        let key = Key::generate(algorithm.id()).map_err(unspecified)?;
        Ok(Self::new(algorithm, key))
    }

    /// Loads a PKCS#8 key for `algorithm`: the seed, the expanded private
    /// key, or both when they agree. A v2 public key that does not match is
    /// refused.
    pub fn from_pkcs8(
        algorithm: &'static PqdsaSigningAlgorithm,
        pkcs8: &[u8],
    ) -> Result<Self, KeyRejected> {
        // The algorithm identifier is public, so it picks the refusal before
        // any key is expanded. Only the parameter set it names is parsed.
        let named = der::pkcs8_algorithm(pkcs8).map(AlgorithmId::from_oid);
        match named {
            // Another ML-DSA parameter set: aws-lc-rs parses the key as that
            // set, then refuses it as `Unspecified` once its size is wrong,
            // or as `InvalidEncoding` when it does not parse.
            Some(Some(id)) if id != algorithm.id() => match Key::from_pkcs8(id, pkcs8) {
                Ok(_) => Err(KeyRejected::unspecified()),
                Err(err) => Err(KeyRejected::rind(err)),
            },
            // Another algorithm. aws-lc-rs says `WrongAlgorithm` only after
            // `EVP_parse_private_key` succeeds on a non-ML-DSA key. An unknown
            // or truncated OID, or a known OID whose key does not parse, is
            // `InvalidEncoding`.
            Some(None) => {
                if parses_as_other_private_key(pkcs8) {
                    Err(KeyRejected::wrong_algorithm())
                } else {
                    Err(KeyRejected::invalid_encoding())
                }
            }
            // This parameter set, or a document whose header does not parse,
            // which rind refuses with its own reason.
            Some(Some(_)) | None => Key::from_pkcs8(algorithm.id(), pkcs8)
                .map(|key| Self::new(algorithm, key))
                .map_err(KeyRejected::rind),
        }
    }

    /// Loads an expanded private key, FIPS 204's encoding.
    ///
    /// The bytes are wrapped in the PKCS#8 form rind loads. A seed-sized
    /// input is refused: this is the expanded key, not [`Self::from_seed`].
    pub fn from_raw_private_key(
        algorithm: &'static PqdsaSigningAlgorithm,
        raw_private_key: &[u8],
    ) -> Result<Self, KeyRejected> {
        // aws-lc-rs picks the parameter set from the length, then refuses
        // the key when that set is not `algorithm`. The length is public, so
        // that refusal comes before the key is expanded.
        let Some(id) = AlgorithmId::from_raw_len(raw_private_key.len()) else {
            return Err(KeyRejected::invalid_encoding());
        };
        if id != algorithm.id() {
            return Err(KeyRejected::unspecified());
        }
        // A copy inside the call, freed unwiped: rind wipes the key it
        // loads, and nothing else is.
        let der = expanded_pkcs8(id, raw_private_key);
        let key = Key::from_pkcs8(id, &der).map_err(|_| KeyRejected::invalid_encoding())?;
        Ok(Self::new(algorithm, key))
    }

    /// Expands a 32-byte seed into its key pair.
    pub fn from_seed(
        algorithm: &'static PqdsaSigningAlgorithm,
        seed: &[u8],
    ) -> Result<Self, KeyRejected> {
        match seed.len().cmp(&algorithm.seed_len()) {
            core::cmp::Ordering::Less => return Err(KeyRejected::too_small()),
            core::cmp::Ordering::Greater => return Err(KeyRejected::too_large()),
            core::cmp::Ordering::Equal => {}
        }
        let key = Key::from_seed(algorithm.id(), seed).map_err(KeyRejected::rind)?;
        Ok(Self::new(algorithm, key))
    }

    /// Encodes the private key as PKCS#8 v1 in seed form.
    ///
    /// A key loaded from its expanded form has no seed, and this fails, as
    /// aws-lc-rs's does. rind would write the expanded form; that encoding
    /// is not returned here.
    pub fn to_pkcs8v1(&self) -> Result<Document, Unspecified> {
        Ok(Document::new(self.pkcs8_seed()?.as_ref()))
    }

    /// Deprecated alias for [`Self::to_pkcs8v1`].
    ///
    /// # Errors
    ///
    /// Returns `Unspecified` when the key has no seed.
    #[cfg(feature = "unstable")]
    #[deprecated(since = "1.18.0", note = "use `PqdsaKeyPair::to_pkcs8v1`")]
    pub fn to_pkcs8(&self) -> Result<Document, Unspecified> {
        self.to_pkcs8v1()
    }

    /// Signs `msg`, writing the signature into `signature`, which must be at
    /// least [`PqdsaSigningAlgorithm::signature_len`] bytes. Returns the
    /// number of bytes written.
    pub fn sign(&self, msg: &[u8], signature: &mut [u8]) -> Result<usize, Unspecified> {
        let len = self.algorithm.signature_len();
        if signature.len() < len {
            return Err(Unspecified);
        }
        self.key
            .sign_into(msg, &mut signature[..len])
            .map_err(unspecified)?;
        Ok(len)
    }

    /// The signing algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static PqdsaSigningAlgorithm {
        self.algorithm
    }

    /// The private key.
    #[must_use]
    pub fn private_key(&self) -> PqdsaPrivateKey<'_> {
        PqdsaPrivateKey(self)
    }

    /// rind's PKCS#8 in seed form, wiped when dropped. Callers copy it once,
    /// into the wiped value they return.
    fn pkcs8_seed(&self) -> Result<rind::encoding::Pkcs8, Unspecified> {
        if !self.key.has_seed() {
            return Err(Unspecified);
        }
        Ok(self.key.to_pkcs8())
    }
}

impl Drop for PqdsaKeyPair {
    fn drop(&mut self) {
        // rind wipes the private key, and its own public key, when the last
        // `Arc` goes. The adapter's copies of the public key are wiped here,
        // per clone. `cfg!` keeps the wipe type-checked in every build.
        if cfg!(feature = "wipe") {
            self.pubkey.octets.zeroize();
            self.pubkey.spki.zeroize();
        }
    }
}

impl signature::KeyPair for PqdsaKeyPair {
    type PublicKey = PqdsaPublicKey;

    fn public_key(&self) -> &PqdsaPublicKey {
        &self.pubkey
    }
}

impl fmt::Debug for PqdsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqdsaKeyPair")
            .field("algorithm", &self.algorithm)
            .finish()
    }
}

/// An ML-DSA private key, borrowed from its [`PqdsaKeyPair`].
pub struct PqdsaPrivateKey<'a>(pub(crate) &'a PqdsaKeyPair);

impl AsDer<Pkcs8V1Der<'static>> for PqdsaPrivateKey<'_> {
    fn as_der(&self) -> Result<Pkcs8V1Der<'static>, Unspecified> {
        Ok(Pkcs8V1Der::new(self.0.pkcs8_seed()?.as_ref().to_vec()))
    }
}

impl fmt::Debug for PqdsaPrivateKey<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PqdsaPrivateKey({:?})", self.0.algorithm.0.id())
    }
}

/// Whether `pkcs8` is a private key of a type aws-lc-rs parses that is not
/// ML-DSA. The OID is public; only the parser for that OID runs, and only a
/// successful parse is `WrongAlgorithm`.
fn parses_as_other_private_key(pkcs8: &[u8]) -> bool {
    let Some(oid) = der::pkcs8_algorithm(pkcs8) else {
        return false;
    };
    match oid {
        // RFC 8410 Ed25519.
        [0x2b, 0x65, 0x70] => rind::signature::Ed25519KeyPair::from_pkcs8(pkcs8).is_ok(),
        // RFC 8410 X25519.
        [0x2b, 0x65, 0x6e] => {
            rind::agreement::PrivateKey::from_pkcs8(&rind::agreement::X25519, pkcs8).is_ok()
        }
        // RFC 5480 `id-ecPublicKey`. The curve is in the parameters. A curve
        // rind does not implement, such as secp256k1, fails these parsers;
        // aws-lc-rs can still parse it, and the README lists that difference.
        [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01] => {
            use rind::signature::sign::{
                ECDSA_P256_SHA256_ASN1, ECDSA_P384_SHA384_ASN1, ECDSA_P521_SHA512_ASN1,
            };
            [
                &ECDSA_P256_SHA256_ASN1,
                &ECDSA_P384_SHA384_ASN1,
                &ECDSA_P521_SHA512_ASN1,
            ]
            .into_iter()
            .any(|algorithm| rind::signature::EcdsaKeyPair::from_pkcs8(algorithm, pkcs8).is_ok())
        }
        // RFC 8017 `rsaEncryption`.
        [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01] => {
            rind::signature::RsaKeyPair::from_pkcs8(pkcs8).is_ok()
        }
        _ => false,
    }
}

/// RFC 5958 v1 around RFC 9881's expanded private key: an `OCTET STRING`
/// holding the raw key, itself inside PKCS#8's `privateKey` `OCTET STRING`.
/// Every length is known up front, so the headers are written in place and
/// the key is copied once.
fn expanded_pkcs8(id: AlgorithmId, raw: &[u8]) -> Vec<u8> {
    let algorithm = algorithm_identifier(id);
    let choice = tlv_len(raw.len());
    let private_key = tlv_len(choice);
    let body = 3 + algorithm.len() + private_key;
    let len = tlv_len(body);
    let mut der = Vec::with_capacity(len);
    push_header(&mut der, 0x30, body);
    der.extend_from_slice(&[0x02, 0x01, 0x00]);
    der.extend_from_slice(algorithm);
    push_header(&mut der, 0x04, choice);
    push_header(&mut der, 0x04, raw.len());
    der.extend_from_slice(raw);
    debug_assert_eq!(der.len(), len);
    der
}

/// `AlgorithmIdentifier` for the parameter set, with no parameters.
fn algorithm_identifier(id: AlgorithmId) -> &'static [u8] {
    match id {
        // id-ml-dsa-44, 2.16.840.1.101.3.4.3.17
        AlgorithmId::ML_DSA_44 => &[
            0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11,
        ],
        // id-ml-dsa-65, 2.16.840.1.101.3.4.3.18
        AlgorithmId::ML_DSA_65 => &[
            0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12,
        ],
        // id-ml-dsa-87, 2.16.840.1.101.3.4.3.19
        AlgorithmId::ML_DSA_87 => &[
            0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x13,
        ],
    }
}

/// The longest body [`push_header`] writes: PKCS#8 around ML-DSA-87's expanded
/// key (version, algorithm identifier, and two octet-string headers).
const MAX_DER_BODY: usize = 3 + 13 + 1 + 3 + 1 + 3 + 4896;
const _: () = assert!(MAX_DER_BODY <= 0xffff);

/// The length of a DER element whose contents are `len` bytes, at most
/// [`MAX_DER_BODY`].
const fn tlv_len(len: usize) -> usize {
    len + match len {
        0..=0x7f => 2,
        0x80..=0xff => 3,
        _ => 4,
    }
}

/// Appends a DER element's tag and length. `len` is a public size, at most
/// [`MAX_DER_BODY`].
fn push_header(out: &mut Vec<u8>, tag: u8, len: usize) {
    debug_assert!(len <= MAX_DER_BODY);
    out.push(tag);
    if len < 0x80 {
        out.push(len as u8);
    } else if len <= 0xff {
        out.extend([0x81, len as u8]);
    } else {
        // `MAX_DER_BODY` fits in two length bytes.
        let len = len as u16;
        out.push(0x82);
        out.extend(len.to_be_bytes());
    }
}
