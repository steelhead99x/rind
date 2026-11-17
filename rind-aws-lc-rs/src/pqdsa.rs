//! ML-DSA (FIPS 204), which aws-lc-rs names PQDSA, backed by rind's
//! `ml_dsa::KeyPair`, whose parameter set is a type where aws-lc-rs's is a
//! value.

use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use rind::ml_dsa::{self, MlDsa44, MlDsa65, MlDsa87};

use crate::digest::Digest;
use crate::encoding::{AsDer, Pkcs8V1Der, PublicKeyX509Der};
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::signature::{KeyPair, ParsedKey, private, verification_algorithm};
use crate::wipe::Wiped;
use crate::{Hex, der, pkcs8};

/// An ML-DSA parameter set.
#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AlgorithmID {
    ML_DSA_44,
    ML_DSA_65,
    ML_DSA_87,
}

impl AlgorithmID {
    const fn public_key_len(&self) -> usize {
        match self {
            Self::ML_DSA_44 => 1312,
            Self::ML_DSA_65 => 1952,
            Self::ML_DSA_87 => 2592,
        }
    }

    const fn private_key_len(&self) -> usize {
        match self {
            Self::ML_DSA_44 => 2560,
            Self::ML_DSA_65 => 4032,
            Self::ML_DSA_87 => 4896,
        }
    }

    const fn signature_len(&self) -> usize {
        match self {
            Self::ML_DSA_44 => 2420,
            Self::ML_DSA_65 => 3309,
            Self::ML_DSA_87 => 4627,
        }
    }

    /// The last byte of the parameter set's OID, `2.16.840.1.101.3.4.3.n`
    /// (RFC 9881).
    const fn oid_last(&self) -> u8 {
        match self {
            Self::ML_DSA_44 => 17,
            Self::ML_DSA_65 => 18,
            Self::ML_DSA_87 => 19,
        }
    }

    /// The object identifier's contents, without its tag and length.
    fn oid(self) -> [u8; 9] {
        [
            0x60,
            0x86,
            0x48,
            0x01,
            0x65,
            0x03,
            0x04,
            0x03,
            self.oid_last(),
        ]
    }

    /// The parameter set whose expanded private key is `len` bytes.
    /// aws-lc-rs selects it from the length before checking the caller's
    /// algorithm (`parse_raw_private_key` in aws-lc-rs 1.19.0
    /// `aws-lc-rs/src/evp_pkey.rs`).
    fn from_raw_len(len: usize) -> Option<Self> {
        [Self::ML_DSA_44, Self::ML_DSA_65, Self::ML_DSA_87]
            .into_iter()
            .find(|id| id.private_key_len() == len)
    }

    /// The parameter set whose object identifier's contents are `oid`.
    fn from_oid(oid: &[u8]) -> Option<Self> {
        [Self::ML_DSA_44, Self::ML_DSA_65, Self::ML_DSA_87]
            .into_iter()
            .find(|id| id.oid().as_slice() == oid)
    }

    /// Parses FIPS 204's encoding of a public key of this parameter set.
    fn parse_raw(&self, bytes: &[u8]) -> Result<ParsedKey, rind::Error> {
        Ok(match self {
            Self::ML_DSA_44 => ParsedKey::MlDsa44(ml_dsa::PublicKey::new(bytes)?),
            Self::ML_DSA_65 => ParsedKey::MlDsa65(ml_dsa::PublicKey::new(bytes)?),
            Self::ML_DSA_87 => ParsedKey::MlDsa87(ml_dsa::PublicKey::new(bytes)?),
        })
    }

    /// Parses a `SubjectPublicKeyInfo` naming this parameter set.
    fn parse_spki(&self, der: &[u8]) -> Result<ParsedKey, rind::Error> {
        Ok(match self {
            Self::ML_DSA_44 => ParsedKey::MlDsa44(ml_dsa::PublicKey::from_spki(der)?),
            Self::ML_DSA_65 => ParsedKey::MlDsa65(ml_dsa::PublicKey::from_spki(der)?),
            Self::ML_DSA_87 => ParsedKey::MlDsa87(ml_dsa::PublicKey::from_spki(der)?),
        })
    }
}

/// ML-DSA verification of one parameter set.
///
/// It takes a public key as FIPS 204's encoding or as a
/// `SubjectPublicKeyInfo`, as aws-lc-rs does.
#[derive(Debug, Eq, PartialEq)]
pub struct PqdsaVerificationAlgorithm {
    pub(crate) id: &'static AlgorithmID,
}

impl private::Verify for PqdsaVerificationAlgorithm {
    fn parse(&self, public_key: &[u8]) -> Result<ParsedKey, KeyRejected> {
        // aws-lc-rs tries a SubjectPublicKeyInfo, then the raw key
        // (`parse_pqdsa_public_key` in aws-lc-rs 1.19.0 `aws-lc-rs/src/pqdsa.rs`).
        // A raw key of another length is `Unspecified`
        // (`parse_raw_public_key` in `aws-lc-rs/src/evp_pkey.rs`), and
        // `Result::or` keeps that error in place of the SPKI failure.
        if let Ok(key) = self.id.parse_spki(public_key) {
            return Ok(key);
        }
        // aws-lc's `EVP_parse_public_key` reads one value and leaves the rest
        // (`crypto/evp_extra/evp_asn1.c`).
        if let Some(prefix) = der::sequence_prefix(public_key)
            && prefix.len() != public_key.len()
            && let Ok(key) = self.id.parse_spki(prefix)
        {
            return Ok(key);
        }
        if public_key.len() == self.id.public_key_len() {
            return self.id.parse_raw(public_key).map_err(KeyRejected::rind);
        }
        Err(KeyRejected::unspecified())
    }

    fn verify_parsed(
        &self,
        key: &ParsedKey,
        msg: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        // A key of another parameter set, or another algorithm, verifies
        // nothing here.
        match (self.id, key) {
            (AlgorithmID::ML_DSA_44, ParsedKey::MlDsa44(key)) => key.verify(msg, signature),
            (AlgorithmID::ML_DSA_65, ParsedKey::MlDsa65(key)) => key.verify(msg, signature),
            (AlgorithmID::ML_DSA_87, ParsedKey::MlDsa87(key)) => key.verify(msg, signature),
            _ => return Err(Unspecified),
        }
        .map_err(unspecified)
    }

    fn verify_parsed_digest(&self, _: &ParsedKey, _: &Digest, _: &[u8]) -> Result<(), Unspecified> {
        Err(Unspecified)
    }
}

verification_algorithm!(PqdsaVerificationAlgorithm);

/// ML-DSA signing of one parameter set.
#[derive(Debug, Eq, PartialEq)]
pub struct PqdsaSigningAlgorithm(pub(crate) &'static PqdsaVerificationAlgorithm);

impl PqdsaSigningAlgorithm {
    /// The length of a signature, in bytes.
    #[must_use]
    pub fn signature_len(&self) -> usize {
        self.0.id.signature_len()
    }

    /// The length of a public key, in bytes.
    #[must_use]
    pub fn public_key_len(&self) -> usize {
        self.0.id.public_key_len()
    }

    /// The length of a seed, in bytes.
    #[must_use]
    pub fn seed_len(&self) -> usize {
        32
    }
}

/// rind's key pair, of whichever parameter set.
// Each set's key has its own allocation: one shared `Arc<Key>` would carry a
// smaller set's key in the largest's space, whose slack a move fills with
// stale stack bytes, a seed among them, that the key's wipe never reaches.
#[derive(Clone)]
enum Key {
    MlDsa44(Arc<ml_dsa::KeyPair<MlDsa44>>),
    MlDsa65(Arc<ml_dsa::KeyPair<MlDsa65>>),
    MlDsa87(Arc<ml_dsa::KeyPair<MlDsa87>>),
}

/// Runs `$body` with `$k` bound to the [`Key`]'s rind key pair.
macro_rules! with_key {
    ($key:expr, $k:ident => $body:expr) => {
        match $key {
            Key::MlDsa44($k) => $body,
            Key::MlDsa65($k) => $body,
            Key::MlDsa87($k) => $body,
        }
    };
}

/// Calls rind's `ml_dsa::KeyPair::$method($args)` for `$id`'s parameter set,
/// returning a [`Key`].
macro_rules! new_key {
    ($id:expr, $method:ident($($arg:expr),*)) => {
        match $id {
            AlgorithmID::ML_DSA_44 => ml_dsa::KeyPair::$method($($arg),*).map(|k| Key::MlDsa44(Arc::new(k))),
            AlgorithmID::ML_DSA_65 => ml_dsa::KeyPair::$method($($arg),*).map(|k| Key::MlDsa65(Arc::new(k))),
            AlgorithmID::ML_DSA_87 => ml_dsa::KeyPair::$method($($arg),*).map(|k| Key::MlDsa87(Arc::new(k))),
        }
    };
}

/// An ML-DSA private key and its public key.
#[derive(Clone)]
pub struct PqdsaKeyPair {
    algorithm: &'static PqdsaSigningAlgorithm,
    key: Key,
    public_key: PqdsaPublicKey,
}

impl PqdsaKeyPair {
    fn new(algorithm: &'static PqdsaSigningAlgorithm, key: Key) -> Self {
        let public_key = with_key!(&key, k => k.public_key().as_ref().to_vec());
        Self {
            algorithm,
            key,
            public_key: PqdsaPublicKey {
                id: algorithm.0.id,
                bytes: Arc::new(Wiped::new(public_key)),
            },
        }
    }

    /// Generates a key pair from the system random source.
    pub fn generate(algorithm: &'static PqdsaSigningAlgorithm) -> Result<Self, Unspecified> {
        let key = new_key!(algorithm.0.id, generate()).map_err(unspecified)?;
        Ok(Self::new(algorithm, key))
    }

    /// Loads a PKCS#8 key: its seed, its expanded key, or both, which must
    /// agree.
    pub fn from_pkcs8(
        algorithm: &'static PqdsaSigningAlgorithm,
        pkcs8: &[u8],
    ) -> Result<Self, KeyRejected> {
        // The algorithm identifier is public, so it picks the refusal before
        // any key is expanded. Only the parameter set it names is parsed.
        // aws-lc-rs 1.19.0 `parse_rfc5208_private_key` (`aws-lc-rs/src/evp_pkey.rs`)
        // returns `InvalidEncoding` when `EVP_parse_private_key` fails and
        // `WrongAlgorithm` when the parsed key is not PQDSA. A parsed ML-DSA
        // key of another parameter set then fails `validate_pqdsa_evp_key`
        // (`aws-lc-rs/src/pqdsa.rs`) as `Unspecified`.
        let named = der::pkcs8_algorithm(pkcs8).map(AlgorithmID::from_oid);
        match named {
            Some(Some(id)) if algorithm.0.id != &id => Err(other_parameter_set(&id, pkcs8)),
            Some(None) => {
                if parses_as_other_private_key(pkcs8) {
                    Err(KeyRejected::wrong_algorithm())
                } else {
                    Err(KeyRejected::invalid_encoding())
                }
            }
            Some(Some(id)) => {
                let key = load_mldsa_pkcs8(&id, pkcs8).map_err(KeyRejected::rind)?;
                Ok(Self::new(algorithm, key))
            }
            None => {
                let key = new_key!(algorithm.0.id, from_pkcs8(pkcs8)).map_err(KeyRejected::rind)?;
                Ok(Self::new(algorithm, key))
            }
        }
    }

    /// Loads FIPS 204's expanded private key. The key pair then has no seed,
    /// so [`Self::to_pkcs8v1`] fails.
    pub fn from_raw_private_key(
        algorithm: &'static PqdsaSigningAlgorithm,
        raw_private_key: &[u8],
    ) -> Result<Self, KeyRejected> {
        // aws-lc-rs picks the parameter set from the length and loads the
        // key as that set, then refuses a key of another set as
        // `Unspecified` (`validate_pqdsa_evp_key`). Loading runs the
        // consistency check first, so an inconsistent key of another set is
        // `InvalidEncoding`, as `other_parameter_set` does for PKCS#8. Any
        // other length is `InvalidEncoding`.
        let Some(id) = AlgorithmID::from_raw_len(raw_private_key.len()) else {
            return Err(KeyRejected::invalid_encoding());
        };
        // rind loads an expanded key only as PKCS#8 (RFC 9881's
        // `expandedKey`), so wrap it in one. aws-lc-rs 1.19.0
        // `parse_raw_private_key` (`aws-lc-rs/src/evp_pkey.rs`) maps every
        // failure of `EVP_PKEY_pqdsa_new_raw_private_key` at this length to
        // `InvalidEncoding`.
        let pkcs8 = expanded_pkcs8(&id, raw_private_key);
        let key = new_key!(&id, from_pkcs8(&pkcs8)).map_err(|_| KeyRejected::invalid_encoding())?;
        if algorithm.0.id != &id {
            return Err(KeyRejected::unspecified());
        }
        Ok(Self::new(algorithm, key))
    }

    /// Expands a 32-byte seed into its key pair, as FIPS 204's key
    /// generation does.
    pub fn from_seed(
        algorithm: &'static PqdsaSigningAlgorithm,
        seed: &[u8],
    ) -> Result<Self, KeyRejected> {
        match seed.len().cmp(&algorithm.seed_len()) {
            core::cmp::Ordering::Less => return Err(KeyRejected::too_small()),
            core::cmp::Ordering::Greater => return Err(KeyRejected::too_large()),
            core::cmp::Ordering::Equal => {}
        }
        let key = new_key!(algorithm.0.id, from_seed(seed)).map_err(KeyRejected::rind)?;
        Ok(Self::new(algorithm, key))
    }

    /// Encodes the private key's seed as PKCS#8 v1, failing for a key loaded
    /// from its expanded form, which has none.
    pub fn to_pkcs8v1(&self) -> Result<pkcs8::Document, Unspecified> {
        with_key!(&self.key, k => match k.has_seed() {
            true => Ok(pkcs8::Document::new(k.to_pkcs8().as_ref())),
            false => Err(Unspecified),
        })
    }

    /// Encodes the private key as [`Self::to_pkcs8v1`] does.
    #[cfg(feature = "unstable")]
    #[deprecated(since = "1.18.0", note = "use `PqdsaKeyPair::to_pkcs8v1`")]
    pub fn to_pkcs8(&self) -> Result<pkcs8::Document, Unspecified> {
        self.to_pkcs8v1()
    }

    /// Signs `msg` into `signature`, which must hold at least
    /// [`PqdsaSigningAlgorithm::signature_len`] bytes, and returns the
    /// signature's length.
    pub fn sign(&self, msg: &[u8], signature: &mut [u8]) -> Result<usize, Unspecified> {
        let len = self.algorithm.signature_len();
        let out = signature.get_mut(..len).ok_or(Unspecified)?;
        with_key!(&self.key, k => {
            out.copy_from_slice(k.sign(msg).map_err(unspecified)?.as_ref());
        });
        Ok(len)
    }

    /// The key pair's algorithm.
    #[must_use]
    pub fn algorithm(&self) -> &'static PqdsaSigningAlgorithm {
        self.algorithm
    }

    /// The private key.
    #[must_use]
    pub fn private_key(&self) -> PqdsaPrivateKey<'_> {
        PqdsaPrivateKey(self)
    }
}

impl KeyPair for PqdsaKeyPair {
    type PublicKey = PqdsaPublicKey;

    fn public_key(&self) -> &PqdsaPublicKey {
        &self.public_key
    }
}

impl fmt::Debug for PqdsaKeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PqdsaKeyPair")
            .field("algorithm", &self.algorithm)
            .finish()
    }
}

/// Wraps an expanded private key in PKCS#8 v1, as RFC 9881's `expandedKey`.
fn expanded_pkcs8(id: &AlgorithmID, key: &[u8]) -> Vec<u8> {
    /// A DER header with a two-byte length, which every ML-DSA key needs.
    fn header(out: &mut Vec<u8>, tag: u8, len: usize) {
        let len = u16::try_from(len).expect("ML-DSA keys are under 64 KiB");
        out.push(tag);
        out.push(0x82);
        out.extend_from_slice(&len.to_be_bytes());
    }
    // `version` 0, then the `AlgorithmIdentifier` with the parameter set's OID.
    let prefix = [
        0x02,
        0x01,
        0x00,
        0x30,
        0x0b,
        0x06,
        0x09,
        0x60,
        0x86,
        0x48,
        0x01,
        0x65,
        0x03,
        0x04,
        0x03,
        id.oid_last(),
    ];
    // A copy of the key inside one call, which the repository leaves unwiped.
    let mut der = Vec::with_capacity(prefix.len() + key.len() + 12);
    header(&mut der, 0x30, prefix.len() + key.len() + 8);
    der.extend_from_slice(&prefix);
    header(&mut der, 0x04, key.len() + 4);
    header(&mut der, 0x04, key.len());
    der.extend_from_slice(key);
    der
}

/// An ML-DSA key pair's private key.
pub struct PqdsaPrivateKey<'a>(&'a PqdsaKeyPair);

impl AsDer<Pkcs8V1Der<'static>> for PqdsaPrivateKey<'_> {
    /// Encodes the private key as [`PqdsaKeyPair::to_pkcs8v1`] does.
    fn as_der(&self) -> Result<Pkcs8V1Der<'static>, Unspecified> {
        Ok(Pkcs8V1Der::new(self.0.to_pkcs8v1()?.as_ref().to_vec()))
    }
}

impl fmt::Debug for PqdsaPrivateKey<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PqdsaPrivateKey({:?})", self.0.algorithm.0.id)
    }
}

/// An ML-DSA key pair's public key, FIPS 204's encoding; wiped on drop, as
/// the key pair is.
#[derive(Clone)]
pub struct PqdsaPublicKey {
    id: &'static AlgorithmID,
    bytes: Arc<Wiped<Vec<u8>>>,
}

impl AsRef<[u8]> for PqdsaPublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl AsDer<PublicKeyX509Der<'static>> for PqdsaPublicKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        let key = self.id.parse_raw(&self.bytes).map_err(unspecified)?;
        Ok(PublicKeyX509Der::new(key.to_spki().as_ref().to_vec()))
    }
}

impl fmt::Debug for PqdsaPublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PqdsaPublicKey(")?;
        fmt::Debug::fmt(&Hex(self.as_ref()), f)?;
        f.write_str(")")
    }
}

/// Refuses a PKCS#8 key whose algorithm is another ML-DSA parameter set.
///
/// The key is loaded in full as the set it names, as aws-lc's
/// `pqdsa_priv_decode` (`crypto/evp_extra/p_pqdsa_asn1.c`) does before
/// aws-lc-rs's `validate_pqdsa_evp_key` refuses the set. A key that fails to
/// load keeps that refusal, `InvalidEncoding` for an inconsistent expanded
/// key, and one that loads is `Unspecified`.
fn other_parameter_set(id: &AlgorithmID, pkcs8: &[u8]) -> KeyRejected {
    match load_mldsa_pkcs8(id, pkcs8) {
        Ok(_) => KeyRejected::unspecified(),
        Err(err) => KeyRejected::rind(err),
    }
}

/// Loads an ML-DSA PKCS#8 key of parameter set `id` as aws-lc reads it,
/// through [`strict_mldsa_pkcs8`].
fn load_mldsa_pkcs8(id: &AlgorithmID, pkcs8: &[u8]) -> Result<Key, rind::Error> {
    let rebuilt = strict_mldsa_pkcs8(id, pkcs8);
    new_key!(id, from_pkcs8(rebuilt.as_deref().unwrap_or(pkcs8)))
}

/// Whether `pkcs8` is a private key of a type aws-lc-rs parses that is not
/// ML-DSA. The OID is public; only the parser for that OID runs, and only a
/// successful parse is `WrongAlgorithm`, as `parse_rfc5208_private_key` does
/// (aws-lc-rs 1.19.0 `aws-lc-rs/src/evp_pkey.rs`). `EVP_parse_private_key`
/// reads one value (`crypto/evp_extra/evp_asn1.c`), so bytes after the
/// document are ignored.
fn parses_as_other_private_key(pkcs8: &[u8]) -> bool {
    let Some(oid) = der::pkcs8_algorithm(pkcs8) else {
        return false;
    };
    let document = der::sequence_prefix(pkcs8).unwrap_or(pkcs8);
    match oid {
        // RFC 8410 Ed25519.
        [0x2b, 0x65, 0x70] => rind::ed25519::KeyPair::from_pkcs8(document).is_ok(),
        // RFC 8410 X25519.
        [0x2b, 0x65, 0x6e] => {
            rind::agreement::PrivateKey::from_pkcs8(&rind::agreement::X25519, document).is_ok()
        }
        // RFC 5480 `id-ecPublicKey`.
        [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01] => ec_private_key(document),
        // RFC 8017 `rsaEncryption`, RFC 4055 `id-RSAES-OAEP`, and X.509's
        // `id-ea-rsa`. `rsa_priv_decode` (`p_rsa_asn1.c`, lines 104-127)
        // rejects a v2 public key and requires NULL parameters.
        [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]
        | [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x07]
        | [0x55, 0x08, 0x01, 0x01] => rsa_private_key(document),
        // RFC 4055 `id-RSASSA-PSS`.
        [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a] => rsa_pss_private_key(document),
        // RFC 9935 ML-KEM. The seed is 64 bytes and the expanded key has the
        // parameter set's length. aws-lc accepts either encoding at that
        // length and does not check the bytes further. `kem_priv_decode`
        // ignores a v2 public key.
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01] => {
            ml_kem_private_key(document, 1632)
        }
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x02] => {
            ml_kem_private_key(document, 2400)
        }
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x03] => {
            ml_kem_private_key(document, 3168)
        }
        // X9.57 `id-dsa`, which rind cannot back, decided from its OID
        // alone without reading the private key.
        [0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01] => true,
        _ => false,
    }
}

/// An RSASSA-PSS private key. `rsa_pss_priv_decode` (`p_rsa_asn1.c`) does not
/// reject a v2 public key. Parameters may be absent, empty, or an explicit
/// hash that `RSASSA_PSS_parse_params` accepts.
fn rsa_pss_private_key(pkcs8: &[u8]) -> bool {
    let Some(parts) = der::pkcs8_parts(pkcs8) else {
        return false;
    };
    if !pss_parameters_ok(parts.parameters) {
        return false;
    }
    rind::rsa::KeyPair::from_pkcs1(parts.private_key).is_ok()
        || unbacked_rsa_size(parts.private_key)
}

/// `rsa_priv_decode`: NULL parameters, no v2 public key, and components that
/// agree, which rind checks for a modulus of 2048 to 8192 bits.
fn rsa_private_key(pkcs8: &[u8]) -> bool {
    let Some(parts) = der::pkcs8_parts(pkcs8) else {
        return false;
    };
    if parts.has_public_key || parts.parameters != [0x05, 0x00] {
        return false;
    }
    rind::rsa::KeyPair::from_pkcs8(pkcs8).is_ok() || unbacked_rsa_size(parts.private_key)
}

/// Whether a PKCS#1 `RSAPrivateKey`'s modulus is outside the 2048 to 8192
/// bits rind signs with. rind cannot back such a key, so it is refused as
/// another algorithm from that public length alone, without reading the
/// private components.
fn unbacked_rsa_size(pkcs1: &[u8]) -> bool {
    let Some((0x30, body)) = der::first_element(pkcs1) else {
        return false;
    };
    let Some(version) = der::leading_element(body) else {
        return false;
    };
    let Some((0x02, modulus)) = body.get(version.len()..).and_then(der::first_element) else {
        return false;
    };
    !(2048..=8192).contains(&der::bits(modulus))
}

/// An ML-KEM private key in RFC 9935's seed form or expanded form.
fn ml_kem_private_key(pkcs8: &[u8], expanded_len: usize) -> bool {
    let Some(parts) = der::pkcs8_parts(pkcs8) else {
        return false;
    };
    if !parts.parameters.is_empty() {
        return false;
    }
    // aws-lc reads one inner value and does not require it to end the
    // private key.
    match der::first_element(parts.private_key) {
        Some((0x80, seed)) => seed.len() == 64,
        Some((0x04, expanded)) => expanded.len() == expanded_len,
        _ => false,
    }
}

/// A PKCS#8 document rind's ML-DSA parser accepts, or `None` when `pkcs8`
/// already is one. aws-lc ignores bytes after the document, bytes after the
/// single private-key element, and the v2 public key (`pqdsa_priv_decode`
/// does not read `pubkey`).
fn strict_mldsa_pkcs8(id: &AlgorithmID, pkcs8: &[u8]) -> Option<Vec<u8>> {
    let parts = der::pkcs8_parts(pkcs8)?;
    if !parts.parameters.is_empty() {
        return None;
    }
    let element = der::leading_element(parts.private_key)?;
    let strip = der::pkcs8_trailing(pkcs8)
        || parts.has_public_key
        || element.len() != parts.private_key.len();
    if !strip {
        return None;
    }
    encode_mldsa_pkcs8(id, element)
}

fn encode_mldsa_pkcs8(id: &AlgorithmID, private_key: &[u8]) -> Option<Vec<u8>> {
    let oid = der_tlv(0x06, &id.oid())?;
    let algorithm = der_tlv(0x30, &oid)?;
    let key = der_tlv(0x04, private_key)?;
    let mut body = vec![0x02, 0x01, 0x00];
    body.extend(algorithm);
    body.extend(key);
    der_tlv(0x30, &body)
}

fn der_tlv(tag: u8, body: &[u8]) -> Option<Vec<u8>> {
    let mut out = Vec::with_capacity(body.len() + 4);
    out.push(tag);
    if body.len() < 0x80 {
        out.push(body.len() as u8);
    } else if body.len() <= 0xff {
        out.extend([0x81, body.len() as u8]);
    } else {
        let len = u16::try_from(body.len()).ok()?;
        out.push(0x82);
        out.extend(len.to_be_bytes());
    }
    out.extend_from_slice(body);
    Some(out)
}

/// P-256, P-384, and P-521 through rind, including a scalar shorter than the
/// field. A curve rind cannot back is decided from its OID alone.
fn ec_private_key(pkcs8: &[u8]) -> bool {
    use rind::ecdsa::sign::{
        P256_SHA256_ASN1 as ECDSA_P256_SHA256_ASN1, P384_SHA384_ASN1 as ECDSA_P384_SHA384_ASN1,
        P521_SHA512_ASN1 as ECDSA_P521_SHA512_ASN1,
    };
    if unbacked_curve(pkcs8) {
        return true;
    }
    let padded = padded_ec_scalar(pkcs8);
    [
        &ECDSA_P256_SHA256_ASN1,
        &ECDSA_P384_SHA384_ASN1,
        &ECDSA_P521_SHA512_ASN1,
    ]
    .into_iter()
    .any(|algorithm| {
        rind::ecdsa::KeyPair::from_pkcs8(algorithm, pkcs8).is_ok()
            || padded
                .as_ref()
                .is_some_and(|padded| rind::ecdsa::KeyPair::from_pkcs8(algorithm, padded).is_ok())
    })
}

/// A scalar shorter than the field, left-padded with zeros, for P-256,
/// P-384, or P-521. aws-lc accepts that encoding when the value is below
/// the order (`EC_KEY_parse_private_key`).
fn padded_ec_scalar(pkcs8: &[u8]) -> Option<Vec<u8>> {
    let parts = der::pkcs8_parts(pkcs8)?;
    if parts.has_public_key {
        return None;
    }
    let field = field_len(curve_oid(parts.parameters)?)?;
    if der::leading_element(parts.private_key)?.len() != parts.private_key.len() {
        return None;
    }
    let (_, seq) = der::first_element(parts.private_key)?;
    let version = der::leading_element(seq)?;
    let rest = seq.get(version.len()..)?;
    let scalar_enc = der::leading_element(rest)?;
    let (_, scalar) = der::first_element(rest)?;
    if scalar.is_empty() || scalar.len() >= field {
        return None;
    }
    let mut padded_scalar = vec![0u8; field - scalar.len()];
    padded_scalar.extend_from_slice(scalar);
    let tail = rest.get(scalar_enc.len()..)?;
    let mut inner = version.to_vec();
    inner.extend(der_tlv(0x04, &padded_scalar)?);
    inner.extend_from_slice(tail);
    let sec1 = der_tlv(0x30, &inner)?;
    let mut algorithm = der_tlv(0x06, &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01])?;
    algorithm.extend_from_slice(parts.parameters);
    let algorithm = der_tlv(0x30, &algorithm)?;
    let key = der_tlv(0x04, &sec1)?;
    let mut body = vec![0x02, 0x01, 0x00];
    body.extend(algorithm);
    body.extend(key);
    der_tlv(0x30, &body)
}

fn field_len(oid: &[u8]) -> Option<usize> {
    Some(match oid {
        [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07] => 32,
        [0x2b, 0x81, 0x04, 0x00, 0x22] => 48,
        [0x2b, 0x81, 0x04, 0x00, 0x23] => 66,
        _ => return None,
    })
}

fn curve_oid(parameters: &[u8]) -> Option<&[u8]> {
    let (tag, oid) = der::first_element(parameters)?;
    if tag != 0x06 || der::leading_element(parameters)?.len() != parameters.len() {
        return None;
    }
    Some(oid)
}

/// secp256k1, secp224r1, and brainpoolP256r1, which rind cannot back. A key
/// naming one is refused as another algorithm from that public OID, without
/// reading its secret scalar.
fn unbacked_curve(pkcs8: &[u8]) -> bool {
    der::pkcs8_parts(pkcs8)
        .and_then(|parts| curve_oid(parts.parameters))
        .is_some_and(|oid| {
            matches!(
                oid,
                [0x2b, 0x81, 0x04, 0x00, 0x0a]
                    | [0x2b, 0x81, 0x04, 0x00, 0x21]
                    | [0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07]
            )
        })
}

/// Absent parameters, an empty `RSASSA-PSS-params`, or one explicit hash
/// `RSASSA_PSS_parse_params` accepts (`crypto/rsa_extra/rsassa_pss_asn1.c`).
fn pss_parameters_ok(parameters: &[u8]) -> bool {
    if parameters.is_empty() || parameters == [0x30, 0x00] {
        return true;
    }
    let Some((0x30, mut body)) = der::first_element(parameters) else {
        return false;
    };
    if der::leading_element(parameters).is_none_or(|enc| enc.len() != parameters.len()) {
        return false;
    }
    if body.is_empty() {
        return true;
    }
    if let Some((hash, rest)) = explicit_field(body, 0xa0) {
        if !one_way_hash(hash) {
            return false;
        }
        body = rest;
    }
    if let Some((mgf, rest)) = explicit_field(body, 0xa1) {
        if !mgf1(mgf) {
            return false;
        }
        body = rest;
    }
    if let Some((salt, rest)) = explicit_field(body, 0xa2) {
        if !nonnegative_int(salt) {
            return false;
        }
        body = rest;
    }
    if let Some((trailer, rest)) = explicit_field(body, 0xa3) {
        if !der_int_value(trailer).is_some_and(|value| value == 1) {
            return false;
        }
        body = rest;
    }
    body.is_empty()
}

/// `Some` when the field is present: its contents and what follows it.
fn explicit_field(body: &[u8], tag: u8) -> Option<(&[u8], &[u8])> {
    if body.first() != Some(&tag) {
        return None;
    }
    let enc = der::leading_element(body)?;
    let (_, inner) = der::first_element(body)?;
    Some((inner, &body[enc.len()..]))
}

fn one_way_hash(explicit: &[u8]) -> bool {
    let Some(seq) = der::leading_element(explicit) else {
        return false;
    };
    if seq.len() != explicit.len() {
        return false;
    }
    let Some((0x30, ident)) = der::first_element(explicit) else {
        return false;
    };
    let Some(oid_enc) = der::leading_element(ident) else {
        return false;
    };
    let Some((0x06, oid)) = der::first_element(ident) else {
        return false;
    };
    let known = matches!(
        oid,
        // SHA-1, SHA-256, SHA-384, SHA-512, and SHA-224, as `cbs_to_md`
        // (`crypto/rsa_extra/rsassa_pss_asn1.c`) accepts.
        [0x2b, 0x0e, 0x03, 0x02, 0x1a]
            | [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x04]
            | [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
            | [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02]
            | [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03]
    );
    let rest = &ident[oid_enc.len()..];
    known && (rest.is_empty() || rest == [0x05, 0x00])
}

/// MGF1 with a hash `decode_mask_gen` accepts. The OID is
/// `1.2.840.113549.1.1.8`.
fn mgf1(explicit: &[u8]) -> bool {
    let Some(seq) = der::leading_element(explicit) else {
        return false;
    };
    if seq.len() != explicit.len() {
        return false;
    }
    let Some((0x30, body)) = der::first_element(explicit) else {
        return false;
    };
    let Some(oid_enc) = der::leading_element(body) else {
        return false;
    };
    let Some((0x06, oid)) = der::first_element(body) else {
        return false;
    };
    oid == [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x08]
        && one_way_hash(&body[oid_enc.len()..])
}

fn nonnegative_int(body: &[u8]) -> bool {
    der_int_value(body).is_some()
}

fn der_int_value(body: &[u8]) -> Option<u64> {
    let enc = der::leading_element(body)?;
    if enc.len() != body.len() {
        return None;
    }
    let (0x02, bytes) = der::first_element(body)? else {
        return None;
    };
    // `CBS_get_asn1_int64` accepts a positive value through `i64::MAX`, which
    // is nine bytes when the magnitude's top bit is set.
    if bytes.is_empty() || bytes[0] >= 0x80 || bytes.len() > 9 {
        return None;
    }
    let bytes = if bytes.len() == 9 {
        if bytes[0] != 0 {
            return None;
        }
        &bytes[1..]
    } else {
        bytes
    };
    if bytes.len() == 8 && bytes[0] >= 0x80 {
        return None;
    }
    let mut value = 0u64;
    for byte in bytes {
        value = (value << 8) | u64::from(*byte);
    }
    Some(value)
}
