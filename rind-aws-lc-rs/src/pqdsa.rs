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
                let rebuilt = strict_mldsa_pkcs8(&id, pkcs8);
                let document: &[u8] = match rebuilt.as_deref() {
                    Some(bytes) => bytes,
                    None => pkcs8,
                };
                let key = new_key!(id, from_pkcs8(document)).map_err(KeyRejected::rind)?;
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
/// A seed-form key is decided from public lengths. aws-lc's
/// `pqdsa_priv_decode` (`crypto/evp_extra/p_pqdsa_asn1.c`) rejects any seed
/// other than 32 bytes before keygen, and keygen accepts every 32-byte seed,
/// so the parameter-set check is then `Unspecified` with no expansion. An
/// expanded key still runs the consistency check: `pk_from_sk` rejects an
/// inconsistent key, which is `InvalidEncoding`, and accepts a consistent
/// one, which is then `Unspecified`. Bytes after the document are unread,
/// as `EVP_parse_private_key` reads one value, and bytes after the seed
/// element are unread (`pqdsa_priv_decode`, aws-lc-sys 0.47.0
/// `crypto/evp_extra/p_pqdsa_asn1.c`, lines 198-211).
fn other_parameter_set(id: &AlgorithmID, pkcs8: &[u8]) -> KeyRejected {
    if let Some(parts) = der::pkcs8_parts(pkcs8) {
        if !parts.parameters.is_empty() {
            return KeyRejected::invalid_encoding();
        }
        if let Some((0x80, seed)) = der::first_element(parts.private_key) {
            return if seed.len() == 32 {
                KeyRejected::unspecified()
            } else {
                KeyRejected::invalid_encoding()
            };
        }
    }
    match new_key!(id, from_pkcs8(pkcs8)) {
        Ok(_) => KeyRejected::unspecified(),
        Err(err) => KeyRejected::rind(err),
    }
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
        // X9.57 `id-dsa`. `dsa_check_key` (`crypto/dsa/dsa_asn1.c`, lines
        // 22-79) checks bounds, not primality.
        [0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01] => dsa_private_key(document),
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
        || rind::rsa::KeyPair::pkcs1_components_agree(parts.private_key)
}

/// `rsa_priv_decode`: NULL parameters, no v2 public key, and components that
/// agree. A modulus outside 2048 to 8192 bits still agrees when the same
/// relations hold; rind's loader refuses that size.
fn rsa_private_key(pkcs8: &[u8]) -> bool {
    let Some(parts) = der::pkcs8_parts(pkcs8) else {
        return false;
    };
    if parts.has_public_key || parts.parameters != [0x05, 0x00] {
        return false;
    }
    rind::rsa::KeyPair::from_pkcs8(pkcs8).is_ok()
        || rind::rsa::KeyPair::pkcs1_components_agree(parts.private_key)
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
/// field. Other named curves aws-lc parses are checked against the order
/// and, when a public point is present, the curve equation.
fn ec_private_key(pkcs8: &[u8]) -> bool {
    use rind::ecdsa::sign::{
        P256_SHA256_ASN1 as ECDSA_P256_SHA256_ASN1, P384_SHA384_ASN1 as ECDSA_P384_SHA384_ASN1,
        P521_SHA512_ASN1 as ECDSA_P521_SHA512_ASN1,
    };
    if [
        &ECDSA_P256_SHA256_ASN1,
        &ECDSA_P384_SHA384_ASN1,
        &ECDSA_P521_SHA512_ASN1,
    ]
    .into_iter()
    .any(|algorithm| rind::ecdsa::KeyPair::from_pkcs8(algorithm, pkcs8).is_ok())
    {
        return true;
    }
    let Some(padded) = padded_ec_scalar(pkcs8) else {
        return named_curve_private_key(pkcs8);
    };
    [
        &ECDSA_P256_SHA256_ASN1,
        &ECDSA_P384_SHA384_ASN1,
        &ECDSA_P521_SHA512_ASN1,
    ]
    .into_iter()
    .any(|algorithm| rind::ecdsa::KeyPair::from_pkcs8(algorithm, &padded).is_ok())
        || named_curve_private_key(pkcs8)
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

/// secp256k1, secp224r1, and brainpoolP256r1. The scalar is secret; the
/// order comparison does not return early. A public point is on the curve
/// equation when it is present (`EC_POINT_oct2point` then `EC_KEY_check_key`).
fn named_curve_private_key(pkcs8: &[u8]) -> bool {
    let Some(parts) = der::pkcs8_parts(pkcs8) else {
        return false;
    };
    if parts.has_public_key {
        return false;
    }
    let Some(oid) = curve_oid(parts.parameters) else {
        return false;
    };
    let Some(curve) = NamedCurve::from_oid(oid) else {
        return false;
    };
    let Ok((_, seq)) = first_body(parts.private_key) else {
        return false;
    };
    let Some(version) = der::leading_element(seq) else {
        return false;
    };
    let Some(rest) = seq.get(version.len()..) else {
        return false;
    };
    let Some(scalar_enc) = der::leading_element(rest) else {
        return false;
    };
    let Some((0x04, scalar)) = der::first_element(rest) else {
        return false;
    };
    if !scalar_in_range(scalar, curve.order) {
        return false;
    }
    let tail = &rest[scalar_enc.len()..];
    if tail.is_empty() {
        return true;
    }
    // Optional [0] parameters, then [1] public key.
    let mut tail = tail;
    if tail.first() == Some(&0xa0) {
        let Some(enc) = der::leading_element(tail) else {
            return false;
        };
        tail = &tail[enc.len()..];
    }
    if tail.is_empty() {
        return true;
    }
    let Some((0xa1, wrapped)) = split_tag(tail) else {
        return false;
    };
    if der::leading_element(tail).is_none_or(|enc| enc.len() != tail.len()) {
        return false;
    }
    let Some((0x03, bits)) = split_tag(wrapped) else {
        return false;
    };
    if der::leading_element(wrapped).is_none_or(|enc| enc.len() != wrapped.len()) {
        return false;
    }
    public_point_matches(bits, scalar, &curve)
}

fn first_body(der: &[u8]) -> Result<(u8, &[u8]), ()> {
    let Some(enc) = der::leading_element(der) else {
        return Err(());
    };
    if enc.len() != der.len() {
        return Err(());
    }
    der::first_element(der).ok_or(())
}

fn split_tag(der: &[u8]) -> Option<(u8, &[u8])> {
    let (tag, body) = der::first_element(der)?;
    Some((tag, body))
}

struct NamedCurve {
    order: &'static [u8],
    prime: &'static [u8],
    a: &'static [u8],
    b: &'static [u8],
    gx: &'static [u8],
    gy: &'static [u8],
}

impl NamedCurve {
    fn from_oid(oid: &[u8]) -> Option<Self> {
        // Orders and field parameters from OpenSSL's `ecparam -text`.
        const K1_N: &[u8] = &hex_32(
            0xffffffff, 0xffffffff, 0xffffffff, 0xfffffffe, 0xbaaedce6, 0xaf48a03b, 0xbfd25e8c,
            0xd0364141,
        );
        const K1_P: &[u8] = &hex_32(
            0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xfffffffe,
            0xfffffc2f,
        );
        const P224_N: &[u8] = &[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0x16, 0xa2, 0xe0, 0xb8, 0xf0, 0x3e, 0x13, 0xdd, 0x29, 0x45, 0x5c, 0x5c, 0x2a, 0x3d,
        ];
        const P224_P: &[u8] = &[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
        ];
        const P224_A: &[u8] = &[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xfe, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
        ];
        const P224_B: &[u8] = &[
            0xb4, 0x05, 0x0a, 0x85, 0x0c, 0x04, 0xb3, 0xab, 0xf5, 0x41, 0x32, 0x56, 0x50, 0x44,
            0xb0, 0xb7, 0xd7, 0xbf, 0xd8, 0xba, 0x27, 0x0b, 0x39, 0x43, 0x23, 0x55, 0xff, 0xb4,
        ];
        const BP_N: &[u8] = &hex_32(
            0xa9fb57db, 0xa1eea9bc, 0x3e660a90, 0x9d838d71, 0x8c397aa3, 0xb561a6f7, 0x901e0e82,
            0x974856a7,
        );
        const BP_P: &[u8] = &hex_32(
            0xa9fb57db, 0xa1eea9bc, 0x3e660a90, 0x9d838d72, 0x6e3bf623, 0xd5262028, 0x2013481d,
            0x1f6e5377,
        );
        const BP_A: &[u8] = &hex_32(
            0x7d5a0975, 0xfc2c3057, 0xeef67530, 0x417affe7, 0xfb8055c1, 0x26dc5c6c, 0xe94a4b44,
            0xf330b5d9,
        );
        const BP_B: &[u8] = &hex_32(
            0x26dc5c6c, 0xe94a4b44, 0xf330b5d9, 0xbbd77cbf, 0x95841629, 0x5cf7e1ce, 0x6bccdc18,
            0xff8c07b6,
        );
        const K1_GX: &[u8] = &hex_32(
            0x79be667e, 0xf9dcbbac, 0x55a06295, 0xce870b07, 0x029bfcdb, 0x2dce28d9, 0x59f2815b,
            0x16f81798,
        );
        const K1_GY: &[u8] = &hex_32(
            0x483ada77, 0x26a3c465, 0x5da4fbfc, 0x0e1108a8, 0xfd17b448, 0xa6855419, 0x9c47d08f,
            0xfb10d4b8,
        );
        const P224_GX: &[u8] = &[
            0xb7, 0x0e, 0x0c, 0xbd, 0x6b, 0xb4, 0xbf, 0x7f, 0x32, 0x13, 0x90, 0xb9, 0x4a, 0x03,
            0xc1, 0xd3, 0x56, 0xc2, 0x11, 0x22, 0x34, 0x32, 0x80, 0xd6, 0x11, 0x5c, 0x1d, 0x21,
        ];
        const P224_GY: &[u8] = &[
            0xbd, 0x37, 0x63, 0x88, 0xb5, 0xf7, 0x23, 0xfb, 0x4c, 0x22, 0xdf, 0xe6, 0xcd, 0x43,
            0x75, 0xa0, 0x5a, 0x07, 0x47, 0x64, 0x44, 0xd5, 0x81, 0x99, 0x85, 0x00, 0x7e, 0x34,
        ];
        const BP_GX: &[u8] = &hex_32(
            0x8bd2aeb9, 0xcb7e57cb, 0x2c4b482f, 0xfc81b7af, 0xb9de27e1, 0xe3bd23c2, 0x3a4453bd,
            0x9ace3262,
        );
        const BP_GY: &[u8] = &hex_32(
            0x547ef835, 0xc3dac4fd, 0x97f8461a, 0x14611dc9, 0xc2774513, 0x2ded8e54, 0x5c1d54c7,
            0x2f046997,
        );
        Some(match oid {
            [0x2b, 0x81, 0x04, 0x00, 0x0a] => Self {
                order: K1_N,
                prime: K1_P,
                a: &[0u8],
                b: &[7],
                gx: K1_GX,
                gy: K1_GY,
            },
            [0x2b, 0x81, 0x04, 0x00, 0x21] => Self {
                order: P224_N,
                prime: P224_P,
                a: P224_A,
                b: P224_B,
                gx: P224_GX,
                gy: P224_GY,
            },
            [0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07] => Self {
                order: BP_N,
                prime: BP_P,
                a: BP_A,
                b: BP_B,
                gx: BP_GX,
                gy: BP_GY,
            },
            _ => return None,
        })
    }
}

/// Secret scalar in `(0, order)`, compared without returning early.
fn scalar_in_range(scalar: &[u8], order: &[u8]) -> bool {
    if scalar.is_empty() || scalar.len() > order.len() + 8 {
        return false;
    }
    let mut value = alloc::vec![0u8; order.len()];
    if scalar.len() > order.len() {
        let extra = scalar.len() - order.len();
        let mut high = 0u8;
        for byte in &scalar[..extra] {
            high |= byte;
        }
        if high != 0 {
            return false;
        }
        value.copy_from_slice(&scalar[extra..]);
    } else {
        value[order.len() - scalar.len()..].copy_from_slice(scalar);
    }
    // The leading-zero check above branches on public length and on bytes
    // that would make the integer wider than the order. Those bytes are
    // public framing when the encoding is longer than the order. The value
    // that fits is compared in full.
    ct_nonzero(&value) && ct_less(&value, order)
}

fn ct_nonzero(bytes: &[u8]) -> bool {
    let mut acc = 0u8;
    for byte in bytes {
        acc |= byte;
    }
    acc != 0
}

fn int_less(left: &[u8], right: &[u8]) -> bool {
    let n = left.len().max(right.len());
    let mut a = vec![0u8; n];
    let mut b = vec![0u8; n];
    a[n - left.len()..].copy_from_slice(left);
    b[n - right.len()..].copy_from_slice(right);
    ct_less(&a, &b)
}

fn ct_less(left: &[u8], right: &[u8]) -> bool {
    let mut decided = 0u8;
    let mut less = 0u8;
    for (&x, &y) in left.iter().zip(right) {
        let lt = ((x as u32).wrapping_sub(y as u32) >> 31) as u8;
        let gt = ((y as u32).wrapping_sub(x as u32) >> 31) as u8;
        less |= lt & (decided ^ 1);
        decided |= lt | gt;
    }
    less == 1
}

/// Whether the public point is `scalar * G`. The scalar is secret: the
/// ladder and the field arithmetic do not branch on it. The point's
/// coordinates are public, and only the final equality is revealed.
fn public_point_matches(bit_string: &[u8], scalar: &[u8], curve: &NamedCurve) -> bool {
    let Some(0) = bit_string.first().copied() else {
        return false;
    };
    let Some(point) = bit_string.get(1..) else {
        return false;
    };
    let prime = Fe::from_be(curve.prime);
    let Some((x, y)) = decode_point(point, curve, &prime) else {
        return false;
    };
    let got = mul_base(scalar, curve, &prime);
    let (ax, ay) = affine(&got, &prime);
    let yy = mul(ay, ay, &prime);
    let xx = mul(ax, ax, &prime);
    let right = add(
        add(
            mul(xx, ax, &prime),
            mul(Fe::from_be(curve.a), ax, &prime),
            &prime,
        ),
        Fe::from_be(curve.b),
        &prime,
    );
    yy == right && ax == x && ay == y
}

/// Uncompressed `04 || x || y`, or compressed `02`/`03 || x`. Coordinates
/// are public, so recovering `y` may run in variable time.
fn decode_point(point: &[u8], curve: &NamedCurve, prime: &Fe) -> Option<(Fe, Fe)> {
    let n = curve.prime.len();
    match point {
        [0x04, rest @ ..] if rest.len() == n * 2 => {
            let (x, y) = rest.split_at(n);
            if !int_less(x, curve.prime) || !int_less(y, curve.prime) {
                return None;
            }
            Some((Fe::from_be(x), Fe::from_be(y)))
        }
        [prefix @ (0x02 | 0x03), x @ ..] if x.len() == n && int_less(x, curve.prime) => {
            let x = Fe::from_be(x);
            let mut y = sqrt_y(&x, curve, prime)?;
            let odd = y.0[0] & 1 == 1;
            if odd != (*prefix == 0x03) {
                y = sub(*prime, y, prime);
            }
            Some((x, y))
        }
        _ => None,
    }
}

fn sqrt_y(x: &Fe, curve: &NamedCurve, prime: &Fe) -> Option<Fe> {
    let xx = mul(*x, *x, prime);
    let rhs = add(
        add(
            mul(xx, *x, prime),
            mul(Fe::from_be(curve.a), *x, prime),
            prime,
        ),
        Fe::from_be(curve.b),
        prime,
    );
    let y = field_sqrt(rhs, curve.prime, prime)?;
    (mul(y, y, prime) == rhs).then_some(y)
}

fn field_sqrt(value: Fe, prime_be: &[u8], prime: &Fe) -> Option<Fe> {
    if value == Fe::zero() {
        return Some(value);
    }
    if prime_be.last().is_some_and(|byte| byte & 3 == 3) {
        return Some(modexp(value, &plus_one_over_four(prime_be), prime));
    }
    tonelli(value, prime_be, prime)
}

fn plus_one_over_four(prime_be: &[u8]) -> Vec<u8> {
    let mut out = prime_be.to_vec();
    add_small(&mut out, 1);
    shr(&mut out, 2);
    out
}

fn add_small(bytes: &mut [u8], mut carry: u16) {
    for byte in bytes.iter_mut().rev() {
        let sum = u16::from(*byte) + carry;
        *byte = sum as u8;
        carry = sum >> 8;
        if carry == 0 {
            break;
        }
    }
}

fn shr(bytes: &mut [u8], bits: u32) {
    for _ in 0..bits {
        let mut carry = 0u8;
        for byte in bytes.iter_mut() {
            let next = *byte & 1;
            *byte = (*byte >> 1) | (carry << 7);
            carry = next;
        }
    }
}

fn modexp(base: Fe, exp: &[u8], prime: &Fe) -> Fe {
    let mut out = Fe::one();
    for byte in exp {
        for shift in (0..8).rev() {
            out = mul(out, out, prime);
            if byte >> shift & 1 == 1 {
                out = mul(out, base, prime);
            }
        }
    }
    out
}

/// Square root modulo a prime that is 1 mod 4. `value` is public.
fn tonelli(value: Fe, prime_be: &[u8], prime: &Fe) -> Option<Fe> {
    let mut q = prime_be.to_vec();
    sub_small(&mut q, 1);
    let mut s = 0u32;
    while q.last().is_some_and(|byte| byte & 1 == 0) {
        shr(&mut q, 1);
        s += 1;
    }
    let mut half = prime_be.to_vec();
    sub_small(&mut half, 1);
    shr(&mut half, 1);
    let mut z_be = vec![0u8; prime_be.len()];
    let z = loop {
        *z_be.last_mut()? += 1;
        let legendre = modexp(Fe::from_be(&z_be), &half, prime);
        if legendre == sub(*prime, Fe::one(), prime) {
            break Fe::from_be(&z_be);
        }
        if z_be.last()? == &32 {
            return None;
        }
    };
    let mut q1 = q.clone();
    add_small(&mut q1, 1);
    shr(&mut q1, 1);
    let mut m = s;
    let mut c = modexp(z, &q, prime);
    let mut r = modexp(value, &q1, prime);
    let mut t = modexp(value, &q, prime);
    while t != Fe::one() {
        let mut i = 1u32;
        let mut squared = mul(t, t, prime);
        while squared != Fe::one() {
            i += 1;
            if i == m {
                return None;
            }
            squared = mul(squared, squared, prime);
        }
        let mut b = c;
        for _ in 0..m - i - 1 {
            b = mul(b, b, prime);
        }
        m = i;
        c = mul(b, b, prime);
        t = mul(t, c, prime);
        r = mul(r, b, prime);
    }
    Some(r)
}

fn sub_small(bytes: &mut [u8], mut amount: u8) {
    for byte in bytes.iter_mut().rev() {
        let (diff, borrow) = byte.overflowing_sub(amount);
        *byte = diff;
        if !borrow {
            break;
        }
        amount = 1;
    }
}

/// Eight little-endian limbs. Field elements use the low four; a product
/// uses all eight.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Fe([u64; 8]);

impl Fe {
    fn zero() -> Self {
        Self([0; 8])
    }

    fn one() -> Self {
        Self([1, 0, 0, 0, 0, 0, 0, 0])
    }

    fn from_be(bytes: &[u8]) -> Self {
        let mut limbs = [0u64; 8];
        for (i, &byte) in bytes.iter().rev().enumerate() {
            if i >= 64 {
                break;
            }
            limbs[i / 8] |= u64::from(byte) << ((i % 8) * 8);
        }
        Self(limbs)
    }

    fn is_zero(self) -> u64 {
        let mut acc = 0u64;
        for limb in self.0 {
            acc |= limb;
        }
        u64::from(acc == 0)
    }
}

fn word_lt(left: u64, right: u64) -> u64 {
    u64::from(left.overflowing_sub(right).1)
}

fn cmp_ge(left: &Fe, right: &Fe) -> u64 {
    let mut ge = 1u64;
    let mut decided = 0u64;
    for i in (0..8).rev() {
        let lt = word_lt(left.0[i], right.0[i]);
        let gt = word_lt(right.0[i], left.0[i]);
        ge &= !(lt & (decided ^ 1));
        decided |= lt | gt;
    }
    ge
}

#[allow(clippy::needless_range_loop)]
fn sub_masked(left: &Fe, right: &Fe, mask: u64) -> Fe {
    let m = 0u64.wrapping_sub(mask & 1);
    let mut out = [0u64; 8];
    let mut borrow = 0u64;
    for i in 0..8 {
        let (d1, br1) = left.0[i].overflowing_sub(right.0[i] & m);
        let (d2, br2) = d1.overflowing_sub(borrow);
        out[i] = d2;
        borrow = u64::from(br1 || br2);
    }
    Fe(out)
}

#[allow(clippy::needless_range_loop)]
fn try_shl(value: &Fe, bits: usize) -> Option<Fe> {
    if bits >= 512 {
        return None;
    }
    let words = bits / 64;
    let rem = bits % 64;
    let mut lost = 0u64;
    if words > 0 {
        for limb in &value.0[8 - words..] {
            lost |= limb;
        }
    }
    if rem != 0 {
        lost |= value.0[7 - words] >> (64 - rem);
    }
    if lost != 0 {
        return None;
    }
    let mut out = [0u64; 8];
    for i in words..8 {
        let src = i - words;
        out[i] = value.0[src] << rem;
        if rem != 0 && src > 0 {
            out[i] |= value.0[src - 1] >> (64 - rem);
        }
    }
    Some(Fe(out))
}

fn reduce(mut value: Fe, prime: &Fe) -> Fe {
    for shift in (0..=256).rev() {
        if let Some(shifted) = try_shl(prime, shift) {
            let ge = cmp_ge(&value, &shifted);
            value = sub_masked(&value, &shifted, ge);
        }
    }
    value
}

#[allow(clippy::needless_range_loop)]
fn add(left: Fe, right: Fe, prime: &Fe) -> Fe {
    let mut out = [0u64; 8];
    let mut carry = 0u128;
    for i in 0..8 {
        let sum = u128::from(left.0[i]) + u128::from(right.0[i]) + carry;
        out[i] = sum as u64;
        carry = sum >> 64;
    }
    let sum = Fe(out);
    sub_masked(&sum, prime, cmp_ge(&sum, prime))
}

#[allow(clippy::needless_range_loop)]
fn sub(left: Fe, right: Fe, prime: &Fe) -> Fe {
    // `left + prime - right` stays below `2 * prime` when both are.
    let mut sum = [0u64; 8];
    let mut carry = 0u128;
    for i in 0..8 {
        let wide = u128::from(left.0[i]) + u128::from(prime.0[i]) + carry;
        sum[i] = wide as u64;
        carry = wide >> 64;
    }
    let mut diff = [0u64; 8];
    let mut borrow = 0u64;
    for i in 0..8 {
        let (d1, br1) = sum[i].overflowing_sub(right.0[i]);
        let (d2, br2) = d1.overflowing_sub(borrow);
        diff[i] = d2;
        borrow = u64::from(br1 || br2);
    }
    let diff = Fe(diff);
    sub_masked(&diff, prime, cmp_ge(&diff, prime))
}

fn mul_wide(left: Fe, right: Fe) -> Fe {
    let mut out = [0u64; 8];
    for i in 0..4 {
        let mut carry = 0u128;
        for j in 0..4 {
            let sum =
                u128::from(out[i + j]) + u128::from(left.0[i]) * u128::from(right.0[j]) + carry;
            out[i + j] = sum as u64;
            carry = sum >> 64;
        }
        for step in 0..2 {
            let at = i + 4 + step;
            if at >= 8 {
                break;
            }
            let sum = u128::from(out[at]) + carry;
            out[at] = sum as u64;
            carry = sum >> 64;
        }
    }
    Fe(out)
}

fn mul(left: Fe, right: Fe, prime: &Fe) -> Fe {
    reduce(mul_wide(left, right), prime)
}

#[allow(clippy::needless_range_loop)]
fn cmov(left: Fe, right: Fe, bit: u64) -> Fe {
    let mask = 0u64.wrapping_sub(bit & 1);
    let mut out = [0u64; 8];
    for i in 0..8 {
        out[i] = left.0[i] ^ ((left.0[i] ^ right.0[i]) & mask);
    }
    Fe(out)
}

fn inv(value: Fe, prime: &Fe) -> Fe {
    let exp = sub(*prime, Fe([2, 0, 0, 0, 0, 0, 0, 0]), prime);
    let mut out = Fe::one();
    for index in 0..256 {
        out = mul(out, out, prime);
        let from_top = 255 - index;
        let bit = (exp.0[from_top / 64] >> (from_top % 64)) & 1;
        out = cmov(out, mul(out, value, prime), bit);
    }
    out
}

#[derive(Clone, Copy)]
struct Pt {
    x: Fe,
    y: Fe,
    z: Fe,
}

impl Pt {
    fn infinity() -> Self {
        Self {
            x: Fe::zero(),
            y: Fe::one(),
            z: Fe::zero(),
        }
    }
}

fn cswap_pts(left: &mut Pt, right: &mut Pt, bit: u64) {
    let lx = left.x;
    let ly = left.y;
    let lz = left.z;
    left.x = cmov(left.x, right.x, bit);
    left.y = cmov(left.y, right.y, bit);
    left.z = cmov(left.z, right.z, bit);
    right.x = cmov(right.x, lx, bit);
    right.y = cmov(right.y, ly, bit);
    right.z = cmov(right.z, lz, bit);
}

fn cmov_pt(left: Pt, right: Pt, bit: u64) -> Pt {
    Pt {
        x: cmov(left.x, right.x, bit),
        y: cmov(left.y, right.y, bit),
        z: cmov(left.z, right.z, bit),
    }
}

fn dbl(point: &Pt, prime: &Fe, a: Fe) -> Pt {
    let yy = mul(point.y, point.y, prime);
    let s = mul(
        point.x,
        add(add(yy, yy, prime), add(yy, yy, prime), prime),
        prime,
    );
    let xx = mul(point.x, point.x, prime);
    let three_xx = add(add(xx, xx, prime), xx, prime);
    let zz = mul(point.z, point.z, prime);
    let m = add(three_xx, mul(a, mul(zz, zz, prime), prime), prime);
    let x = sub(mul(m, m, prime), add(s, s, prime), prime);
    let y4 = mul(yy, yy, prime);
    let two_y4 = add(y4, y4, prime);
    let four_y4 = add(two_y4, two_y4, prime);
    let eight = add(four_y4, four_y4, prime);
    let y = sub(mul(m, sub(s, x, prime), prime), eight, prime);
    let z = add(
        mul(point.y, point.z, prime),
        mul(point.y, point.z, prime),
        prime,
    );
    Pt { x, y, z }
}

fn add_pts(left: &Pt, right: &Pt, prime: &Fe) -> Pt {
    let z2z = mul(right.z, right.z, prime);
    let u1 = mul(left.x, z2z, prime);
    let z1z = mul(left.z, left.z, prime);
    let u2 = mul(right.x, z1z, prime);
    let s1 = mul(left.y, mul(z2z, right.z, prime), prime);
    let s2 = mul(right.y, mul(z1z, left.z, prime), prime);
    let h = sub(u2, u1, prime);
    let r = sub(s2, s1, prime);
    let h2 = mul(h, h, prime);
    let h3 = mul(h, h2, prime);
    let u1h2 = mul(u1, h2, prime);
    let x = sub(
        sub(mul(r, r, prime), h3, prime),
        add(u1h2, u1h2, prime),
        prime,
    );
    let y = sub(
        mul(r, sub(u1h2, x, prime), prime),
        mul(s1, h3, prime),
        prime,
    );
    let z = mul(mul(h, left.z, prime), right.z, prime);
    let sum = Pt { x, y, z };
    let sum = cmov_pt(sum, *right, left.z.is_zero());
    cmov_pt(sum, *left, right.z.is_zero())
}

fn affine(point: &Pt, prime: &Fe) -> (Fe, Fe) {
    let zinv = inv(point.z, prime);
    let zinv2 = mul(zinv, zinv, prime);
    (
        mul(point.x, zinv2, prime),
        mul(point.y, mul(zinv2, zinv, prime), prime),
    )
}

fn mul_base(scalar: &[u8], curve: &NamedCurve, prime: &Fe) -> Pt {
    let a = Fe::from_be(curve.a);
    let width = curve.order.len();
    let mut wide = alloc::vec![0u8; width];
    if scalar.len() > width {
        wide.copy_from_slice(&scalar[scalar.len() - width..]);
    } else {
        let start = width - scalar.len();
        wide[start..].copy_from_slice(scalar);
    }
    let mut r0 = Pt::infinity();
    let mut r1 = Pt {
        x: Fe::from_be(curve.gx),
        y: Fe::from_be(curve.gy),
        z: Fe::one(),
    };
    for index in 0..wide.len() * 8 {
        let bit = u64::from((wide[index / 8] >> (7 - (index % 8))) & 1);
        cswap_pts(&mut r0, &mut r1, bit);
        r1 = add_pts(&r0, &r1, prime);
        r0 = dbl(&r0, prime, a);
        cswap_pts(&mut r0, &mut r1, bit);
    }
    r0
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
        [0x2b, 0x0e, 0x03, 0x02, 0x1a]
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

/// X9.57 DSA, bounds only, as `dsa_check_key` (`crypto/dsa/dsa_asn1.c`,
/// lines 22-79). `p`, `q`, and `g` are public. The private key is compared
/// with `q` over its whole width.
fn dsa_private_key(pkcs8: &[u8]) -> bool {
    let Some(parts) = der::pkcs8_parts(pkcs8) else {
        return false;
    };
    if parts.has_public_key {
        return false;
    }
    let Some((0x30, params)) = der::first_element(parts.parameters) else {
        return false;
    };
    let Some(p) = take_int(params) else {
        return false;
    };
    let Some(q) = take_int(&params[p.0.len()..]) else {
        return false;
    };
    let Some(g) = take_int(&params[p.0.len() + q.0.len()..]) else {
        return false;
    };
    if p.0.len() + q.0.len() + g.0.len() != params.len() {
        return false;
    }
    let (p, q, g) = (p.1, q.1, g.1);
    let q_bits = der::bits(q);
    if !matches!(q_bits, 160 | 224 | 256) || der::bits(p) > 10000 || der::bits(p) == 0 {
        return false;
    }
    if p.last().is_none_or(|b| b & 1 == 0) || q.last().is_none_or(|b| b & 1 == 0) {
        return false;
    }
    if !int_less(q, p) || !ct_nonzero(g) || !int_less(g, p) {
        return false;
    }
    let Some((0x02, x)) = der::first_element(parts.private_key) else {
        return false;
    };
    if x.first().is_some_and(|b| *b >= 0x80) {
        return false;
    }
    if der::leading_element(parts.private_key)
        .is_none_or(|enc| enc.len() != parts.private_key.len())
    {
        return false;
    }
    scalar_in_range(x, q)
}

fn take_int(der: &[u8]) -> Option<(Vec<u8>, &[u8])> {
    let enc = der::leading_element(der)?;
    let (tag, body) = der::first_element(der)?;
    if tag != 0x02 || body.is_empty() || body[0] >= 0x80 {
        return None;
    }
    Some((enc.to_vec(), body))
}

#[allow(clippy::too_many_arguments)]
const fn hex_32(a: u32, b: u32, c: u32, d: u32, e: u32, f: u32, g: u32, h: u32) -> [u8; 32] {
    let words = [a, b, c, d, e, f, g, h];
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 8 {
        let w = words[i].to_be_bytes();
        out[i * 4] = w[0];
        out[i * 4 + 1] = w[1];
        out[i * 4 + 2] = w[2];
        out[i * 4 + 3] = w[3];
        i += 1;
    }
    out
}

#[cfg(test)]
mod named_curve_math {
    use super::{Fe, NamedCurve, Pt, add, affine, dbl, mul, mul_base, public_point_matches};

    fn curve(oid: &[u8]) -> NamedCurve {
        NamedCurve::from_oid(oid).unwrap()
    }

    fn on_curve(curve: &NamedCurve) {
        let prime = Fe::from_be(curve.prime);
        let x = Fe::from_be(curve.gx);
        let y = Fe::from_be(curve.gy);
        let yy = mul(y, y, &prime);
        let xx = mul(x, x, &prime);
        let x3 = mul(xx, x, &prime);
        let ax = mul(Fe::from_be(curve.a), x, &prime);
        let right = add(add(x3, ax, &prime), Fe::from_be(curve.b), &prime);
        assert!(yy == right);
    }

    #[test]
    fn generators_satisfy_their_curves() {
        on_curve(&curve(&[0x2b, 0x81, 0x04, 0x00, 0x0a]));
        on_curve(&curve(&[0x2b, 0x81, 0x04, 0x00, 0x21]));
        on_curve(&curve(&[
            0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07,
        ]));
    }

    #[test]
    fn compressed_generators_match_scalar_one() {
        for oid in [
            &[0x2b, 0x81, 0x04, 0x00, 0x0a][..],
            &[0x2b, 0x81, 0x04, 0x00, 0x21],
            &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07],
        ] {
            let curve = curve(oid);
            let y = Fe::from_be(curve.gy);
            let mut point = vec![if y.0[0] & 1 == 0 { 0x02 } else { 0x03 }];
            point.extend_from_slice(curve.gx);
            let mut scalar = vec![0u8; curve.order.len()];
            let last = scalar.len() - 1;
            scalar[last] = 1;
            let mut bits = vec![0x00];
            bits.extend(point);
            assert!(public_point_matches(&bits, &scalar, &curve), "{oid:?}");
        }
    }

    #[test]
    fn base_multiples() {
        let curve = curve(&[0x2b, 0x81, 0x04, 0x00, 0x0a]);
        let mut scalar = vec![0u8; 32];
        scalar[31] = 1;
        let mut bits = vec![0x00, 0x04];
        bits.extend_from_slice(curve.gx);
        bits.extend_from_slice(curve.gy);
        assert!(public_point_matches(&bits, &scalar, &curve));
        let last = bits.len() - 1;
        bits[last] ^= 1;
        assert!(!public_point_matches(&bits, &scalar, &curve));

        let prime = Fe::from_be(curve.prime);
        let g = Pt {
            x: Fe::from_be(curve.gx),
            y: Fe::from_be(curve.gy),
            z: Fe::one(),
        };
        let doubled = dbl(&g, &prime, Fe::from_be(curve.a));
        scalar[31] = 2;
        let got = mul_base(&scalar, &curve, &prime);
        assert!(affine(&got, &prime) == affine(&doubled, &prime));
    }
}
