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

    /// Every parameter set, in OID order. Length and OID lookups share this.
    const ALL: [Self; 3] = [Self::ML_DSA_44, Self::ML_DSA_65, Self::ML_DSA_87];

    /// The parameter set whose expanded private key is `len` bytes.
    /// aws-lc-rs selects it from the length before checking the caller's
    /// algorithm (`parse_raw_private_key` in aws-lc-rs 1.19.0
    /// `aws-lc-rs/src/evp_pkey.rs`).
    fn from_raw_len(len: usize) -> Option<Self> {
        Self::ALL.into_iter().find(|id| id.private_key_len() == len)
    }

    /// The parameter set whose object identifier's contents are `oid`.
    fn from_oid(oid: &[u8]) -> Option<Self> {
        Self::ALL.into_iter().find(|id| id.oid().as_slice() == oid)
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
        let load = || {
            let key = new_key!(algorithm.0.id, from_pkcs8(pkcs8)).map_err(KeyRejected::rind)?;
            Ok(Self::new(algorithm, key))
        };
        // One read of the header. The OID is public and picks the refusal
        // before any other algorithm's secret is used.
        match der::pkcs8_parts(pkcs8) {
            Some(parts) => match AlgorithmID::from_oid(parts.oid) {
                Some(id) if algorithm.0.id != &id => Err(other_parameter_set(&id, pkcs8)),
                None => {
                    if parses_as_other_private_key(pkcs8, &parts) {
                        Err(KeyRejected::wrong_algorithm())
                    } else {
                        Err(KeyRejected::invalid_encoding())
                    }
                }
                Some(_) => load(),
            },
            None => load(),
        }
    }

    /// Loads FIPS 204's expanded private key. The key pair then has no seed,
    /// so [`Self::to_pkcs8v1`] fails.
    pub fn from_raw_private_key(
        algorithm: &'static PqdsaSigningAlgorithm,
        raw_private_key: &[u8],
    ) -> Result<Self, KeyRejected> {
        // aws-lc-rs picks the parameter set from the length, then refuses a
        // key of another set as `Unspecified` (`validate_pqdsa_evp_key`).
        // The length is public, so that refusal comes before the key is
        // expanded. Any other length is `InvalidEncoding`.
        let Some(id) = AlgorithmID::from_raw_len(raw_private_key.len()) else {
            return Err(KeyRejected::invalid_encoding());
        };
        if algorithm.0.id != &id {
            return Err(KeyRejected::unspecified());
        }
        // rind loads an expanded key only as PKCS#8 (RFC 9881's
        // `expandedKey`), so wrap it in one. aws-lc-rs 1.19.0
        // `parse_raw_private_key` (`aws-lc-rs/src/evp_pkey.rs`) maps every
        // failure of `EVP_PKEY_pqdsa_new_raw_private_key` at this length to
        // `InvalidEncoding`.
        let pkcs8 = expanded_pkcs8(&id, raw_private_key);
        let key = new_key!(&id, from_pkcs8(&pkcs8)).map_err(|_| KeyRejected::invalid_encoding())?;
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
///
/// The buffer is the private key, so it is wiped on drop under the `wipe`
/// feature. Heap scratch that holds a private key is wiped; a copy that is
/// only inside the call and is not the key is not.
fn expanded_pkcs8(id: &AlgorithmID, key: &[u8]) -> Wiped<Vec<u8>> {
    /// A DER header with a two-byte length, which every ML-DSA key needs.
    fn header(out: &mut Vec<u8>, tag: u8, len: usize) {
        let len = u16::try_from(len).expect("ML-DSA keys are under 64 KiB");
        out.push(tag);
        out.push(0x82);
        out.extend_from_slice(&len.to_be_bytes());
    }
    // `version` 0, then the `AlgorithmIdentifier`. The OID bytes are
    // [`AlgorithmID::oid`], the one list of them.
    let oid = id.oid();
    let prefix_len = 7 + oid.len();
    let mut der = Vec::with_capacity(prefix_len + key.len() + 12);
    header(&mut der, 0x30, prefix_len + key.len() + 8);
    der.extend_from_slice(&[0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09]);
    der.extend_from_slice(&oid);
    header(&mut der, 0x04, key.len() + 4);
    header(&mut der, 0x04, key.len());
    der.extend_from_slice(key);
    Wiped::new(der)
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

/// An ML-DSA key pair's public key, FIPS 204's encoding; wiped on drop under
/// the `wipe` feature, as the key pair is.
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
/// `pqdsa_priv_decode` (aws-lc-sys 0.47.0 `crypto/evp_extra/p_pqdsa_asn1.c`,
/// lines 198-211) rejects any seed other than 32 bytes before keygen, and
/// keygen accepts every 32-byte seed, so the parameter-set check is then
/// `Unspecified` with no expansion. An expanded key still runs the
/// consistency check: an inconsistent key is `InvalidEncoding`, and a
/// consistent one is then `Unspecified`. A byte after the document is
/// refused here; the README lists that.
///
/// That decoder does not require its private-key CBS to end after the seed
/// (lines 198-211). A 32-byte seed is therefore `Unspecified` for another
/// parameter set even when bytes follow the seed element. The named set
/// still refuses those bytes: rind's parser requires the value to end
/// (`Type::from_bytes` calls `check_end` in `rind/src/high/asn1.rs`).
fn other_parameter_set(id: &AlgorithmID, pkcs8: &[u8]) -> KeyRejected {
    if der::pkcs8_trailing(pkcs8) {
        return KeyRejected::invalid_encoding();
    }
    if let Some(parts) = der::pkcs8_parts(pkcs8) {
        if !parts.parameters.is_empty() {
            return KeyRejected::invalid_encoding();
        }
        // The first element only. Bytes after a 32-byte seed are unread,
        // as `pqdsa_priv_decode` leaves them unread.
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

/// Whether `parts` is a private key of a type aws-lc-rs parses that is not
/// ML-DSA. The OID was already read. Only that OID's shape is checked, and
/// only a shape aws-lc's `EVP_parse_private_key` accepts is `WrongAlgorithm`
/// (aws-lc-rs 1.19.0 `parse_rfc5208_private_key`, `aws-lc-rs/src/evp_pkey.rs`).
/// A curve or parameter set rind does not implement still parses in aws-lc;
/// the README lists those, and they stay `InvalidEncoding`.
fn parses_as_other_private_key(pkcs8: &[u8], parts: &der::Pkcs8Parts<'_>) -> bool {
    match parts.oid {
        // RFC 8410 Ed25519.
        [0x2b, 0x65, 0x70] => curve25519_private_key(pkcs8, parts, |document| {
            rind::ed25519::KeyPair::from_pkcs8(document).is_ok()
        }),
        // RFC 8410 X25519.
        [0x2b, 0x65, 0x6e] => curve25519_private_key(pkcs8, parts, |document| {
            rind::agreement::PrivateKey::from_pkcs8(&rind::agreement::X25519, document).is_ok()
        }),
        // RFC 5480 `id-ecPublicKey`. The curve is in the parameters.
        [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01] => ec_private_key(parts),
        // RFC 8017 `rsaEncryption`, RFC 4055 `id-RSAES-OAEP`, and X.509's
        // `id-ea-rsa`. aws-lc decodes each with the RSA private-key parser,
        // which requires NULL parameters (`p_rsa_asn1.c` `rsa_priv_decode`,
        // lines 104-127).
        [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]
        | [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x07]
        | [0x55, 0x08, 0x01, 0x01] => rsa_private_key(pkcs8, parts),
        // RFC 4055 `id-RSASSA-PSS`. Absent parameters, or an empty parameter
        // sequence, take the defaults. Explicit hash or mask parameters are
        // `InvalidEncoding` here; the README lists that.
        [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a] => rsa_pss_private_key(parts),
        // RFC 9935 ML-KEM. The seed is 64 bytes and the expanded key has the
        // parameter set's length. aws-lc accepts either encoding at that
        // length and does not check the bytes further.
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01] => ml_kem_private_key(parts, 1632),
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x02] => ml_kem_private_key(parts, 2400),
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x03] => ml_kem_private_key(parts, 3168),
        // DSA, and an `id-ecPublicKey` curve rind does not implement, are not
        // recognized. aws-lc parses those keys; the README lists the difference.
        _ => false,
    }
}

/// An RFC 8410 private key: an empty parameter list and one 32-byte seed.
///
/// aws-lc-sys 0.47.0 `ed25519_priv_decode` (`p_ed25519_asn1.c` lines 164-168;
/// X25519 is the same in `p_x25519_asn1.c` lines 157-161) requires that
/// element to end the private key. A v2 public key has to match the seed
/// (`ed25519_set_priv_raw`, lines 29-48), which is the one case that still
/// expands the seed. Bytes after the PKCS#8 document are not part of that
/// check: `EVP_parse_private_key` (`evp_asn1.c` lines 136-140) reads one
/// value and leaves the rest.
fn curve25519_private_key(
    pkcs8: &[u8],
    parts: &der::Pkcs8Parts<'_>,
    accept_v2: impl FnOnce(&[u8]) -> bool,
) -> bool {
    if !parts.parameters.is_empty() {
        return false;
    }
    let Some((0x04, seed)) = der::sole_element(parts.private_key) else {
        return false;
    };
    if seed.len() != 32 {
        return false;
    }
    if !parts.has_public_key {
        return true;
    }
    der::sequence_prefix(pkcs8).is_some_and(accept_v2)
}

/// P-256, P-384, or P-521 as SEC 1's `ECPrivateKey`, the curves rind
/// implements. `eckey_priv_decode` (`p_ec_asn1.c` lines 104-116) rejects a
/// v2 public key. secp224r1, secp256k1, and Brainpool are left unrecognized.
fn ec_private_key(parts: &der::Pkcs8Parts<'_>) -> bool {
    if parts.has_public_key {
        return false;
    }
    let Some((0x06, curve)) = der::sole_element(parts.parameters) else {
        return false;
    };
    // 1.2.840.10045.3.1.7, 1.3.132.0.34, and 1.3.132.0.35.
    let scalar_len = match curve {
        [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07] => 32,
        [0x2b, 0x81, 0x04, 0x00, 0x22] => 48,
        [0x2b, 0x81, 0x04, 0x00, 0x23] => 66,
        _ => return false,
    };
    let Some((0x30, mut rest)) = der::sole_element(parts.private_key) else {
        return false;
    };
    let Some((0x02, version, next)) = der::element(rest) else {
        return false;
    };
    if version != [1] {
        return false;
    }
    let Some((0x04, scalar, next)) = der::element(next) else {
        return false;
    };
    if scalar.len() != scalar_len || scalar.iter().all(|byte| *byte == 0) {
        return false;
    }
    rest = next;
    if rest.first() == Some(&0xa0) {
        let Some((_, _, next)) = der::element(rest) else {
            return false;
        };
        rest = next;
    }
    if rest.first() == Some(&0xa1) {
        let Some((_, _, next)) = der::element(rest) else {
            return false;
        };
        rest = next;
    }
    rest.is_empty()
}

/// A two-prime RSA private key whose modulus aws-lc will parse.
///
/// `rsa_priv_decode` rejects a v2 public key and requires NULL parameters.
/// `is_public_component_of_rsa_key_good` (`crypto/fipsmodule/rsa/rsa.c`,
/// lines 1097-1148) allows an odd modulus of at most 16384 bits and an odd
/// public exponent of 2 to 33 bits. rind itself loads 2048 to 8192 bits and
/// checks the components agree; a modulus outside that range is still
/// `WrongAlgorithm`, and its length is public, so that arm does not multiply.
fn rsa_private_key(pkcs8: &[u8], parts: &der::Pkcs8Parts<'_>) -> bool {
    if parts.has_public_key || parts.parameters != [0x05, 0x00] {
        return false;
    }
    let Some(bits) = rsa_modulus_bits(parts.private_key) else {
        return false;
    };
    if !(2..=16 * 1024).contains(&bits) {
        return false;
    }
    if (2048..=8192).contains(&bits) {
        return der::sequence_prefix(pkcs8)
            .is_some_and(|document| rind::rsa::KeyPair::from_pkcs8(document).is_ok());
    }
    true
}

/// The bit length of a PKCS#1 two-prime `RSAPrivateKey` modulus, or `None`
/// when the encoding is not that shape. `n` and `e` are public; the other
/// integers are only checked to be present and well formed.
fn rsa_modulus_bits(body: &[u8]) -> Option<usize> {
    let (tag, mut rest) = der::sole_element(body)?;
    if tag != 0x30 {
        return None;
    }
    let (tag, version, next) = der::element(rest)?;
    if tag != 0x02 || version != [0] {
        return None;
    }
    rest = next;
    let mut n_bits = None;
    for index in 0..8 {
        let (tag, integer, next) = der::element(rest)?;
        if tag != 0x02 {
            return None;
        }
        let magnitude = integer_magnitude(integer)?;
        if index == 0 {
            if magnitude.last().is_none_or(|byte| byte & 1 == 0) {
                return None;
            }
            n_bits = Some(der::bits(magnitude));
        }
        if index == 1 {
            let bits = der::bits(magnitude);
            if magnitude.last().is_none_or(|byte| byte & 1 == 0) || !(2..=33).contains(&bits) {
                return None;
            }
        }
        rest = next;
    }
    rest.is_empty().then_some(n_bits).flatten()
}

/// A positive DER INTEGER's magnitude.
fn integer_magnitude(bytes: &[u8]) -> Option<&[u8]> {
    match bytes {
        [] | [0x80..=0xff, ..] => None,
        [0, rest @ ..] => match rest {
            [0x80..=0xff, ..] => Some(rest),
            _ => None,
        },
        other => Some(other),
    }
}

/// An RSASSA-PSS private key whose parameters are absent or an empty
/// `RSASSA-PSS-params`, and whose private key is a two-prime PKCS#1 key of
/// a modulus length aws-lc parses.
fn rsa_pss_private_key(parts: &der::Pkcs8Parts<'_>) -> bool {
    let defaults = parts.parameters.is_empty() || parts.parameters == [0x30, 0x00];
    defaults
        && rsa_modulus_bits(parts.private_key).is_some_and(|bits| (2..=16 * 1024).contains(&bits))
}

/// An ML-KEM private key in RFC 9935's seed form or expanded form.
fn ml_kem_private_key(parts: &der::Pkcs8Parts<'_>, expanded_len: usize) -> bool {
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
