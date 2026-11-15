//! ML-DSA (FIPS 204), which aws-lc-rs names PQDSA, backed by rind's
//! `MlDsaKeyPair`, whose parameter set is a type where aws-lc-rs's is a
//! value.

use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use rind::signature::sign::{MlDsa44, MlDsa65, MlDsa87, MlDsaKeyPair};

use crate::digest::Digest;
use crate::encoding::{AsDer, Pkcs8V1Der, PublicKeyX509Der};
use crate::error::{KeyRejected, Unspecified, unspecified};
use crate::signature::{KeyPair, private, verification_algorithm};
use crate::wipe::Wiped;
use crate::{Hex, pkcs8};

/// An ML-DSA parameter set.
#[allow(non_camel_case_types)]
#[derive(Debug, Eq, PartialEq)]
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

    fn rind(&self) -> &'static rind::signature::VerificationAlgorithm {
        match self {
            Self::ML_DSA_44 => &rind::signature::verify::ML_DSA_44,
            Self::ML_DSA_65 => &rind::signature::verify::ML_DSA_65,
            Self::ML_DSA_87 => &rind::signature::verify::ML_DSA_87,
        }
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
    fn parse(&self, public_key: &[u8]) -> Result<rind::signature::PublicKey, KeyRejected> {
        let algorithm = self.id.rind();
        match public_key.len() == self.id.public_key_len() {
            true => rind::signature::PublicKey::new(algorithm, public_key),
            false => rind::signature::PublicKey::from_spki(algorithm, public_key),
        }
        .map_err(KeyRejected::rind)
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
        _: &Digest,
        _: &[u8],
    ) -> Result<(), Unspecified> {
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
    MlDsa44(Arc<MlDsaKeyPair<MlDsa44>>),
    MlDsa65(Arc<MlDsaKeyPair<MlDsa65>>),
    MlDsa87(Arc<MlDsaKeyPair<MlDsa87>>),
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

/// Calls rind's `MlDsaKeyPair::$method($args)` for `$id`'s parameter set,
/// returning a [`Key`].
macro_rules! new_key {
    ($id:expr, $method:ident($($arg:expr),*)) => {
        match $id {
            AlgorithmID::ML_DSA_44 => MlDsaKeyPair::$method($($arg),*).map(|k| Key::MlDsa44(Arc::new(k))),
            AlgorithmID::ML_DSA_65 => MlDsaKeyPair::$method($($arg),*).map(|k| Key::MlDsa65(Arc::new(k))),
            AlgorithmID::ML_DSA_87 => MlDsaKeyPair::$method($($arg),*).map(|k| Key::MlDsa87(Arc::new(k))),
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
        let key = new_key!(algorithm.0.id, from_pkcs8(pkcs8)).map_err(KeyRejected::rind)?;
        Ok(Self::new(algorithm, key))
    }

    /// Loads FIPS 204's expanded private key. The key pair then has no seed,
    /// so [`Self::to_pkcs8v1`] fails.
    pub fn from_raw_private_key(
        algorithm: &'static PqdsaSigningAlgorithm,
        raw_private_key: &[u8],
    ) -> Result<Self, KeyRejected> {
        let id = algorithm.0.id;
        if raw_private_key.len() != id.private_key_len() {
            return Err(KeyRejected::invalid_encoding());
        }
        // rind loads an expanded key only as PKCS#8 (RFC 9881's
        // `expandedKey`), so wrap it in one.
        let pkcs8 = expanded_pkcs8(id, raw_private_key);
        Self::from_pkcs8(algorithm, &pkcs8)
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
        let key =
            rind::signature::PublicKey::new(self.id.rind(), &self.bytes).map_err(unspecified)?;
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
