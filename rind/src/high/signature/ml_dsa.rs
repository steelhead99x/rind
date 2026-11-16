// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-DSA's public API: key pairs and public keys whose parameter set is a
//! type.

use core::fmt;

use super::{Buffer, Pkcs8, Spki};
use crate::error::{Error, KeyFormatError};
use crate::high::asn1::{self, Type, pkix};
use crate::high::{pkcs8, spki};
use crate::low;
use crate::mid::mldsa::{self, MlDsa44, MlDsa65, MlDsa87, Params};

/// An ML-DSA parameter set, as FIPS 204 standardises them: [`MlDsa44`],
/// [`MlDsa65`], or [`MlDsa87`], which fixes the sizes of its keys and
/// signatures.
pub trait ParameterSet: Params {
    #[doc(hidden)]
    const ALGORITHM: Algorithm;
}

impl ParameterSet for MlDsa44 {
    const ALGORITHM: Algorithm = Algorithm {
        name: "ML-DSA-44",
        oid: &asn1::oid::id_ml_dsa_44,
    };
}

impl ParameterSet for MlDsa65 {
    const ALGORITHM: Algorithm = Algorithm {
        name: "ML-DSA-65",
        oid: &asn1::oid::id_ml_dsa_65,
    };
}

impl ParameterSet for MlDsa87 {
    const ALGORITHM: Algorithm = Algorithm {
        name: "ML-DSA-87",
        oid: &asn1::oid::id_ml_dsa_87,
    };
}

/// An ML-DSA parameter set's name and its OID (RFC 9881).
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct Algorithm {
    name: &'static str,
    oid: &'static asn1::ObjectId,
}

/// An ML-DSA public key of parameter set `P`: FIPS 204's encoding, and its
/// hash `tr`, which every signature it verifies binds in.
///
/// It keeps its encoding's expansion on the heap from its second
/// verification on, so a key used once never holds it: 20 KiB for
/// ML-DSA-44, 36 KiB for ML-DSA-65, and 64 KiB for ML-DSA-87. A clone keeps
/// its own.
pub struct PublicKey<P: ParameterSet>(mldsa::PublicKey<P>);

impl<P: ParameterSet> PublicKey<P> {
    /// Parses FIPS 204's encoding of a public key: any bytes of the
    /// parameter set's length are one.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        mldsa::PublicKey::from_bytes(bytes).map(Self)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, which names
    /// the parameter set's OID (RFC 9881).
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        Self::new(spki::decode(der, &[P::ALGORITHM.oid], None)?)
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming its
    /// parameter set.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            spki::encode(self.as_ref(), P::ALGORITHM.oid, None, output)
        }))
    }

    /// Verifies `signature` over `message`: pure ML-DSA with the empty
    /// context, as TLS and X.509 sign.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        self.0.verify(&[], message, signature)
    }
}

impl<P: ParameterSet> Clone for PublicKey<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: ParameterSet> AsRef<[u8]> for PublicKey<P> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<P: ParameterSet> fmt::Debug for PublicKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", &format_args!("{}", P::ALGORITHM.name))
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// The longest ML-DSA private key, ML-DSA-87's expanded form in its
/// `OCTET STRING`.
pub(super) const MAX_PRIVATE_KEY_LEN: usize = mldsa::secret_key_len::<MlDsa87>() + 4;

/// An ML-DSA private key and its public key, of parameter set `P`.
///
/// It signs pure ML-DSA (FIPS 204) with the empty context, as TLS and X.509
/// use it, hedged with fresh randomness, as [`PublicKey::verify`] verifies.
///
/// Loading it expands its encodings once, so that no signature repeats that
/// work, and keeps the expansion on the heap: 28 KiB for ML-DSA-44, 47 KiB
/// for ML-DSA-65, and 79 KiB for ML-DSA-87.
///
/// It wipes its whole value on drop under the `wipe` feature.
pub struct KeyPair<P: ParameterSet> {
    pair: mldsa::KeyPair<P>,
    public: PublicKey<P>,
}

impl<P: ParameterSet> KeyPair<P> {
    fn from_parts((pair, public): (mldsa::KeyPair<P>, mldsa::PublicKey<P>)) -> Self {
        Self {
            pair,
            public: PublicKey(public),
        }
    }

    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Error> {
        mldsa::KeyPair::generate().map(Self::from_parts)
    }

    /// Expands a 32-byte seed, FIPS 204's `xi`, into its key pair.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        let seed = seed.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        Ok(Self::from_parts(mldsa::KeyPair::from_seed(seed)))
    }

    /// Returns the private key's 32-byte seed, which [`Self::from_seed`]
    /// loads, unless the key was loaded from its expanded form, which has
    /// none.
    pub fn to_seed(&self) -> Option<Seed> {
        self.pair.seed().map(|seed| Seed(*seed))
    }

    /// Whether the key pair has its seed, which it lacks when loaded from its
    /// expanded form.
    pub fn has_seed(&self) -> bool {
        self.pair.seed().is_some()
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
                Self::from_parts(mldsa::KeyPair::from_secret_key(key.as_octets())?)
            }
            pkix::MlDsaPrivateKey::Both(both) => {
                let key = Self::from_seed(both.seed.as_octets())?;
                let expanded = key.pair.secret_key().as_ref();
                if !low::ct::into_public(low::ct_equal(expanded, both.expandedKey.as_octets())) {
                    return Err(KeyFormatError::MismatchedMlDsaSeed.into());
                }
                key
            }
        };
        match p8.public_key() {
            Some(public_key) if public_key != key.public.as_ref() => {
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
        let private_key = match self.pair.seed() {
            Some(seed) => pkix::MlDsaPrivateKey::Seed(asn1::OctetString::new(seed)),
            None => pkix::MlDsaPrivateKey::ExpandedKey(asn1::OctetString::new(
                self.pair.secret_key().as_ref(),
            )),
        };
        let mut private_key_buf = [0u8; MAX_PRIVATE_KEY_LEN];
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
    pub fn public_key(&self) -> &PublicKey<P> {
        &self.public
    }

    /// Signs `message`, with fresh randomness from the system random source.
    pub fn sign(&self, message: &[u8]) -> Result<Signature<P>, Error> {
        self.pair.sign(&[], message).map(Signature)
    }
}

#[cfg(test)]
impl<P: ParameterSet> KeyPair<P> {
    /// The key pair the mid layer holds.
    pub(crate) fn inner(&self) -> &mldsa::KeyPair<P> {
        &self.pair
    }

    /// The parameter set's OID.
    pub(crate) fn oid() -> &'static asn1::ObjectId {
        P::ALGORITHM.oid
    }
}

impl<P: ParameterSet> fmt::Debug for KeyPair<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", &format_args!("{}", P::ALGORITHM.name))
            .finish_non_exhaustive()
    }
}

// As the mid layer's public key is.
impl<P: ParameterSet> low::Zeroable for PublicKey<P> {}

impl<P: ParameterSet> Drop for KeyPair<P> {
    // The private key's own drop wipes its expansion and its value, which a
    // wipe of this whole value would forget the expansion's place in, so
    // this wipes the public key alone, once it frees its kept expansion.
    fn drop(&mut self) {
        self.public.0.free_expansion();
        low::zeroise_value(&mut self.public);
    }
}

/// An ML-DSA signature of parameter set `P`, FIPS 204's encoding.
pub struct Signature<P: ParameterSet>(P::Signature);

impl<P: ParameterSet> Clone for Signature<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<P: ParameterSet> AsRef<[u8]> for Signature<P> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<P: ParameterSet> fmt::Debug for Signature<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// An ML-DSA private key's 32-byte seed, wiped on drop under the `wipe`
/// feature.
pub struct Seed([u8; mldsa::SEED_LEN]);

impl AsRef<[u8]> for Seed {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl fmt::Debug for Seed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Seed").finish_non_exhaustive()
    }
}

impl Drop for Seed {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}
