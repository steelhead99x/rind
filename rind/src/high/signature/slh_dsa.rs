// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SLH-DSA's public API: key pairs and public keys whose parameter set is a
//! type.

use alloc::boxed::Box;
use core::fmt;
use core::marker::PhantomData;

use super::{Buffer, Pkcs8, Spki};
use crate::error::{Error, KeyFormatError};
use crate::high::asn1;
use crate::high::{pkcs8, spki};
use crate::low;
use crate::mid::slhdsa::{
    self, Params, SlhDsaSha2_128f, SlhDsaSha2_128s, SlhDsaSha2_192f, SlhDsaSha2_192s,
    SlhDsaSha2_256f, SlhDsaSha2_256s, SlhDsaShake128f, SlhDsaShake128s, SlhDsaShake192f,
    SlhDsaShake192s, SlhDsaShake256f, SlhDsaShake256s,
};
use crate::mid::util::Array;

/// Pure SLH-DSA's message prefix with the empty context, as X.509 signs:
/// `0 || len(context)`.
const PREFIX: [u8; 2] = [0, 0];

/// An SLH-DSA parameter set, as FIPS 205 standardises them, such as
/// [`SlhDsaSha2_128s`] or [`SlhDsaShake256f`], which fixes its hash and the
/// sizes of its keys and signatures.
pub trait ParameterSet: Params {
    #[doc(hidden)]
    const ALGORITHM: Algorithm;
}

macro_rules! sets {
    ($($set:ident: $name:literal, $oid:ident;)*) => {$(
        impl ParameterSet for $set {
            const ALGORITHM: Algorithm = Algorithm {
                name: $name,
                oid: &asn1::oid::$oid,
            };
        }
    )*};
}

sets! {
    SlhDsaSha2_128s: "SLH-DSA-SHA2-128s", id_slh_dsa_sha2_128s;
    SlhDsaSha2_128f: "SLH-DSA-SHA2-128f", id_slh_dsa_sha2_128f;
    SlhDsaSha2_192s: "SLH-DSA-SHA2-192s", id_slh_dsa_sha2_192s;
    SlhDsaSha2_192f: "SLH-DSA-SHA2-192f", id_slh_dsa_sha2_192f;
    SlhDsaSha2_256s: "SLH-DSA-SHA2-256s", id_slh_dsa_sha2_256s;
    SlhDsaSha2_256f: "SLH-DSA-SHA2-256f", id_slh_dsa_sha2_256f;
    SlhDsaShake128s: "SLH-DSA-SHAKE-128s", id_slh_dsa_shake_128s;
    SlhDsaShake128f: "SLH-DSA-SHAKE-128f", id_slh_dsa_shake_128f;
    SlhDsaShake192s: "SLH-DSA-SHAKE-192s", id_slh_dsa_shake_192s;
    SlhDsaShake192f: "SLH-DSA-SHAKE-192f", id_slh_dsa_shake_192f;
    SlhDsaShake256s: "SLH-DSA-SHAKE-256s", id_slh_dsa_shake_256s;
    SlhDsaShake256f: "SLH-DSA-SHAKE-256f", id_slh_dsa_shake_256f;
}

/// An SLH-DSA parameter set's name and its OID (RFC 9909).
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct Algorithm {
    name: &'static str,
    oid: &'static asn1::ObjectId,
}

/// An SLH-DSA public key of parameter set `P`: FIPS 205's encoding,
/// `PK.seed || PK.root`.
pub struct PublicKey<P: ParameterSet>(P::PublicKey);

impl<P: ParameterSet> PublicKey<P> {
    /// Parses FIPS 205's encoding of a public key: any bytes of the
    /// parameter set's length are one.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        let mut key = P::PublicKey::zeroed();
        if bytes.len() != key.as_ref().len() {
            return Err(KeyFormatError::WrongLength.into());
        }
        key.as_mut().copy_from_slice(bytes);
        Ok(Self(key))
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, which names
    /// the parameter set's OID (RFC 9909).
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

    /// Verifies `signature` over `message`: pure SLH-DSA with the empty
    /// context, as X.509 signs.
    pub fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        slhdsa::verify::<P>(self.as_ref(), &PREFIX, message, signature)
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

// A byte array.
impl<P: ParameterSet> low::Zeroable for PublicKey<P> {}

/// An SLH-DSA private key and its public key, of parameter set `P`.
///
/// It signs pure SLH-DSA (FIPS 205) with the empty context, as X.509 uses
/// it (RFC 9909), randomized with fresh randomness as FIPS 205 recommends,
/// as [`PublicKey::verify`] verifies.
///
/// It wipes its whole value on drop.
pub struct KeyPair<P: ParameterSet> {
    pair: slhdsa::KeyPair<P>,
    public: PublicKey<P>,
}

impl<P: ParameterSet> KeyPair<P> {
    fn from_pair(pair: slhdsa::KeyPair<P>) -> Self {
        let mut public = P::PublicKey::zeroed();
        public.as_mut().copy_from_slice(pair.public_key());
        Self {
            pair,
            public: PublicKey(public),
        }
    }

    /// Generates a key pair from the system random source.
    pub fn generate() -> Result<Self, Error> {
        slhdsa::KeyPair::generate().map(Self::from_pair)
    }

    /// Loads a PKCS#8 SLH-DSA key (RFC 9909), refused if it carries a public
    /// key (v2, RFC 5958) that does not match.
    ///
    /// Its private key is FIPS 205's encoding, `SK.seed || SK.prf || PK.seed
    /// || PK.root`, and is refused unless `PK.root` is the root its seeds
    /// make, which costs as much as generating the key.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let p8 = pkcs8::Key::decode(der, &[P::ALGORITHM.oid], None)?;
        let key = Self::from_pair(slhdsa::KeyPair::from_secret_key(p8.private_key())?);
        match p8.public_key() {
            Some(public_key) if public_key != key.public.as_ref() => {
                Err(KeyFormatError::MismatchedPkcs8PublicKey.into())
            }
            _ => Ok(key),
        }
    }

    /// Encodes the private key as PKCS#8 v1 (RFC 9909).
    pub fn to_pkcs8(&self) -> Pkcs8 {
        let _entry = low::Entry::new_secret();
        let pkcs8 = Pkcs8(Buffer::encode(|output| {
            pkcs8::Key::construct(
                self.pair.secret_key().as_ref(),
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
        self.pair
            .sign(&PREFIX, message)
            .map(|signature| Signature(signature, PhantomData))
    }
}

impl<P: ParameterSet> KeyPair<P> {
    /// The parameter set's OID.
    pub(crate) const fn oid() -> &'static asn1::ObjectId {
        P::ALGORITHM.oid
    }
}

#[cfg(test)]
impl<P: ParameterSet> KeyPair<P> {
    /// The key pair the mid layer holds.
    pub(crate) fn inner(&self) -> &slhdsa::KeyPair<P> {
        &self.pair
    }
}

impl<P: ParameterSet> fmt::Debug for KeyPair<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("algorithm", &format_args!("{}", P::ALGORITHM.name))
            .finish_non_exhaustive()
    }
}

impl<P: ParameterSet> Drop for KeyPair<P> {
    // The private key's own drop wipes it, so this wipes the public key.
    fn drop(&mut self) {
        low::zeroise_value(&mut self.public);
    }
}

/// An SLH-DSA signature of parameter set `P`, FIPS 205's encoding: up to
/// 49,856 bytes, so it lives on the heap.
pub struct Signature<P: ParameterSet>(Box<[u8]>, PhantomData<P>);

impl<P: ParameterSet> Clone for Signature<P> {
    fn clone(&self) -> Self {
        Self(self.0.clone(), PhantomData)
    }
}

impl<P: ParameterSet> AsRef<[u8]> for Signature<P> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<P: ParameterSet> fmt::Debug for Signature<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}
