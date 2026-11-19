//! ML-DSA (FIPS 204) as `signature`'s `Signer` and `Verifier`, with `ml_dsa`'s
//! type names, parameter-set markers, and `Signature<P>`.
//!
//! The key is seed-based, as `ml_dsa::SigningKey` is. rind signs hedged, as
//! FIPS 204 recommends and with the empty context, where `ml_dsa`'s `Signer`
//! signs deterministically; a signature differs from RustCrypto's for the
//! same key and message, and verifies under it.

use core::fmt;

use ::ml_dsa::{EncodedSignature, EncodedVerifyingKey, MlDsaParams};
pub use ::ml_dsa::{MlDsa44, MlDsa65, MlDsa87, Seed, Signature};
use ::signature::{Error, KeypairRef, MultipartSigner, MultipartVerifier, Signer, Verifier};

mod sealed {
    pub trait Sealed {}
}

/// An ML-DSA parameter set both libraries have: [`MlDsa44`], [`MlDsa65`], and
/// [`MlDsa87`].
pub trait Params: sealed::Sealed + MlDsaParams {
    #[doc(hidden)]
    type Rind: rind::ml_dsa::ParameterSet;
}

macro_rules! params {
    ($($set:ident),*) => {$(
        impl sealed::Sealed for $set {}
        impl Params for $set {
            type Rind = rind::ml_dsa::$set;
        }
    )*};
}

params!(MlDsa44, MlDsa65, MlDsa87);

/// A public key.
pub struct VerifyingKey<P: Params> {
    key: rind::ml_dsa::PublicKey<P::Rind>,
}

impl<P: Params> Clone for VerifyingKey<P> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
        }
    }
}

impl<P: Params> VerifyingKey<P> {
    /// The key's encoding.
    pub fn encode(&self) -> EncodedVerifyingKey<P> {
        EncodedVerifyingKey::<P>::try_from(self.key.as_ref())
            .expect("an ML-DSA public key is its parameter set's length")
    }

    /// A key from its encoding, which every array of the right length is.
    pub fn decode(enc: &EncodedVerifyingKey<P>) -> Self {
        let key = rind::ml_dsa::PublicKey::new(enc.as_slice())
            .expect("an ML-DSA public key is any array of the right length");
        Self { key }
    }
}

impl<P: Params> PartialEq for VerifyingKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.key.as_ref() == other.key.as_ref()
    }
}

impl<P: Params> Eq for VerifyingKey<P> {}

impl<P: Params> fmt::Debug for VerifyingKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("VerifyingKey { .. }")
    }
}

impl<P: Params> Verifier<Signature<P>> for VerifyingKey<P> {
    fn verify(&self, msg: &[u8], signature: &Signature<P>) -> Result<(), Error> {
        let encoded = signature.encode();
        self.key
            .verify(msg, encoded.as_slice())
            .map_err(|_| Error::new())
    }
}

impl<P: Params> MultipartVerifier<Signature<P>> for VerifyingKey<P> {
    fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature<P>) -> Result<(), Error> {
        self.verify(&msg.concat(), signature)
    }
}

/// A signing key: rind's key pair, which wipes itself on drop. The wrapper
/// holds no other copy of the seed.
pub struct SigningKey<P: Params> {
    pair: rind::ml_dsa::KeyPair<P::Rind>,
    verifying: VerifyingKey<P>,
}

impl<P: Params> SigningKey<P> {
    /// The key a 32-byte seed makes.
    pub fn from_seed(seed: &Seed) -> Self {
        let pair = rind::ml_dsa::KeyPair::<P::Rind>::from_seed(seed.as_slice())
            .expect("a 32-byte seed is a key");
        let verifying = VerifyingKey {
            key: pair.public_key().clone(),
        };
        Self { pair, verifying }
    }

    /// The public key.
    pub fn verifying_key(&self) -> VerifyingKey<P> {
        self.verifying.clone()
    }
}

impl<P: Params> fmt::Debug for SigningKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl<P: Params> AsRef<VerifyingKey<P>> for SigningKey<P> {
    fn as_ref(&self) -> &VerifyingKey<P> {
        &self.verifying
    }
}

impl<P: Params> KeypairRef for SigningKey<P> {
    type VerifyingKey = VerifyingKey<P>;
}

impl<P: Params> Signer<Signature<P>> for SigningKey<P> {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature<P>, Error> {
        let signature = self.pair.sign(msg).map_err(|_| Error::new())?;
        let encoded =
            EncodedSignature::<P>::try_from(signature.as_ref()).map_err(|_| Error::new())?;
        Signature::decode(&encoded).ok_or_else(Error::new)
    }
}

impl<P: Params> MultipartSigner<Signature<P>> for SigningKey<P> {
    fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature<P>, Error> {
        self.try_sign(&msg.concat())
    }
}

impl<P: Params> Verifier<Signature<P>> for SigningKey<P> {
    fn verify(&self, msg: &[u8], signature: &Signature<P>) -> Result<(), Error> {
        self.verifying.verify(msg, signature)
    }
}
