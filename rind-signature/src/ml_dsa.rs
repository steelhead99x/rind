//! ML-DSA (FIPS 204) as `signature`'s `Signer` and `Verifier`, with `ml_dsa`'s
//! type names, parameter-set markers, and `Signature<P>`.
//!
//! The key is seed-based, as `ml_dsa::SigningKey` is. rind signs hedged, as
//! FIPS 204 recommends and with the empty context, where `ml_dsa`'s `Signer`
//! signs deterministically; a signature differs from RustCrypto's for the
//! same key and message, and verifies under it.

use core::fmt;

use ::ml_dsa::common::rand_core::TryCryptoRng;
use ::ml_dsa::common::typenum::U32;
pub use ::ml_dsa::common::{self, Generate, KeyExport, KeyInit, KeySizeUser};
pub use ::ml_dsa::{
    B32, EncodedSignature, EncodedVerifyingKey, MlDsa44, MlDsa65, MlDsa87, MlDsaParams, Seed,
    Signature,
};
pub use ::signature::{self, Error, Keypair, SignatureEncoding, Signer, Verifier};
use ::signature::{KeypairRef, MultipartSigner, MultipartVerifier};

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
#[repr(transparent)]
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
    /// rind's public key as this wrapper, borrowed rather than copied, so a
    /// signing key's public key is the one inside rind's key pair, which that
    /// pair wipes on drop.
    fn from_rind(key: &rind::ml_dsa::PublicKey<P::Rind>) -> &Self {
        // SAFETY: `VerifyingKey` is `repr(transparent)` over rind's public key,
        // so the two share a layout and the borrow's lifetime carries over.
        unsafe { &*(key as *const rind::ml_dsa::PublicKey<P::Rind>).cast::<Self>() }
    }

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
            .verify(b"", msg, encoded.as_slice())
            .map_err(|_| Error::new())
    }
}

impl<P: Params> MultipartVerifier<Signature<P>> for VerifyingKey<P> {
    fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature<P>) -> Result<(), Error> {
        self.verify(&msg.concat(), signature)
    }
}

/// A signing key: rind's key pair, which wipes its whole value, public key
/// included, on drop. The wrapper is only that pair: it holds no other copy of
/// the seed or the public key.
#[repr(transparent)]
pub struct SigningKey<P: Params> {
    pair: rind::ml_dsa::KeyPair<P::Rind>,
}

impl<P: Params> SigningKey<P> {
    /// The key a 32-byte seed makes.
    pub fn from_seed(seed: &Seed) -> Self {
        let pair = rind::ml_dsa::KeyPair::<P::Rind>::from_seed(seed.as_slice())
            .expect("a 32-byte seed is a key");
        Self { pair }
    }

    /// The 32-byte seed, which rind holds for every key made here.
    pub fn to_seed(&self) -> Seed {
        let seed = self.pair.to_seed().expect("made from a seed");
        Seed::try_from(seed.as_ref()).expect("a 32-byte seed")
    }

    /// The public key.
    pub fn verifying_key(&self) -> VerifyingKey<P> {
        self.verifying().clone()
    }

    fn verifying(&self) -> &VerifyingKey<P> {
        VerifyingKey::from_rind(self.pair.public_key())
    }
}

impl<P: Params> KeySizeUser for SigningKey<P> {
    type KeySize = U32;
}

impl<P: Params> KeyInit for SigningKey<P> {
    fn new(seed: &Seed) -> Self {
        Self::from_seed(seed)
    }
}

impl<P: Params> KeyExport for SigningKey<P> {
    fn to_bytes(&self) -> Seed {
        self.to_seed()
    }
}

impl<P: Params> Generate for SigningKey<P> {
    /// FIPS 204's `ML-DSA.KeyGen`: a key from a seed of 32 bytes of `rng`, a
    /// stack temporary left unwiped, as rind leaves its own; rind's key pair
    /// wipes its copy.
    fn try_generate_from_rng<R: TryCryptoRng + ?Sized>(rng: &mut R) -> Result<Self, R::Error> {
        let mut seed = Seed::default();
        rng.try_fill_bytes(&mut seed)?;
        Ok(Self::from_seed(&seed))
    }
}

impl<P: Params> fmt::Debug for SigningKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SigningKey").finish_non_exhaustive()
    }
}

impl<P: Params> AsRef<VerifyingKey<P>> for SigningKey<P> {
    fn as_ref(&self) -> &VerifyingKey<P> {
        self.verifying()
    }
}

impl<P: Params> KeypairRef for SigningKey<P> {
    type VerifyingKey = VerifyingKey<P>;
}

impl<P: Params> Signer<Signature<P>> for SigningKey<P> {
    fn try_sign(&self, msg: &[u8]) -> Result<Signature<P>, Error> {
        let signature = self.pair.sign(b"", msg).map_err(|_| Error::new())?;
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
        self.verifying().verify(msg, signature)
    }
}
