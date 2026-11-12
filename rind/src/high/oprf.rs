// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! [RFC 9497] OPRF and VOPRF.
//!
//! POPRF is not here: its first consumer, the public-metadata Privacy Pass
//! token, is still a draft. The DLEQ proof's verification may run in variable
//! time. Blinding, evaluation, finalization, and proof generation do not.
//! The blinded element, the evaluation, the proof, and the public key are
//! declassified once they are the bytes a party sends, and verification
//! reads those bytes.
//!
//! [RFC 9497]: https://www.rfc-editor.org/rfc/rfc9497.html

use core::fmt;

use crate::error::Error;
use crate::low::{self, Zeroable, ZeroableRef};
use crate::mid::p256::oprf as p256;
use crate::mid::p384::oprf as p384;
use crate::mid::p521::oprf as p521;
use crate::mid::ristretto_oprf as ristretto;
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::sha2::{Sha256Context, Sha384Context, Sha512Context};

const MODE_OPRF: u8 = 0x00;
const MODE_VOPRF: u8 = 0x01;
const SEED_LEN: usize = 32;
/// RFC 9497 §5.1: an input is shorter than 2^16 − 1 bytes.
const MAX_INPUT: usize = 65534;

/// One RFC 9497 ciphersuite.
///
/// The four suites are [`RISTRETTO255_SHA512`], [`P256_SHA256`],
/// [`P384_SHA384`], and [`P521_SHA512`].
pub struct Suite<const H: usize, const E: usize, const S: usize> {
    identifier: &'static str,
    group: GroupId,
}

#[derive(Clone, Copy)]
enum GroupId {
    Ristretto,
    P256,
    P384,
    P521,
}

/// OPRF(ristretto255, SHA-512).
pub static RISTRETTO255_SHA512: Suite<64, 32, 32> = Suite {
    identifier: "ristretto255-SHA512",
    group: GroupId::Ristretto,
};

/// OPRF(P-256, SHA-256).
pub static P256_SHA256: Suite<32, 33, 32> = Suite {
    identifier: "P256-SHA256",
    group: GroupId::P256,
};

/// OPRF(P-384, SHA-384). Privacy Pass's privately verifiable token
/// (RFC 9578, type `0x0001`) is this suite in VOPRF mode.
pub static P384_SHA384: Suite<48, 49, 48> = Suite {
    identifier: "P384-SHA384",
    group: GroupId::P384,
};

/// OPRF(P-521, SHA-512).
pub static P521_SHA512: Suite<64, 67, 66> = Suite {
    identifier: "P521-SHA512",
    group: GroupId::P521,
};

impl<const H: usize, const E: usize, const S: usize> fmt::Debug for Suite<H, E, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.identifier)
    }
}

impl<const H: usize, const E: usize, const S: usize> Copy for Suite<H, E, S> {}

impl<const H: usize, const E: usize, const S: usize> Clone for Suite<H, E, S> {
    fn clone(&self) -> Self {
        *self
    }
}

/// A serialized group element: a blinded input, or the server's evaluation.
#[derive(Clone, Copy)]
pub struct BlindedElement<const N: usize>([u8; N]);

impl<const N: usize> BlindedElement<N> {
    /// Parses an element for `suite`.
    ///
    /// The encoding is the suite's: ristretto255's 32 bytes, or a compressed
    /// SEC1 point for a NIST curve. The identity is refused.
    pub fn from_bytes<const H: usize, const S: usize>(
        suite: &'static Suite<H, N, S>,
        bytes: &[u8],
    ) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        // Multiply by 1: decoding refuses a bad encoding and the identity, and
        // the product is the canonical encoding, so a second encoding is refused.
        let scalar = suite.scalar_one()?;
        let canonical = suite.mul_bytes(bytes, &scalar)?;
        if canonical.as_slice() != bytes {
            return Err(crate::error::KeyFormatError::PointEncoding.into());
        }
        let mut out = [0u8; N];
        out.copy_from_slice(bytes);
        Ok(Self(out))
    }
}

impl<const N: usize> AsRef<[u8]> for BlindedElement<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const N: usize> fmt::Debug for BlindedElement<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("BlindedElement").finish_non_exhaustive()
    }
}

/// The server's public key, the group element `sk * G`.
#[derive(Clone, Copy)]
pub struct PublicKey<const N: usize>([u8; N]);

impl<const N: usize> PublicKey<N> {
    /// Parses a public key for `suite`. The identity is refused.
    pub fn from_bytes<const H: usize, const S: usize>(
        suite: &'static Suite<H, N, S>,
        bytes: &[u8],
    ) -> Result<Self, Error> {
        Ok(Self(BlindedElement::from_bytes(suite, bytes)?.0))
    }
}

impl<const N: usize> AsRef<[u8]> for PublicKey<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const N: usize> fmt::Debug for PublicKey<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").finish_non_exhaustive()
    }
}

/// A VOPRF DLEQ proof, the scalars `c` and `s` concatenated.
pub struct Proof<const S: usize> {
    c: [u8; S],
    s: [u8; S],
}

impl<const S: usize> Proof<S> {
    /// Parses `c || s`, each a scalar in `[0, n)`.
    pub fn from_bytes<const H: usize, const E: usize>(
        suite: &'static Suite<H, E, S>,
        bytes: &[u8],
    ) -> Result<Self, Error> {
        let _entry = low::Entry::new_public();
        if bytes.len() != S * 2 {
            return Err(Error::WrongLength);
        }
        let c = suite.scalar_any(&bytes[..S])?;
        let s = suite.scalar_any(&bytes[S..])?;
        Ok(Self { c, s })
    }

    /// Writes `c || s` into `out`, which is `2 * S` bytes.
    pub fn copy_to(&self, out: &mut [u8]) -> Result<(), Error> {
        if out.len() != S * 2 {
            return Err(Error::WrongLength);
        }
        out[..S].copy_from_slice(&self.c);
        out[S..].copy_from_slice(&self.s);
        Ok(())
    }
}

impl<const S: usize> fmt::Debug for Proof<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Proof").finish_non_exhaustive()
    }
}

/// The PRF output, `H` bytes for the suite's hash.
///
/// Whether this output is secret after `finalize` returns it is open: it is
/// derived from the client's input. It does not implement `PartialEq`.
pub struct Output<const N: usize>([u8; N]);

impl<const N: usize> AsRef<[u8]> for Output<N> {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl<const N: usize> fmt::Debug for Output<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Output")
    }
}

/// OPRF mode. An evaluation is not a proof, so it cannot be passed to a
/// [`voprf`] client.
// The mode's path is `oprf::oprf`, beside `oprf::voprf`.
#[allow(clippy::module_inception)]
pub mod oprf {
    use super::*;

    /// The server's OPRF key. The whole value is wiped on drop.
    #[repr(transparent)]
    pub struct ServerKey<const H: usize, const E: usize, const S: usize>(Key<MODE_OPRF, H, E, S>);

    impl<const H: usize, const E: usize, const S: usize> ServerKey<H, E, S> {
        /// A fresh key from the system RNG.
        pub fn generate(suite: &'static Suite<H, E, S>) -> Result<Self, Error> {
            let _entry = low::Entry::new_secret();
            Ok(Self(Key::generate(suite)?))
        }

        /// RFC 9497 `DeriveKeyPair`, from a 32-byte `seed` and an `info`
        /// string shorter than 65535 bytes.
        pub fn derive_key_pair(
            suite: &'static Suite<H, E, S>,
            seed: &[u8],
            info: &[u8],
        ) -> Result<Self, Error> {
            let _entry = low::Entry::new_secret();
            Ok(Self(Key::derive(suite, seed, info)?))
        }

        /// The public element `sk * G`. OPRF clients do not need it.
        pub fn public_key(&self) -> PublicKey<E> {
            PublicKey(self.0.public_key)
        }

        /// Evaluates each blinded element. `evaluated` is filled in order.
        pub fn evaluate(
            &self,
            blinded: &[BlindedElement<E>],
            evaluated: &mut [BlindedElement<E>],
        ) -> Result<(), Error> {
            let _entry = low::Entry::new_secret();
            self.0.evaluate(blinded, evaluated)
        }

        #[cfg(test)]
        pub(crate) fn scalar(&self) -> &[u8; S] {
            &self.0.scalar
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Drop for ServerKey<H, E, S> {
        fn drop(&mut self) {
            low::zeroise_value(self);
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Zeroable for ServerKey<H, E, S> {}

    impl<const H: usize, const E: usize, const S: usize> fmt::Debug for ServerKey<H, E, S> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("ServerKey")
                .field("suite", &self.0.suite.get().identifier)
                .finish_non_exhaustive()
        }
    }

    /// The client's blind. `finalize` consumes it.
    #[repr(transparent)]
    pub struct Blind<const H: usize, const E: usize, const S: usize>(Client<MODE_OPRF, H, E, S>);

    impl<const H: usize, const E: usize, const S: usize> Blind<H, E, S> {
        /// Unblinds `evaluated` and returns the PRF output.
        pub fn finalize(
            self,
            input: &[u8],
            evaluated: &BlindedElement<E>,
        ) -> Result<Output<H>, Error> {
            let _entry = low::Entry::new_secret();
            self.0.finalize_oprf(input, evaluated)
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Drop for Blind<H, E, S> {
        fn drop(&mut self) {
            low::zeroise_value(self);
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Zeroable for Blind<H, E, S> {}

    impl<const H: usize, const E: usize, const S: usize> fmt::Debug for Blind<H, E, S> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Blind")
                .field("suite", &self.0.suite.get().identifier)
                .finish_non_exhaustive()
        }
    }

    /// Blinds `input` for `suite`. Returns the element to send and the blind
    /// `finalize` consumes.
    pub fn blind<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        input: &[u8],
    ) -> Result<(BlindedElement<E>, Blind<H, E, S>), Error> {
        let _entry = low::Entry::new_secret();
        let (element, blind) = Client::<MODE_OPRF, H, E, S>::blind(suite, input, None)?;
        Ok((element, Blind(blind)))
    }

    #[cfg(test)]
    pub(crate) fn blind_with<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        input: &[u8],
        scalar: &[u8],
    ) -> Result<(BlindedElement<E>, Blind<H, E, S>), Error> {
        let _entry = low::Entry::new_secret();
        let (element, blind) = Client::<MODE_OPRF, H, E, S>::blind(suite, input, Some(scalar))?;
        Ok((element, Blind(blind)))
    }
}

/// VOPRF mode. `finalize` requires the server's proof, so an OPRF evaluation
/// cannot be finalized here.
pub mod voprf {
    use super::*;

    /// The server's VOPRF key. The whole value is wiped on drop.
    #[repr(transparent)]
    pub struct ServerKey<const H: usize, const E: usize, const S: usize>(Key<MODE_VOPRF, H, E, S>);

    impl<const H: usize, const E: usize, const S: usize> ServerKey<H, E, S> {
        /// A fresh key from the system RNG.
        pub fn generate(suite: &'static Suite<H, E, S>) -> Result<Self, Error> {
            let _entry = low::Entry::new_secret();
            Ok(Self(Key::generate(suite)?))
        }

        /// RFC 9497 `DeriveKeyPair`. The same seed in OPRF mode is a different
        /// key: the mode is part of the context string.
        pub fn derive_key_pair(
            suite: &'static Suite<H, E, S>,
            seed: &[u8],
            info: &[u8],
        ) -> Result<Self, Error> {
            let _entry = low::Entry::new_secret();
            Ok(Self(Key::derive(suite, seed, info)?))
        }

        /// The public key a client uses to check the proof.
        pub fn public_key(&self) -> PublicKey<E> {
            PublicKey(self.0.public_key)
        }

        /// Evaluates each blinded element and proves, for the whole batch,
        /// that the key was `public_key`.
        pub fn evaluate(
            &self,
            blinded: &[BlindedElement<E>],
            evaluated: &mut [BlindedElement<E>],
        ) -> Result<Proof<S>, Error> {
            let _entry = low::Entry::new_secret();
            self.0.evaluate(blinded, evaluated)?;
            self.0.prove(blinded, evaluated, None)
        }

        #[cfg(test)]
        pub(crate) fn scalar(&self) -> &[u8; S] {
            &self.0.scalar
        }

        #[cfg(test)]
        pub(crate) fn evaluate_with_nonce(
            &self,
            blinded: &[BlindedElement<E>],
            evaluated: &mut [BlindedElement<E>],
            nonce: &[u8],
        ) -> Result<Proof<S>, Error> {
            let _entry = low::Entry::new_secret();
            self.0.evaluate(blinded, evaluated)?;
            self.0.prove(blinded, evaluated, Some(nonce))
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Drop for ServerKey<H, E, S> {
        fn drop(&mut self) {
            low::zeroise_value(self);
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Zeroable for ServerKey<H, E, S> {}

    impl<const H: usize, const E: usize, const S: usize> fmt::Debug for ServerKey<H, E, S> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("ServerKey")
                .field("suite", &self.0.suite.get().identifier)
                .finish_non_exhaustive()
        }
    }

    /// The client's blind, together with the element it sent.
    #[repr(transparent)]
    pub struct Blind<const H: usize, const E: usize, const S: usize>(Client<MODE_VOPRF, H, E, S>);

    impl<const H: usize, const E: usize, const S: usize> Blind<H, E, S> {
        /// Checks `proof` against `public_key` and unblinds `evaluated`.
        pub fn finalize(
            self,
            input: &[u8],
            evaluated: &BlindedElement<E>,
            proof: &Proof<S>,
            public_key: &PublicKey<E>,
        ) -> Result<Output<H>, Error> {
            let _entry = low::Entry::new_secret();
            self.0.finalize_voprf(input, evaluated, proof, public_key)
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Drop for Blind<H, E, S> {
        fn drop(&mut self) {
            low::zeroise_value(self);
        }
    }

    impl<const H: usize, const E: usize, const S: usize> Zeroable for Blind<H, E, S> {}

    impl<const H: usize, const E: usize, const S: usize> fmt::Debug for Blind<H, E, S> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Blind")
                .field("suite", &self.0.suite.get().identifier)
                .finish_non_exhaustive()
        }
    }

    /// Blinds `input` for `suite`.
    pub fn blind<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        input: &[u8],
    ) -> Result<(BlindedElement<E>, Blind<H, E, S>), Error> {
        let _entry = low::Entry::new_secret();
        let (element, blind) = Client::<MODE_VOPRF, H, E, S>::blind(suite, input, None)?;
        Ok((element, Blind(blind)))
    }

    #[cfg(test)]
    pub(crate) fn blind_with<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        input: &[u8],
        scalar: &[u8],
    ) -> Result<(BlindedElement<E>, Blind<H, E, S>), Error> {
        let _entry = low::Entry::new_secret();
        let (element, blind) = Client::<MODE_VOPRF, H, E, S>::blind(suite, input, Some(scalar))?;
        Ok((element, Blind(blind)))
    }

    /// Checks one batch proof and unblinds each input.
    ///
    /// `blinds`, `inputs`, and `evaluated` are in the same order the server
    /// evaluated. Each blind is consumed.
    pub fn finalize_batch<const H: usize, const E: usize, const S: usize>(
        blinds: Vec<Blind<H, E, S>>,
        inputs: &[&[u8]],
        evaluated: &[BlindedElement<E>],
        proof: &Proof<S>,
        public_key: &PublicKey<E>,
    ) -> Result<Vec<Output<H>>, Error> {
        let _entry = low::Entry::new_secret();
        if blinds.is_empty() || blinds.len() != inputs.len() || blinds.len() != evaluated.len() {
            return Err(Error::WrongLength);
        }
        let suite = blinds[0].0.suite.get();
        let blinded_elems: Vec<&[u8]> = blinds
            .iter()
            .map(|blind| blind.0.blinded.as_slice())
            .collect();
        let evaluated_elems: Vec<&[u8]> = evaluated
            .iter()
            .map(|element| element.0.as_slice())
            .collect();
        verify(
            suite,
            MODE_VOPRF,
            &public_key.0,
            &blinded_elems,
            &evaluated_elems,
            proof,
        )?;
        let mut outputs = Vec::with_capacity(blinds.len());
        for ((blind, input), element) in blinds.iter().zip(inputs).zip(evaluated) {
            if input.len() > MAX_INPUT {
                return Err(Error::WrongLength);
            }
            let unblinded = suite.unblind(&blind.0.scalar, &element.0)?;
            outputs.push(suite.finish(input, &unblinded)?);
        }
        Ok(outputs)
    }
}

struct Key<const MODE: u8, const H: usize, const E: usize, const S: usize> {
    suite: ZeroableRef<Suite<H, E, S>>,
    scalar: [u8; S],
    public_key: [u8; E],
}

impl<const MODE: u8, const H: usize, const E: usize, const S: usize> Key<MODE, H, E, S> {
    fn generate(suite: &'static Suite<H, E, S>) -> Result<Self, Error> {
        let scalar = suite.random_scalar(&mut SystemRandom)?;
        let public_key = publish(suite.base_mul(&scalar)?);
        Ok(Self {
            suite: ZeroableRef::new(suite),
            scalar,
            public_key,
        })
    }

    fn derive(suite: &'static Suite<H, E, S>, seed: &[u8], info: &[u8]) -> Result<Self, Error> {
        if seed.len() != SEED_LEN || info.len() > MAX_INPUT {
            return Err(Error::WrongLength);
        }
        let mut message = Vec::with_capacity(SEED_LEN + 2 + info.len() + 1);
        message.extend_from_slice(seed);
        message.extend_from_slice(&u16::try_from(info.len()).unwrap().to_be_bytes());
        message.extend_from_slice(info);
        let dst = suite.dst(MODE, b"DeriveKeyPair");
        for counter in 0..=255u8 {
            message.push(counter);
            let scalar = suite.hash_to_scalar(dst.as_bytes(), &message)?;
            message.pop();
            if !suite.scalar_is_zero(&scalar) {
                let public_key = publish(suite.base_mul(&scalar)?);
                return Ok(Self {
                    suite: ZeroableRef::new(suite),
                    scalar,
                    public_key,
                });
            }
        }
        // RFC 9497 raises DeriveKeyPairError. The scalar is not a key.
        // `Fault` is an internal failure, which this is not.
        Err(crate::error::KeyFormatError::ScalarOutOfRange.into())
    }

    fn evaluate(
        &self,
        blinded: &[BlindedElement<E>],
        evaluated: &mut [BlindedElement<E>],
    ) -> Result<(), Error> {
        if blinded.is_empty() || blinded.len() != evaluated.len() || blinded.len() > 65536 {
            return Err(Error::WrongLength);
        }
        for (blinded, out) in blinded.iter().zip(evaluated.iter_mut()) {
            *out = BlindedElement(publish(self.suite.get().mul(&blinded.0, &self.scalar)?));
        }
        Ok(())
    }

    fn prove(
        &self,
        blinded: &[BlindedElement<E>],
        evaluated: &[BlindedElement<E>],
        nonce: Option<&[u8]>,
    ) -> Result<Proof<S>, Error> {
        let suite = self.suite.get();
        let cs: Vec<&[u8]> = blinded.iter().map(|e| e.0.as_slice()).collect();
        let ds: Vec<&[u8]> = evaluated.iter().map(|e| e.0.as_slice()).collect();
        let coefficients = suite.coefficients(MODE, &self.public_key, &cs, &ds)?;
        let coef_refs: Vec<&[u8]> = coefficients.iter().map(|c| c.as_slice()).collect();
        let m = suite.sum_scaled(&cs, &coef_refs)?;
        let z = suite.mul(&m, &self.scalar)?;
        let r = match nonce {
            Some(nonce) => suite.scalar_nonzero(nonce)?,
            None => suite.random_scalar(&mut SystemRandom)?,
        };
        let t2 = suite.base_mul(&r)?;
        let t3 = suite.mul(&m, &r)?;
        let transcript = challenge_transcript(&self.public_key, &m, &z, &t2, &t3)?;
        let c = suite.hash_to_scalar(
            suite.dst(MODE, b"HashToScalar-").as_bytes(),
            transcript.as_bytes(),
        )?;
        let s = suite.sub_scalars(&r, &suite.mul_scalars(&c, &self.scalar)?)?;
        Ok(Proof {
            c: publish(c),
            s: publish(s),
        })
    }
}

struct Client<const MODE: u8, const H: usize, const E: usize, const S: usize> {
    suite: ZeroableRef<Suite<H, E, S>>,
    scalar: [u8; S],
    /// The element sent to the server. OPRF finalization does not read it;
    /// VOPRF's proof does. Both wipe it with the blind.
    blinded: [u8; E],
}

impl<const MODE: u8, const H: usize, const E: usize, const S: usize> Client<MODE, H, E, S> {
    fn blind(
        suite: &'static Suite<H, E, S>,
        input: &[u8],
        scalar: Option<&[u8]>,
    ) -> Result<(BlindedElement<E>, Self), Error> {
        if input.len() > MAX_INPUT {
            return Err(Error::WrongLength);
        }
        let scalar = match scalar {
            Some(scalar) => suite.scalar_nonzero(scalar)?,
            None => suite.random_scalar(&mut SystemRandom)?,
        };
        // One declassified copy: the element sent to the server, and the
        // copy the proof reads. A second copy would stay secret.
        let blinded =
            publish(suite.mul_hash(suite.dst(MODE, b"HashToGroup-").as_bytes(), input, &scalar)?);
        Ok((
            BlindedElement(blinded),
            Self {
                suite: ZeroableRef::new(suite),
                scalar,
                blinded,
            },
        ))
    }

    fn finalize_oprf(
        &self,
        input: &[u8],
        evaluated: &BlindedElement<E>,
    ) -> Result<Output<H>, Error> {
        if input.len() > MAX_INPUT {
            return Err(Error::WrongLength);
        }
        let unblinded = self.suite.get().unblind(&self.scalar, &evaluated.0)?;
        self.suite.get().finish(input, &unblinded)
    }

    fn finalize_voprf(
        &self,
        input: &[u8],
        evaluated: &BlindedElement<E>,
        proof: &Proof<S>,
        public_key: &PublicKey<E>,
    ) -> Result<Output<H>, Error> {
        if input.len() > MAX_INPUT {
            return Err(Error::WrongLength);
        }
        let suite = self.suite.get();
        verify(
            suite,
            MODE,
            &public_key.0,
            &[&self.blinded],
            &[&evaluated.0],
            proof,
        )?;
        let unblinded = suite.unblind(&self.scalar, &evaluated.0)?;
        suite.finish(input, &unblinded)
    }
}

fn verify<const H: usize, const E: usize, const S: usize>(
    suite: &Suite<H, E, S>,
    mode: u8,
    public_key: &[u8; E],
    blinded: &[&[u8]],
    evaluated: &[&[u8]],
    proof: &Proof<S>,
) -> Result<(), Error> {
    let coefficients = suite.coefficients(mode, public_key, blinded, evaluated)?;
    let coef_refs: Vec<&[u8]> = coefficients.iter().map(|c| c.as_slice()).collect();
    let m = match suite.sum_scaled(blinded, &coef_refs) {
        Err(Error::KeyRejected(_)) => return Err(Error::BadSignature),
        other => other?,
    };
    let z = match suite.sum_scaled(evaluated, &coef_refs) {
        Err(Error::KeyRejected(_)) => return Err(Error::BadSignature),
        other => other?,
    };
    let g = suite.generator()?;
    let t2 = match suite.sum_scaled(&[&g, public_key], &[&proof.s, &proof.c]) {
        Err(Error::KeyRejected(_)) => return Err(Error::BadSignature),
        other => other?,
    };
    let t3 = match suite.sum_scaled(&[&m, &z], &[&proof.s, &proof.c]) {
        Err(Error::KeyRejected(_)) => return Err(Error::BadSignature),
        other => other?,
    };
    let transcript = challenge_transcript(public_key, &m, &z, &t2, &t3)?;
    let expect = suite.hash_to_scalar(
        suite.dst(mode, b"HashToScalar-").as_bytes(),
        transcript.as_bytes(),
    )?;
    match expect == proof.c {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

fn challenge_transcript(
    public_key: &[u8],
    m: &[u8],
    z: &[u8],
    t2: &[u8],
    t3: &[u8],
) -> Result<Buf<400>, Error> {
    let mut transcript = Buf::new();
    for part in [public_key, m, z, t2, t3] {
        transcript.push_len(part)?;
    }
    transcript.push(b"Challenge")?;
    Ok(transcript)
}

macro_rules! absorb {
    ($hash:expr, $input:expr, $element:expr) => {{
        $hash.update(&u16::try_from($input.len()).unwrap().to_be_bytes());
        $hash.update($input);
        $hash.update(&u16::try_from($element.len()).unwrap().to_be_bytes());
        $hash.update($element);
        $hash.update(b"Finalize");
    }};
}

impl<const H: usize, const E: usize, const S: usize> Suite<H, E, S> {
    fn context(&self, mode: u8) -> Buf<48> {
        let mut context = Buf::new();
        context.push(b"OPRFV1-").expect("context fits");
        context.push(&[mode]).expect("context fits");
        context.push(b"-").expect("context fits");
        context
            .push(self.identifier.as_bytes())
            .expect("context fits");
        context
    }

    fn dst(&self, mode: u8, prefix: &[u8]) -> Buf<80> {
        let context = self.context(mode);
        let mut dst = Buf::new();
        dst.push(prefix).expect("dst fits");
        dst.push(context.as_bytes()).expect("dst fits");
        dst
    }

    fn mul_hash(&self, dst: &[u8], msg: &[u8], scalar: &[u8; S]) -> Result<[u8; E], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::mul_hash(msg, dst, scalar)?),
            GroupId::P256 => fit(&p256::mul_hash(msg, dst, scalar)?),
            GroupId::P384 => fit(&p384::mul_hash(msg, dst, scalar)?),
            GroupId::P521 => fit(&p521::mul_hash(msg, dst, scalar)?),
        }
    }

    fn hash_to_scalar(&self, dst: &[u8], msg: &[u8]) -> Result<[u8; S], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::hash_to_scalar(msg, dst)?),
            GroupId::P256 => fit(&p256::hash_to_scalar(msg, dst)?),
            GroupId::P384 => fit(&p384::hash_to_scalar(msg, dst)?),
            GroupId::P521 => fit(&p521::hash_to_scalar(msg, dst)?),
        }
    }

    fn random_scalar(&self, rng: &mut dyn RandomSource) -> Result<[u8; S], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::random_scalar(rng)?),
            GroupId::P256 => fit(&p256::random_scalar(rng)?),
            GroupId::P384 => fit(&p384::random_scalar(rng)?),
            GroupId::P521 => fit(&p521::random_scalar(rng)?),
        }
    }

    fn scalar_nonzero(&self, bytes: &[u8]) -> Result<[u8; S], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::scalar_nonzero(bytes)?),
            GroupId::P256 => fit(&p256::scalar_nonzero(bytes)?),
            GroupId::P384 => fit(&p384::scalar_nonzero(bytes)?),
            GroupId::P521 => fit(&p521::scalar_nonzero(bytes)?),
        }
    }

    fn scalar_any(&self, bytes: &[u8]) -> Result<[u8; S], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::scalar_any(bytes)?),
            GroupId::P256 => fit(&p256::scalar_any(bytes)?),
            GroupId::P384 => fit(&p384::scalar_any(bytes)?),
            GroupId::P521 => fit(&p521::scalar_any(bytes)?),
        }
    }

    fn scalar_is_zero(&self, bytes: &[u8; S]) -> bool {
        match self.group {
            GroupId::Ristretto => ristretto::scalar_is_zero(bytes),
            GroupId::P256 => p256::scalar_is_zero(bytes),
            GroupId::P384 => p384::scalar_is_zero(bytes),
            GroupId::P521 => p521::scalar_is_zero(bytes),
        }
    }

    fn scalar_one(&self) -> Result<[u8; S], Error> {
        let mut one = [0u8; S];
        // Ristretto scalars are little-endian. The NIST scalars are big-endian.
        match self.group {
            GroupId::Ristretto => one[0] = 1,
            _ => one[S - 1] = 1,
        }
        self.scalar_nonzero(&one)
    }

    fn base_mul(&self, scalar: &[u8; S]) -> Result<[u8; E], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::base_mul(scalar)?),
            GroupId::P256 => fit(&p256::base_mul(scalar)?),
            GroupId::P384 => fit(&p384::base_mul(scalar)?),
            GroupId::P521 => fit(&p521::base_mul(scalar)?),
        }
    }

    fn mul(&self, element: &[u8; E], scalar: &[u8; S]) -> Result<[u8; E], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::mul(element, scalar)?),
            GroupId::P256 => fit(&p256::mul(element, scalar)?),
            GroupId::P384 => fit(&p384::mul(element, scalar)?),
            GroupId::P521 => fit(&p521::mul(element, scalar)?),
        }
    }

    fn mul_bytes(&self, element: &[u8], scalar: &[u8; S]) -> Result<[u8; E], Error> {
        if element.len() != E {
            return Err(Error::WrongLength);
        }
        let mut element_arr = [0u8; E];
        element_arr.copy_from_slice(element);
        self.mul(&element_arr, scalar)
    }

    fn generator(&self) -> Result<[u8; E], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::generator()),
            GroupId::P256 => fit(&p256::generator()),
            GroupId::P384 => fit(&p384::generator()),
            GroupId::P521 => fit(&p521::generator()),
        }
    }

    fn sum_scaled(&self, points: &[&[u8]], scalars: &[&[u8]]) -> Result<[u8; E], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::sum_scaled(points, scalars)?),
            GroupId::P256 => fit(&p256::sum_scaled(points, scalars)?),
            GroupId::P384 => fit(&p384::sum_scaled(points, scalars)?),
            GroupId::P521 => fit(&p521::sum_scaled(points, scalars)?),
        }
    }

    fn mul_scalars(&self, a: &[u8; S], b: &[u8; S]) -> Result<[u8; S], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::mul_scalars(a, b)?),
            GroupId::P256 => fit(&p256::mul_scalars(a, b)?),
            GroupId::P384 => fit(&p384::mul_scalars(a, b)?),
            GroupId::P521 => fit(&p521::mul_scalars(a, b)?),
        }
    }

    fn sub_scalars(&self, a: &[u8; S], b: &[u8; S]) -> Result<[u8; S], Error> {
        match self.group {
            GroupId::Ristretto => fit(&ristretto::sub_scalars(a, b)?),
            GroupId::P256 => fit(&p256::sub_scalars(a, b)?),
            GroupId::P384 => fit(&p384::sub_scalars(a, b)?),
            GroupId::P521 => fit(&p521::sub_scalars(a, b)?),
        }
    }

    fn unblind(&self, blind: &[u8; S], evaluated: &[u8; E]) -> Result<[u8; E], Error> {
        let inverse = match self.group {
            GroupId::Ristretto => fit(&ristretto::invert(blind)?)?,
            GroupId::P256 => fit(&p256::invert(blind)?)?,
            GroupId::P384 => fit(&p384::invert(blind)?)?,
            GroupId::P521 => fit(&p521::invert(blind)?)?,
        };
        self.mul(evaluated, &inverse)
    }

    fn coefficients(
        &self,
        mode: u8,
        public_key: &[u8],
        blinded: &[&[u8]],
        evaluated: &[&[u8]],
    ) -> Result<Vec<[u8; S]>, Error> {
        if blinded.len() != evaluated.len() || blinded.is_empty() || blinded.len() > 65536 {
            return Err(Error::WrongLength);
        }
        let context = self.context(mode);
        let mut seed_dst = Buf::<64>::new();
        seed_dst.push(b"Seed-")?;
        seed_dst.push(context.as_bytes())?;
        let mut seed_transcript = Buf::<160>::new();
        seed_transcript.push_len(public_key)?;
        seed_transcript.push_len(seed_dst.as_bytes())?;
        let seed = self.hash(seed_transcript.as_bytes())?;
        let dst = self.dst(mode, b"HashToScalar-");
        let mut out = Vec::with_capacity(blinded.len());
        for (i, (blinded, evaluated)) in blinded.iter().zip(evaluated).enumerate() {
            let mut message = Buf::<256>::new();
            message.push_len(&seed)?;
            let index = u16::try_from(i).map_err(|_| Error::WrongLength)?;
            message.push(&index.to_be_bytes())?;
            message.push_len(blinded)?;
            message.push_len(evaluated)?;
            message.push(b"Composite")?;
            out.push(self.hash_to_scalar(dst.as_bytes(), message.as_bytes())?);
        }
        Ok(out)
    }

    fn finish(&self, input: &[u8], element: &[u8]) -> Result<Output<H>, Error> {
        let hashed = match self.group {
            GroupId::P256 => {
                let mut hash = Sha256Context::new();
                absorb!(hash, input, element);
                fit(&hash.finish())?
            }
            GroupId::P384 => {
                let mut hash = Sha384Context::new();
                absorb!(hash, input, element);
                fit(&hash.finish())?
            }
            GroupId::Ristretto | GroupId::P521 => {
                let mut hash = Sha512Context::new();
                absorb!(hash, input, element);
                fit(&hash.finish())?
            }
        };
        Ok(Output(hashed))
    }

    fn hash(&self, message: &[u8]) -> Result<[u8; H], Error> {
        match self.group {
            GroupId::P256 => {
                let mut hash = Sha256Context::new();
                hash.update(message);
                fit(&hash.finish())
            }
            GroupId::P384 => {
                let mut hash = Sha384Context::new();
                hash.update(message);
                fit(&hash.finish())
            }
            GroupId::Ristretto | GroupId::P521 => {
                let mut hash = Sha512Context::new();
                hash.update(message);
                fit(&hash.finish())
            }
        }
    }
}

fn fit<const N: usize>(bytes: &[u8]) -> Result<[u8; N], Error> {
    bytes.try_into().map_err(|_| Error::Fault)
}

/// Bytes a party sends. Verification parses points and compares the
/// challenge in variable time, so the encoding is public from here on.
fn publish<const N: usize>(bytes: [u8; N]) -> [u8; N] {
    low::ct::into_public(bytes)
}

struct Buf<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> Buf<N> {
    fn new() -> Self {
        Self {
            bytes: [0; N],
            len: 0,
        }
    }

    fn push(&mut self, data: &[u8]) -> Result<(), Error> {
        let end = self.len.checked_add(data.len()).ok_or(Error::Fault)?;
        let dest = self.bytes.get_mut(self.len..end).ok_or(Error::Fault)?;
        dest.copy_from_slice(data);
        self.len = end;
        Ok(())
    }

    fn push_len(&mut self, data: &[u8]) -> Result<(), Error> {
        let len = u16::try_from(data.len()).map_err(|_| Error::WrongLength)?;
        self.push(&len.to_be_bytes())?;
        self.push(data)
    }

    fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hex_bytes(text: &str) -> Vec<u8> {
        hex::decode(text).unwrap()
    }

    fn split_hex(text: &str) -> Vec<Vec<u8>> {
        text.split(',').map(hex_bytes).collect()
    }

    fn vectors<const H: usize, const E: usize, const S: usize>(suite: &'static Suite<H, E, S>) {
        let files: Vec<serde_json::Value> = serde_json::from_str(include_str!(
            "../../../thirdparty/vectors/rfc9497/allVectors.json"
        ))
        .unwrap();
        let mut saw = 0;
        for file in files {
            if file["identifier"].as_str() != Some(suite.identifier) {
                continue;
            }
            let mode = file["mode"].as_u64().unwrap();
            if mode == 2 {
                continue;
            }
            saw += 1;
            let seed = hex_bytes(file["seed"].as_str().unwrap());
            let info = hex_bytes(file["keyInfo"].as_str().unwrap());
            let scalar = hex_bytes(file["skSm"].as_str().unwrap());
            let public = file["pkSm"].as_str().map(hex_bytes);
            if mode == 0 {
                let key = oprf::ServerKey::derive_key_pair(suite, &seed, &info).unwrap();
                assert_eq!(key.scalar().as_slice(), scalar.as_slice());
                if let Some(public) = &public {
                    assert_eq!(key.public_key().as_ref(), public.as_slice());
                }
                oprf_vectors(suite, &key, &file["vectors"]);
            } else {
                let key = voprf::ServerKey::derive_key_pair(suite, &seed, &info).unwrap();
                assert_eq!(key.scalar().as_slice(), scalar.as_slice());
                assert_eq!(
                    key.public_key().as_ref(),
                    public.expect("VOPRF vectors publish pkSm").as_slice()
                );
                voprf_vectors(suite, &key, &file["vectors"]);
            }
        }
        assert_eq!(saw, 2, "{}", suite.identifier);
    }

    fn oprf_vectors<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        key: &oprf::ServerKey<H, E, S>,
        vectors: &serde_json::Value,
    ) {
        for vector in vectors.as_array().unwrap() {
            let inputs = split_hex(vector["Input"].as_str().unwrap());
            let blinds = split_hex(vector["Blind"].as_str().unwrap());
            let blinded = split_hex(vector["BlindedElement"].as_str().unwrap());
            let evaluations = split_hex(vector["EvaluationElement"].as_str().unwrap());
            let outputs = split_hex(vector["Output"].as_str().unwrap());
            let mut elements = Vec::new();
            let mut states = Vec::new();
            for ((input, blind), expect) in inputs.iter().zip(&blinds).zip(&blinded) {
                let (element, state) = oprf::blind_with(suite, input, blind).unwrap();
                assert_eq!(element.as_ref(), expect.as_slice());
                elements.push(element);
                states.push(state);
            }
            let mut evaluated = elements.clone();
            key.evaluate(&elements, &mut evaluated).unwrap();
            for (got, expect) in evaluated.iter().zip(&evaluations) {
                assert_eq!(got.as_ref(), expect.as_slice());
            }
            for (((state, input), element), expect) in states
                .into_iter()
                .zip(&inputs)
                .zip(&evaluated)
                .zip(&outputs)
            {
                assert_eq!(
                    state.finalize(input, element).unwrap().as_ref(),
                    expect.as_slice()
                );
            }
        }
    }

    fn voprf_vectors<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        key: &voprf::ServerKey<H, E, S>,
        vectors: &serde_json::Value,
    ) {
        for vector in vectors.as_array().unwrap() {
            let inputs = split_hex(vector["Input"].as_str().unwrap());
            let blinds = split_hex(vector["Blind"].as_str().unwrap());
            let blinded = split_hex(vector["BlindedElement"].as_str().unwrap());
            let evaluations = split_hex(vector["EvaluationElement"].as_str().unwrap());
            let outputs = split_hex(vector["Output"].as_str().unwrap());
            let nonce = hex_bytes(vector["Proof"]["r"].as_str().unwrap());
            let proof_bytes = hex_bytes(vector["Proof"]["proof"].as_str().unwrap());
            let mut elements = Vec::new();
            let mut states = Vec::new();
            for ((input, blind), expect) in inputs.iter().zip(&blinds).zip(&blinded) {
                let (element, state) = voprf::blind_with(suite, input, blind).unwrap();
                assert_eq!(element.as_ref(), expect.as_slice());
                elements.push(element);
                states.push(state);
            }
            let mut evaluated = elements.clone();
            let proof = key
                .evaluate_with_nonce(&elements, &mut evaluated, &nonce)
                .unwrap();
            let mut got_proof = vec![0u8; S * 2];
            proof.copy_to(&mut got_proof).unwrap();
            assert_eq!(got_proof, proof_bytes);
            for (got, expect) in evaluated.iter().zip(&evaluations) {
                assert_eq!(got.as_ref(), expect.as_slice());
            }
            let input_refs: Vec<&[u8]> = inputs.iter().map(Vec::as_slice).collect();
            let got =
                voprf::finalize_batch(states, &input_refs, &evaluated, &proof, &key.public_key())
                    .unwrap();
            for (got, expect) in got.iter().zip(&outputs) {
                assert_eq!(got.as_ref(), expect.as_slice());
            }
        }
    }

    #[test]
    fn rfc9497_ristretto255() {
        vectors(&RISTRETTO255_SHA512);
    }

    #[test]
    fn rfc9497_p256() {
        vectors(&P256_SHA256);
    }

    #[test]
    fn rfc9497_p384() {
        vectors(&P384_SHA384);
    }

    #[test]
    fn rfc9497_p521() {
        vectors(&P521_SHA512);
    }

    fn agree_with_voprf<CS, const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
        blind: &[u8],
    ) where
        CS: ::voprf::CipherSuite<Group = CS> + ::voprf::Group,
    {
        let seed = [0x42u8; 32];
        let info = b"differential";
        let inputs: [&[u8]; 3] = [b"\x00", b"hello", &[0x5a; 17]];
        // Proof nonce 9, in the suite's scalar encoding. That is also the
        // byte string `voprf` reads for one scalar: ristretto's canonical
        // little-endian bytes, or a NIST scalar's big-endian field bytes.
        let mut nonce = [0u8; S];
        if E == 32 {
            nonce[0] = 9;
        } else {
            nonce[S - 1] = 9;
        }

        let our = oprf::ServerKey::derive_key_pair(suite, &seed, info).unwrap();
        let their = ::voprf::OprfServer::<CS>::new_from_seed(&seed, info).unwrap();
        assert_eq!(our.scalar().as_slice(), their.serialize().as_slice());

        let our_v = voprf::ServerKey::derive_key_pair(suite, &seed, info).unwrap();
        let their_v = ::voprf::VoprfServer::<CS>::new_from_seed(&seed, info).unwrap();
        let theirs = their_v.serialize();
        assert_eq!(our_v.scalar().as_slice(), &theirs[..S]);
        assert_eq!(our_v.public_key().as_ref(), &theirs[S..]);

        let scalar = CS::deserialize_scalar(blind).unwrap();
        for input in inputs {
            let (ours, state) = oprf::blind_with(suite, input, blind).unwrap();
            let theirs =
                ::voprf::OprfClient::<CS>::deterministic_blind_unchecked(input, scalar).unwrap();
            assert_eq!(ours.as_ref(), theirs.message.serialize().as_slice());
            let mut evaluated = [ours];
            our.evaluate(core::slice::from_ref(&ours), &mut evaluated)
                .unwrap();
            let their_eval = their.blind_evaluate(&theirs.message);
            assert_eq!(evaluated[0].as_ref(), their_eval.serialize().as_slice());
            let our_out = state.finalize(input, &evaluated[0]).unwrap();
            let their_out = theirs.state.finalize(input, &their_eval).unwrap();
            assert_eq!(our_out.as_ref(), their_out.as_slice());

            let (ours, state) = voprf::blind_with(suite, input, blind).unwrap();
            let theirs =
                ::voprf::VoprfClient::<CS>::deterministic_blind_unchecked(input, scalar).unwrap();
            assert_eq!(ours.as_ref(), theirs.message.serialize().as_slice());
            let mut evaluated = [ours];
            let proof = our_v
                .evaluate_with_nonce(core::slice::from_ref(&ours), &mut evaluated, &nonce)
                .unwrap();
            let mut proof_bytes = vec![0u8; S * 2];
            proof.copy_to(&mut proof_bytes).unwrap();
            let their_eval = their_v.blind_evaluate(&mut NonceRng::new(&nonce), &theirs.message);
            assert_eq!(
                evaluated[0].as_ref(),
                their_eval.message.serialize().as_slice()
            );
            assert_eq!(
                proof_bytes.as_slice(),
                their_eval.proof.serialize().as_slice()
            );
            let our_out = state
                .finalize(input, &evaluated[0], &proof, &our_v.public_key())
                .unwrap();
            let their_out = theirs
                .state
                .finalize(
                    input,
                    &their_eval.message,
                    &their_eval.proof,
                    their_v.get_public_key(),
                )
                .unwrap();
            assert_eq!(our_out.as_ref(), their_out.as_slice());
        }

        let mut blinded = Vec::new();
        let mut states = Vec::new();
        let mut their_clients = Vec::new();
        let mut their_messages = Vec::new();
        for input in inputs {
            let (element, state) = voprf::blind_with(suite, input, blind).unwrap();
            let theirs =
                ::voprf::VoprfClient::<CS>::deterministic_blind_unchecked(input, scalar).unwrap();
            assert_eq!(element.as_ref(), theirs.message.serialize().as_slice());
            blinded.push(element);
            states.push(state);
            their_clients.push(theirs.state);
            their_messages.push(theirs.message);
        }
        let mut evaluated = blinded.clone();
        let proof = our_v
            .evaluate_with_nonce(&blinded, &mut evaluated, &nonce)
            .unwrap();
        let mut proof_bytes = vec![0u8; S * 2];
        proof.copy_to(&mut proof_bytes).unwrap();
        let their_batch = their_v
            .batch_blind_evaluate(&mut NonceRng::new(&nonce), &their_messages)
            .unwrap();
        assert_eq!(
            proof_bytes.as_slice(),
            their_batch.proof.serialize().as_slice()
        );
        for (ours, theirs) in evaluated.iter().zip(&their_batch.messages) {
            assert_eq!(ours.as_ref(), theirs.serialize().as_slice());
        }
        let our_outputs =
            voprf::finalize_batch(states, &inputs, &evaluated, &proof, &our_v.public_key())
                .unwrap();
        let their_outputs = ::voprf::VoprfClient::batch_finalize(
            &inputs,
            &their_clients,
            &their_batch.messages,
            &their_batch.proof,
            their_v.get_public_key(),
        )
        .unwrap();
        for (ours, theirs) in our_outputs.iter().zip(their_outputs) {
            assert_eq!(ours.as_ref(), theirs.unwrap().as_slice());
        }
    }

    /// Yields one scalar, the bytes `voprf` reads for the proof nonce.
    struct NonceRng<'a> {
        bytes: &'a [u8],
        used: bool,
    }

    impl<'a> NonceRng<'a> {
        fn new(bytes: &'a [u8]) -> Self {
            Self { bytes, used: false }
        }
    }

    impl rand::TryRng for NonceRng<'_> {
        type Error = core::convert::Infallible;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            let mut bytes = [0u8; 4];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u32::from_le_bytes(bytes))
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            let mut bytes = [0u8; 8];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u64::from_le_bytes(bytes))
        }

        fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
            assert!(!self.used, "the proof nonce was read twice");
            assert_eq!(dest.len(), self.bytes.len());
            dest.copy_from_slice(self.bytes);
            self.used = true;
            Ok(())
        }
    }

    impl rand::TryCryptoRng for NonceRng<'_> {}

    #[test]
    fn matches_voprf() {
        let mut blind = [0u8; 32];
        blind[0] = 7;
        agree_with_voprf::<::voprf::Ristretto255, 64, 32, 32>(&RISTRETTO255_SHA512, &blind);
        blind = [0u8; 32];
        blind[31] = 7;
        agree_with_voprf::<::p256::NistP256, 32, 33, 32>(&P256_SHA256, &blind);
        let mut blind = [0u8; 48];
        blind[47] = 7;
        agree_with_voprf::<::p384::NistP384, 48, 49, 48>(&P384_SHA384, &blind);
        let mut blind = [0u8; 66];
        blind[65] = 7;
        agree_with_voprf::<::p521::NistP521, 64, 67, 66>(&P521_SHA512, &blind);
    }

    fn stays_secret_one<const H: usize, const E: usize, const S: usize>(
        suite: &'static Suite<H, E, S>,
    ) {
        let seed = low::ct::into_secret([0x5au8; 32]);
        let input = low::ct::into_secret(*b"client input!!");
        let second = low::ct::into_secret(*b"second input!!!");

        let key = oprf::ServerKey::generate(suite).unwrap();
        let (blinded, blind) = oprf::blind(suite, &input).unwrap();
        let mut evaluated = [blinded];
        key.evaluate(core::slice::from_ref(&blinded), &mut evaluated)
            .unwrap();
        let output = blind.finalize(&input, &evaluated[0]).unwrap();
        assert_eq!(low::ct::into_public(output).as_ref().len(), H);

        let key = voprf::ServerKey::derive_key_pair(suite, &seed, b"info").unwrap();
        let (blinded, blind) = voprf::blind(suite, &input).unwrap();
        let mut evaluated = [blinded];
        let proof = key
            .evaluate(core::slice::from_ref(&blinded), &mut evaluated)
            .unwrap();
        let output = blind
            .finalize(&input, &evaluated[0], &proof, &key.public_key())
            .unwrap();
        assert_eq!(low::ct::into_public(output).as_ref().len(), H);

        let key = voprf::ServerKey::generate(suite).unwrap();
        let (first, first_blind) = voprf::blind(suite, &input).unwrap();
        let (second_element, second_blind) = voprf::blind(suite, &second).unwrap();
        let blinded = [first, second_element];
        let mut evaluated = blinded;
        let proof = key.evaluate(&blinded, &mut evaluated).unwrap();
        let outputs = voprf::finalize_batch(
            vec![first_blind, second_blind],
            &[&input[..], &second[..]],
            &evaluated,
            &proof,
            &key.public_key(),
        )
        .unwrap();
        assert_eq!(outputs.len(), 2);
        for output in outputs {
            assert_eq!(low::ct::into_public(output).as_ref().len(), H);
        }
    }

    /// Marks the seed and the inputs. A generated scalar is marked where it
    /// is drawn. The blinded element, the evaluation, the proof, and the
    /// public key are declassified where they are published, and verification
    /// reads those bytes. Covers `generate` and a batch of two.
    /// `admin/ctgrind` is what checks it.
    #[test]
    fn stays_secret() {
        stays_secret_one(&RISTRETTO255_SHA512);
        stays_secret_one(&P256_SHA256);
        stays_secret_one(&P384_SHA384);
        stays_secret_one(&P521_SHA512);
    }

    #[test]
    fn bad_proof_and_bad_element_are_errors() {
        let suite = &P256_SHA256;
        let key = voprf::ServerKey::generate(suite).unwrap();
        let (blinded, blind) = voprf::blind(suite, b"x").unwrap();
        let mut evaluated = [blinded];
        key.evaluate(core::slice::from_ref(&blinded), &mut evaluated)
            .unwrap();
        // Scalars 1 and 1 are in range, and they are not this evaluation's proof.
        let mut bad_bytes = [0u8; 64];
        bad_bytes[31] = 1;
        bad_bytes[63] = 1;
        let bad = Proof::from_bytes(suite, &bad_bytes).unwrap();
        assert_eq!(
            blind
                .finalize(b"x", &evaluated[0], &bad, &key.public_key())
                .unwrap_err(),
            Error::BadSignature
        );
        assert!(BlindedElement::<33>::from_bytes(suite, &[0; 33]).is_err());
        assert!(BlindedElement::<33>::from_bytes(suite, &[4; 33]).is_err());
        assert!(voprf::blind(suite, &vec![0u8; 65535]).is_err());
        let mut none = [];
        assert_eq!(
            key.evaluate(&[], &mut none).unwrap_err(),
            Error::WrongLength
        );
    }
}
