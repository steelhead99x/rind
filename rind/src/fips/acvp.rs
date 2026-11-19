// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The deterministic forms of the module's randomized services, which ACVP
//! drives with randomness of its own: the DRBG from given entropy, ML-KEM
//! from given seeds and messages, and ML-DSA from given seeds and `rnd`.
//!
//! FIPS 203 and 204 allow these only for testing, so only the module's ACVP
//! build exports them, to `rind-acvp`; each is the code the module's own
//! services run, with the randomness passed in.

use crate::Error;
use crate::error::KeyFormatError;
use crate::high::hash::Sha512;
use crate::high::hmac_drbg::HmacDrbg;
use crate::high::signature::ml_dsa::ParameterSet;
use crate::kem::Algorithm;
use crate::low::Entry;
use crate::mid::mldsa::{self, Array as _, KeyPair};
use crate::mid::mlkem::{Array, Ciphertext, DecapKey, EncapKey, Message};
use crate::mid::sha3::Sha3_256Context;

/// One prediction-resistant generate's inputs: the entropy it reseeds with,
/// and the additional input it reseeds with.
pub struct Generate<'a> {
    /// The reseed's entropy input.
    pub entropy: &'a [u8],
    /// The reseed's additional input; the generate itself takes none.
    pub additional_input: &'a [u8],
}

/// ACVP's prediction-resistance test of HMAC_DRBG over SHA-512, the module's
/// DRBG: an instantiation, then two generates.
pub struct Drbg<'a> {
    /// The instantiation's entropy input.
    pub entropy: &'a [u8],
    /// The instantiation's nonce.
    pub nonce: &'a [u8],
    /// The instantiation's personalization string.
    pub personalization: &'a [u8],
    /// The two generates.
    pub generates: [Generate<'a>; 2],
}

impl Drbg<'_> {
    /// Runs the test, writing the second generate's output to `out`.
    ///
    /// A request with prediction resistance reseeds with its additional
    /// input, then generates with none (SP 800-90A section 9.3.1, step 7),
    /// as the module's every draw does.
    pub fn run(&self, out: &mut [u8]) {
        let _entry = Entry::new_secret();
        let mut drbg = HmacDrbg::<Sha512>::new(self.entropy, self.nonce, self.personalization);
        for generate in &self.generates {
            drbg.reseed(generate.entropy, generate.additional_input);
            drbg.generate(out, b"");
        }
    }
}

/// FIPS 203's `ML-KEM.KeyGen_internal` of parameter set `P`, such as
/// [`crate::kem::MlKem768`], from seeds `d` and `z`: the encapsulation key
/// and the expanded decapsulation key.
pub fn ml_kem_key_gen<P: Algorithm>(
    d: &[u8; 32],
    z: &[u8; 32],
) -> (P::EncapKeyBytes, P::DecapKeyBytes) {
    let _entry = Entry::new_secret();
    let mut seed = [0u8; 64];
    seed[..32].copy_from_slice(d);
    seed[32..].copy_from_slice(z);
    let key = DecapKey::<P>::keygen_internal(&seed);
    crate::low::zeroise(&mut seed);
    (key.encapsulation_key().as_bytes().clone(), key.as_bytes())
}

/// FIPS 203's `ML-KEM.Encaps_internal` of message `m` to encapsulation key
/// `ek` of parameter set `P`, after its input checks: the ciphertext and the
/// shared secret.
pub fn ml_kem_encap<P: Algorithm>(
    ek: &[u8],
    m: &[u8; 32],
) -> Result<(P::CiphertextBytes, [u8; 32]), Error> {
    let ek = encapsulation_key::<P>(ek)?;
    let _entry = Entry::new_secret();
    let (secret, ciphertext) = ek.encaps_internal(Message(*m));
    let ciphertext = P::CiphertextBytes::from_slice(ciphertext.as_ref()).unwrap();
    Ok((ciphertext, *secret.as_ref()))
}

/// FIPS 203's `ML-KEM.Decaps_internal` of `ciphertext` with expanded
/// decapsulation key `dk` of parameter set `P`, after their input checks:
/// the shared secret, or the implicit rejection's.
pub fn ml_kem_decap<P: Algorithm>(dk: &[u8], ciphertext: &[u8]) -> Result<[u8; 32], Error> {
    let key = decapsulation_key::<P>(dk)?;
    let ciphertext = Ciphertext::<P>::from_slice(ciphertext).ok_or(Error::WrongLength)?;
    Ok(*key.decaps(&ciphertext).as_ref())
}

/// FIPS 203's encapsulation input check of an encapsulation key of parameter
/// set `P`: its length and its modulus check.
pub fn ml_kem_check_encapsulation_key<P: Algorithm>(ek: &[u8]) -> Result<(), Error> {
    encapsulation_key::<P>(ek).map(drop)
}

/// FIPS 203's decapsulation input check of an expanded decapsulation key of
/// parameter set `P`: its length and its hash check.
///
/// The check is the hash's alone: an embedded encapsulation key that fails
/// its own modulus check still passes, as section 7.3 has it.
pub fn ml_kem_check_decapsulation_key<P: Algorithm>(dk: &[u8]) -> Result<(), Error> {
    let _entry = Entry::new_public();
    let dk =
        P::DecapKeyBytes::from_slice(dk).ok_or_else(|| Error::from(KeyFormatError::WrongLength))?;
    let (ek, h) = dk.as_ref()[P::K * 384..P::K * 768 + 64].split_at(P::K * 384 + 32);
    let mut hash = Sha3_256Context::new();
    hash.update(ek);
    if hash.finish() != *h {
        return Err(KeyFormatError::MismatchedPublicKey.into());
    }
    Ok(())
}

fn encapsulation_key<P: Algorithm>(ek: &[u8]) -> Result<EncapKey<P>, Error> {
    let ek =
        P::EncapKeyBytes::from_slice(ek).ok_or_else(|| Error::from(KeyFormatError::WrongLength))?;
    EncapKey::from_bytes(&ek)
}

fn decapsulation_key<P: Algorithm>(dk: &[u8]) -> Result<DecapKey<P>, Error> {
    let dk =
        P::DecapKeyBytes::from_slice(dk).ok_or_else(|| Error::from(KeyFormatError::WrongLength))?;
    DecapKey::from_bytes(&dk).ok_or_else(|| KeyFormatError::MismatchedPublicKey.into())
}

/// What an ML-DSA signature is over, by the interface ACVP tests.
#[derive(Clone, Copy)]
pub enum MlDsaMessage<'a> {
    /// FIPS 204's external interface, pure ML-DSA: a message under a
    /// context of at most 255 bytes, as the module's services sign with an
    /// empty one.
    External {
        /// The context string.
        context: &'a [u8],
        /// The message.
        message: &'a [u8],
    },
    /// The internal interface's `M'`, taken as is.
    Internal(&'a [u8]),
    /// The message representative `mu`, computed elsewhere.
    Mu(&'a [u8]),
}

impl MlDsaMessage<'_> {
    /// `mu` for a public key whose hash is `tr`.
    fn mu(self, tr: &[u8; mldsa::TR_LEN]) -> Result<[u8; mldsa::MU_LEN], Error> {
        match self {
            Self::External { context, message } => mldsa::mu(tr, context, message),
            Self::Internal(message) => Ok(mldsa::mu_internal(tr, message)),
            Self::Mu(mu) => mu.try_into().map_err(|_| Error::WrongLength),
        }
    }
}

/// FIPS 204's `ML-DSA.KeyGen_internal` from `seed`: the public key and the
/// expanded private key.
pub fn ml_dsa_key_gen<P: ParameterSet>(seed: &[u8; 32]) -> (P::PublicKey, P::SecretKey) {
    let (key, public_key) = KeyPair::<P>::from_seed(seed);
    let secret_key = crate::low::ct::into_public(key.secret_key().clone());
    let mut pk = P::PublicKey::zeroed();
    pk.as_mut().copy_from_slice(public_key.as_ref());
    (pk, secret_key)
}

/// FIPS 204's `ML-DSA.Sign_internal` with expanded private key `sk` over
/// `message`, with randomness `rnd`, all zeros for the deterministic variant.
pub fn ml_dsa_sign<P: ParameterSet>(
    sk: &[u8],
    message: MlDsaMessage<'_>,
    rnd: &[u8; 32],
) -> Result<P::Signature, Error> {
    let _entry = Entry::new_secret();
    let (key, _) = KeyPair::<P>::from_secret_key(sk)?;
    let mu = message.mu(key.tr())?;
    key.sign_internal(&mu, rnd)
}

/// FIPS 204's `ML-DSA.Verify_internal` of `signature` over `message` under
/// public key `pk`.
pub fn ml_dsa_verify<P: ParameterSet>(
    pk: &[u8],
    message: MlDsaMessage<'_>,
    signature: &[u8],
) -> Result<(), Error> {
    let _entry = Entry::new_public();
    if pk.len() != mldsa::public_key_len::<P>() {
        return Err(Error::BadSignature);
    }
    let mu = message
        .mu(&mldsa::tr(pk))
        .map_err(|_| Error::BadSignature)?;
    mldsa::VerifyingKey::new(mldsa::tr(pk)).verify_mu::<P>(pk, &mu, signature)
}
