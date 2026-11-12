// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Operations the unpublished `rind-acvp` binary needs.
//!
//! Not a supported API. The `__acvp` feature exists so that binary can answer
//! NIST's seeded tests. rind's callers generate keys from the system RNG and
//! sign with fresh randomness. Cargo features are public and additive, so the
//! `__` prefix, matching `__ctgrind`, is what marks this one internal.

use crate::error::{Error, KeyFormatError};
use crate::low::PosInt;
use crate::low::{Zeroable, zeroise, zeroise_value};
use crate::mid::mlkem768::{Ciphertext, DecapKey, EncapKey, Message};

const RSA_WORDS: usize = 8192 / 64;
const MLKEM_DK: usize = 2400;
const MLKEM_EK: usize = 1184;
const MLKEM_C: usize = 1088;

/// An ML-DSA-87 expanded private key, the largest secret this module returns.
const SECRET_LEN: usize = 4896;

/// A secret byte string wiped on drop under the `wipe` feature.
///
/// The bytes live in the value, not a `Vec`, so `rind/tests/zeroing.rs` can
/// see every byte after `Drop` and before the allocation is freed. A `Vec`
/// frees its buffer inside `Drop`, so that test would only see the header.
#[doc(hidden)]
pub struct SecretBuf {
    bytes: [u8; SECRET_LEN],
    len: usize,
}

impl SecretBuf {
    /// Copies `bytes` and marks the copy secret.
    ///
    /// # Panics
    ///
    /// Panics if `bytes` is longer than an ML-DSA-87 expanded private key.
    /// Every secret this module returns is that long or shorter.
    pub fn from_slice(bytes: &[u8]) -> Self {
        assert!(
            bytes.len() <= SECRET_LEN,
            "secret of {} bytes exceeds {SECRET_LEN}",
            bytes.len()
        );
        let mut secret = Self {
            bytes: [0; SECRET_LEN],
            len: bytes.len(),
        };
        secret.bytes[..bytes.len()].copy_from_slice(bytes);
        crate::low::ct::secret_slice(secret.as_slice());
        secret
    }

    /// The secret bytes.
    pub fn as_slice(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl AsRef<[u8]> for SecretBuf {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl core::fmt::Debug for SecretBuf {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SecretBuf")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl Drop for SecretBuf {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for SecretBuf {}

/// Copies `bytes` into a [`SecretBuf`] and wipes the array it took.
fn secret_array<const N: usize>(mut bytes: [u8; N]) -> SecretBuf {
    let secret = SecretBuf::from_slice(&bytes);
    zeroise(&mut bytes);
    secret
}

/// ML-KEM-768 key generation from FIPS 203's 64-byte seed `d || z`.
///
/// Returns `(ek, dk)`. `dk` is wiped on drop.
pub fn mlkem768_keygen(seed: &[u8]) -> Result<(Vec<u8>, SecretBuf), Error> {
    let _entry = crate::low::Entry::new_secret();
    let seed: &[u8; 64] = seed.try_into().map_err(|_| Error::WrongLength)?;
    let key = DecapKey::keygen_internal(seed);
    let ek = key.encapsulation_key().as_bytes().to_vec();
    let dk = secret_array(key.as_bytes());
    Ok((ek, dk))
}

/// ML-KEM-768 encapsulation of a given 32-byte message.
///
/// Returns `(ciphertext, shared secret)`. The shared secret is wiped on drop.
pub fn mlkem768_encaps(ek: &[u8], m: &[u8]) -> Result<(Vec<u8>, SecretBuf), Error> {
    let _entry = crate::low::Entry::new_secret();
    let ek: &[u8; MLKEM_EK] = ek.try_into().map_err(|_| Error::WrongLength)?;
    let m: [u8; 32] = m.try_into().map_err(|_| Error::WrongLength)?;
    let key = EncapKey::from_bytes(ek)?;
    let (secret, ciphertext) = key.encaps_internal(Message(m));
    Ok((ciphertext.as_ref().to_vec(), secret_array(*secret.as_ref())))
}

/// ML-KEM-768 decapsulation of an expanded decapsulation key.
///
/// A `dk` whose length is not 2400 bytes is [`Error::WrongLength`]: the
/// caller handed over a buffer of the wrong size. A 2400-byte `dk` that the
/// decapsulation-key check refuses is [`Error::KeyRejected`], the modulus
/// check. That refusal is the embedded encapsulation key failing FIPS 203's
/// modulus check, or `H(ek)` not matching that key. Neither is a length
/// error, and the modulus check is the error rind already uses for an
/// encapsulation key that fails it.
///
/// The shared secret is wiped on drop.
pub fn mlkem768_decaps(dk: &[u8], ciphertext: &[u8]) -> Result<SecretBuf, Error> {
    let _entry = crate::low::Entry::new_secret();
    let dk: &[u8; MLKEM_DK] = dk.try_into().map_err(|_| Error::WrongLength)?;
    let ciphertext: [u8; MLKEM_C] = ciphertext.try_into().map_err(|_| Error::WrongLength)?;
    let key = DecapKey::from_bytes(dk).ok_or(KeyFormatError::MlKemModulus)?;
    Ok(secret_array(
        *key.decaps(&Ciphertext::from(ciphertext)).as_ref(),
    ))
}

/// Whether `ek` passes FIPS 203's encapsulation-key check.
pub fn mlkem768_ek_ok(ek: &[u8]) -> bool {
    let Ok(ek) = ek.try_into() else {
        return false;
    };
    EncapKey::from_bytes(ek).is_ok()
}

/// Whether `dk` passes FIPS 203's decapsulation-key check.
pub fn mlkem768_dk_ok(dk: &[u8]) -> bool {
    let Ok(dk) = dk.try_into() else {
        return false;
    };
    DecapKey::from_bytes(dk).is_some()
}

/// `base` ^ `exp` mod `modulus`, at `modulus`'s byte length, or `None`.
///
/// `None` covers a `base` that is not below the modulus, a modulus that is
/// even or zero, or a value that does not fit. Montgomery reduction requires
/// an odd modulus, so an even or zero modulus is refused before that
/// reduction runs.
///
/// The result is secret. ACVP uses this for the RSA signature primitive and
/// for decryption, and `m^d mod n` is then as good as `d`. It is returned in
/// a [`SecretBuf`] and is not marked public.
///
/// The exponentiation's trace follows the exponent's width. A shorter
/// exponent is widened to the modulus, so that trace follows the public
/// modulus length rather than how many leading zeros the exponent's encoding
/// had. An exponent wider than the modulus is left as it is: widening it
/// would drop its high words, and its trace stays that wider length.
pub fn rsa_modexp(base: &[u8], exp: &[u8], modulus: &[u8]) -> Option<SecretBuf> {
    let _entry = crate::low::Entry::new_secret();
    let base = PosInt::<RSA_WORDS>::from_bytes(base).ok()?;
    let mut exp = PosInt::<RSA_WORDS>::from_bytes(exp).ok()?;
    let modulus_n = PosInt::<RSA_WORDS>::from_bytes(modulus).ok()?;
    if modulus_n.is_even() || !base.less_than(&modulus_n) {
        return None;
    }
    exp.widen_to(&modulus_n);
    let mont = modulus_n.montifier();
    let n0 = modulus_n.mont_neg_inverse();
    let out = base.mod_exp(&exp, &modulus_n, &mont, n0);
    let mut bytes = vec![0u8; modulus.len()];
    out.to_bytes(&mut bytes).ok()?;
    let secret = SecretBuf::from_slice(&bytes);
    zeroise(&mut bytes);
    Some(secret)
}
