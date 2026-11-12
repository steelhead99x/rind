// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Operations the unpublished `rind-acvp` wrapper needs.
//!
//! Compiled only with `--features acvp`. Nothing here is a supported API:
//! rind's callers generate keys from the system RNG and sign with fresh
//! randomness.

use crate::error::Error;
use crate::low::PosInt;
use crate::mid::mlkem768::{Ciphertext, DecapKey, EncapKey, Message};

const RSA_WORDS: usize = 8192 / 64;
const MLKEM_DK: usize = 2400;
const MLKEM_EK: usize = 1184;
const MLKEM_C: usize = 1088;

/// ML-KEM-768 key generation from FIPS 203's 64-byte seed `d || z`.
///
/// Returns `(ek, dk)`.
pub fn mlkem768_keygen(seed: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let _entry = crate::low::Entry::new_secret();
    let seed: &[u8; 64] = seed.try_into().map_err(|_| Error::WrongLength)?;
    let key = DecapKey::keygen_internal(seed);
    Ok((
        key.encapsulation_key().as_bytes().to_vec(),
        key.as_bytes().to_vec(),
    ))
}

/// ML-KEM-768 encapsulation of a given 32-byte message.
///
/// Returns `(ciphertext, shared secret)`.
pub fn mlkem768_encaps(ek: &[u8], m: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let _entry = crate::low::Entry::new_secret();
    let ek: &[u8; MLKEM_EK] = ek.try_into().map_err(|_| Error::WrongLength)?;
    let m: [u8; 32] = m.try_into().map_err(|_| Error::WrongLength)?;
    let key = EncapKey::from_bytes(ek)?;
    let (secret, ciphertext) = key.encaps_internal(Message(m));
    Ok((ciphertext.as_ref().to_vec(), secret.as_ref().to_vec()))
}

/// ML-KEM-768 decapsulation of an expanded decapsulation key.
pub fn mlkem768_decaps(dk: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
    let _entry = crate::low::Entry::new_secret();
    let dk: &[u8; MLKEM_DK] = dk.try_into().map_err(|_| Error::WrongLength)?;
    let ciphertext: [u8; MLKEM_C] = ciphertext.try_into().map_err(|_| Error::WrongLength)?;
    let key = DecapKey::from_bytes(dk).ok_or(Error::WrongLength)?;
    Ok(key.decaps(&Ciphertext::from(ciphertext)).as_ref().to_vec())
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

/// `base` ^ `exp` mod `modulus`, at `modulus`'s width, or `None` when `base`
/// is not below the modulus.
///
/// ACVP's RSA signature and decryption primitives send `d` and `n` without
/// the CRT components rind's signing path uses. The exponentiation is still
/// rind's.
pub fn rsa_modexp(base: &[u8], exp: &[u8], modulus: &[u8]) -> Option<Vec<u8>> {
    let _entry = crate::low::Entry::new_secret();
    let base = PosInt::<RSA_WORDS>::from_bytes(base).ok()?;
    let exp = PosInt::<RSA_WORDS>::from_bytes(exp).ok()?;
    let modulus_n = PosInt::<RSA_WORDS>::from_bytes(modulus).ok()?;
    if !base.less_than(&modulus_n) {
        return None;
    }
    let mont = modulus_n.montifier();
    let n0 = modulus_n.mont_neg_inverse();
    let out = base.mod_exp(&exp, &modulus_n, &mont, n0);
    let mut bytes = vec![0u8; modulus.len()];
    out.to_bytes(&mut bytes).ok()?;
    crate::low::ct::public_slice(&bytes);
    Some(bytes)
}
