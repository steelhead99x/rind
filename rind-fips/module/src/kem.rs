// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Key encapsulation: ML-KEM-768, FIPS 203.
//!
//! A generated key passes a pairwise consistency test, as aws-lc's does
//! (mlkem-native's `MLK_CONFIG_KEYGEN_PCT`): a secret encapsulated to its
//! encapsulation key decapsulates to the same secret. An encapsulation key
//! passes FIPS 203's modulus check as rind parses it, and a ciphertext its
//! length check.

use rind::kem::{self, DecapsulationKey, EncapsulationKey};
use rind::{Error, constant_time};

use crate::abi::{Encoded, Status, bytes, bytes_mut, encoded, free, handle, put, status};
use crate::ids;
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest, ensure, pct_drawing};

/// An encapsulation key's length.
const ENCAPSULATION_KEY_LEN: usize = 1184;

/// A ciphertext's length.
const CIPHERTEXT_LEN: usize = 1088;

/// The KEM `id` names, after its self-test.
fn algorithm(id: u32) -> Option<&'static kem::Algorithm> {
    let algorithm = match id {
        ids::kem::ML_KEM_768 => &kem::ML_KEM_768,
        _ => return None,
    };
    ensure(&[SelfTest::MlKem]);
    Some(algorithm)
}

/// Generates a decapsulation key for the KEM `id` names, writing its handle
/// to `out`, after the pairwise consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_generate(
    id: u32,
    out: *mut *mut DecapsulationKey,
) -> Status {
    let Some(algorithm) = algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    scrubbed(Depth::Large, || {
        let key = DecapsulationKey::generate(algorithm).and_then(|key| {
            pct_drawing(
                "pct_ml_kem",
                || key.public_key().encapsulate(),
                |(ciphertext, secret)| {
                    key.decapsulate(ciphertext.as_ref()).is_ok_and(|again| {
                        constant_time::verify(again.as_ref(), secret.as_ref()).is_ok()
                    })
                },
            )?;
            // SAFETY: the caller's contract.
            unsafe { put(out, handle(key)) };
            Ok(())
        });
        status(key)
    })
}

/// The encapsulation key of `key`, writing its encoding to `out`, which
/// holds 1184 bytes.
///
/// # Safety
/// `key` must be live, and `out` valid for 1184 writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_public_key(
    key: *const DecapsulationKey,
    out: *mut u8,
) -> *mut EncapsulationKey {
    // SAFETY: the caller's contract.
    let public = unsafe { (*key).public_key() };
    // SAFETY: the caller's contract.
    unsafe { bytes_mut(out, ENCAPSULATION_KEY_LEN).copy_from_slice(public.as_ref()) };
    handle(public)
}

/// Decapsulates the `len` bytes at `ciphertext` with `key`, writing the
/// secret's handle to `out`.
///
/// # Safety
/// `key` must be live, `ciphertext` valid for `len` reads, and `out` for a
/// write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_decapsulate(
    key: *const DecapsulationKey,
    ciphertext: *const u8,
    len: usize,
    out: *mut *mut Encoded,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, ciphertext) = unsafe { (&*key, bytes(ciphertext, len)) };
    scrubbed(Depth::Large, || {
        status(key.decapsulate(ciphertext).map(|secret| {
            // SAFETY: the caller's contract.
            unsafe { put(out, encoded(secret)) }
        }))
    })
}

free!(rind_fips_kem_decapsulation_key_free, DecapsulationKey);

/// Parses a peer's encapsulation key for the KEM `id` names from the `len`
/// bytes at `key`, writing its handle to `out`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_encapsulation_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut EncapsulationKey,
) -> Status {
    let Some(algorithm) = algorithm(id) else {
        return status(Err(Error::Unsupported));
    };
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    status(EncapsulationKey::new(algorithm, key).map(|key| {
        // SAFETY: the caller's contract.
        unsafe { put(out, handle(key)) }
    }))
}

/// A copy of `key`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_encapsulation_key_clone(
    key: *const EncapsulationKey,
) -> *mut EncapsulationKey {
    // SAFETY: the caller's contract.
    handle(unsafe { (*key).clone() })
}

/// Encapsulates a fresh secret to `key`, writing the ciphertext to
/// `ciphertext`, which holds 1088 bytes, and the secret's handle to `out`.
///
/// # Safety
/// `key` must be live, `ciphertext` valid for 1088 writes, and `out` for a
/// write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_encapsulate(
    key: *const EncapsulationKey,
    ciphertext: *mut u8,
    out: *mut *mut Encoded,
) -> Status {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    scrubbed(Depth::Large, || {
        status(key.encapsulate().map(|(sealed, secret)| {
            // SAFETY: the caller's contract.
            unsafe {
                bytes_mut(ciphertext, CIPHERTEXT_LEN).copy_from_slice(sealed.as_ref());
                put(out, encoded(secret));
            }
        }))
    })
}

free!(rind_fips_kem_encapsulation_key_free, EncapsulationKey);
