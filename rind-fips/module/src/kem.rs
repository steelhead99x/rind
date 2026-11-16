// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Key encapsulation: ML-KEM-512, ML-KEM-768, and ML-KEM-1024, FIPS 203.
//!
//! A generated key passes a pairwise consistency test, as aws-lc's does
//! (mlkem-native's `MLK_CONFIG_KEYGEN_PCT`): a secret encapsulated to its
//! encapsulation key decapsulates to the same secret. An encapsulation key
//! passes FIPS 203's modulus check as rind parses it, and a ciphertext its
//! length check.

use rind::kem::{Algorithm, Ciphertext, DecapsulationKey, EncapsulationKey};
use rind::kem::{MlKem512, MlKem768, MlKem1024};
use rind::{Error, constant_time};

use crate::abi::{Encoded, Status, bytes, bytes_mut, encoded, free, handle, put, status};
use crate::ids;
use crate::scrub::{Depth, scrubbed};
use crate::selftest::{SelfTest, ensure, pct_drawing};

/// A decapsulation key of any parameter set, boxed as a handle.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Decapsulation {
    MlKem512(DecapsulationKey<MlKem512>),
    MlKem768(DecapsulationKey<MlKem768>),
    MlKem1024(DecapsulationKey<MlKem1024>),
}

/// An encapsulation key of any parameter set, boxed as a handle.
#[allow(clippy::large_enum_variant)]
#[derive(Clone)]
pub(crate) enum Encapsulation {
    MlKem512(EncapsulationKey<MlKem512>),
    MlKem768(EncapsulationKey<MlKem768>),
    MlKem1024(EncapsulationKey<MlKem1024>),
}

/// Runs `$body` with `$key` bound to whichever key `$any` (a
/// [`Decapsulation`] or [`Encapsulation`]) holds, and with `=> $wrap`, wraps
/// what it returns in `$wrap`'s variant of the same set.
macro_rules! on_kem {
    ($any:expr, $ty:ident, |$key:ident| $body:expr) => {
        match $any {
            $ty::MlKem512($key) => $body,
            $ty::MlKem768($key) => $body,
            $ty::MlKem1024($key) => $body,
        }
    };
    ($any:expr, $ty:ident => $wrap:ident, |$key:ident| $body:expr) => {
        match $any {
            $ty::MlKem512($key) => $wrap::MlKem512($body),
            $ty::MlKem768($key) => $wrap::MlKem768($body),
            $ty::MlKem1024($key) => $wrap::MlKem1024($body),
        }
    };
}

/// Runs `$body` for the parameter set `id` names (`ids::kem`), as
/// `kem_load!(id, Wrap, |A| key)`, wrapping its key in `Wrap`'s variant, or
/// `None` for an unknown `id`.
macro_rules! kem_load {
    ($id:expr, $wrap:ident, |$A:ident| $body:expr) => {
        match $id {
            ids::kem::ML_KEM_512 => {
                type $A = MlKem512;
                Some($body.map($wrap::MlKem512))
            }
            ids::kem::ML_KEM_768 => {
                type $A = MlKem768;
                Some($body.map($wrap::MlKem768))
            }
            ids::kem::ML_KEM_1024 => {
                type $A = MlKem1024;
                Some($body.map($wrap::MlKem1024))
            }
            _ => None,
        }
    };
}

/// Generates a decapsulation key of set `A`, after the pairwise consistency
/// test.
fn generate<A: Algorithm>() -> Result<DecapsulationKey<A>, Error> {
    let key = DecapsulationKey::<A>::generate()?;
    pct_drawing(
        "pct_ml_kem",
        || key.public_key().encapsulate(),
        |(ciphertext, secret)| {
            constant_time::verify(key.decapsulate(&ciphertext).as_ref(), secret.as_ref()).is_ok()
        },
    )?;
    Ok(key)
}

/// Boxes `key` at `out`, or fails for an unknown parameter set.
///
/// # Safety
/// `out` must be valid for a write.
unsafe fn kem_put<V>(key: Option<Result<V, Error>>, out: *mut *mut V) -> Status {
    let Some(key) = key else {
        return status(Err(Error::Unsupported));
    };
    status(key.map(|key| {
        // SAFETY: the caller's contract.
        unsafe { put(out, handle(key)) }
    }))
}

/// Generates a decapsulation key of the parameter set `id` names, writing
/// its handle to `out`, after the pairwise consistency test.
///
/// # Safety
/// `out` must be valid for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_generate(id: u32, out: *mut *mut Decapsulation) -> Status {
    ensure(&[SelfTest::MlKem]);
    scrubbed(Depth::Large, || {
        let key = kem_load!(id, Decapsulation, |A| generate::<A>());
        // SAFETY: the caller's contract.
        unsafe { kem_put(key, out) }
    })
}

/// The encapsulation key of `key`, writing its encoding to the `len` bytes
/// at `out`, which must be its set's encapsulation key length.
///
/// # Safety
/// `key` must be live, and `out` valid for `len` writes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_public_key(
    key: *const Decapsulation,
    out: *mut u8,
    len: usize,
) -> *mut Encapsulation {
    // SAFETY: the caller's contract.
    let key = unsafe { &*key };
    let public = on_kem!(key, Decapsulation => Encapsulation, |key| key.public_key());
    // SAFETY: the caller's contract.
    let out = unsafe { bytes_mut(out, len) };
    out.copy_from_slice(on_kem!(&public, Encapsulation, |key| key.as_ref()));
    handle(public)
}

/// Decapsulates the `len` bytes at `ciphertext` with `key`, writing the
/// secret's handle to `out`; fails unless they are its set's ciphertext
/// length.
///
/// # Safety
/// `key` must be live, `ciphertext` valid for `len` reads, and `out` for a
/// write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_decapsulate(
    key: *const Decapsulation,
    ciphertext: *const u8,
    len: usize,
    out: *mut *mut Encoded,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, ciphertext) = unsafe { (&*key, bytes(ciphertext, len)) };
    scrubbed(Depth::Large, || {
        status(on_kem!(key, Decapsulation, |key| {
            Ciphertext::new(ciphertext).map(|ciphertext| {
                // SAFETY: the caller's contract.
                unsafe { put(out, encoded(key.decapsulate(&ciphertext))) }
            })
        }))
    })
}

free!(rind_fips_kem_decapsulation_key_free, Decapsulation);

/// Parses a peer's encapsulation key for the parameter set `id` names from
/// the `len` bytes at `key`, writing its handle to `out`.
///
/// # Safety
/// `key` must be valid for `len` reads, and `out` for a write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_encapsulation_key_new(
    id: u32,
    key: *const u8,
    len: usize,
    out: *mut *mut Encapsulation,
) -> Status {
    ensure(&[SelfTest::MlKem]);
    // SAFETY: the caller's contract.
    let key = unsafe { bytes(key, len) };
    let key = kem_load!(id, Encapsulation, |A| EncapsulationKey::<A>::new(key));
    // SAFETY: the caller's contract.
    unsafe { kem_put(key, out) }
}

/// A copy of `key`.
///
/// # Safety
/// `key` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_encapsulation_key_clone(
    key: *const Encapsulation,
) -> *mut Encapsulation {
    // SAFETY: the caller's contract.
    handle(unsafe { (*key).clone() })
}

/// Encapsulates a fresh secret to `key`, writing the ciphertext to the `len`
/// bytes at `ciphertext`, which must be its set's ciphertext length, and the
/// secret's handle to `out`.
///
/// # Safety
/// `key` must be live, `ciphertext` valid for `len` writes, and `out` for a
/// write.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rind_fips_kem_encapsulate(
    key: *const Encapsulation,
    ciphertext: *mut u8,
    len: usize,
    out: *mut *mut Encoded,
) -> Status {
    // SAFETY: the caller's contract.
    let (key, ciphertext) = unsafe { (&*key, bytes_mut(ciphertext, len)) };
    scrubbed(Depth::Large, || {
        status(on_kem!(key, Encapsulation, |key| {
            key.encapsulate().map(|(sealed, secret)| {
                ciphertext.copy_from_slice(sealed.as_ref());
                // SAFETY: the caller's contract.
                unsafe { put(out, encoded(secret)) };
            })
        }))
    })
}

free!(rind_fips_kem_encapsulation_key_free, Encapsulation);
