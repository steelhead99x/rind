// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! `pyrind.cipher`'s AES-CBC and `pyrind.key_wrap`'s AES-KW, which share
//! their AES key sizes.

use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::cipher::{self, CbcIv};
use rind::key_wrap::{AesKek, Mode};
use zeroize::Zeroizing;

use crate::{Bytes, Secret, WrongLength, algorithm, bytes, bytes_with, constants, error};

algorithm!(
    /// An AES key size.
    Algorithm(cipher::Algorithm) as "pyrind.cipher"."Algorithm" {}
);

fn to_iv(iv: &[u8]) -> PyResult<[u8; 16]> {
    iv.try_into()
        .map_err(|_| WrongLength::new_err("an IV is 16 bytes"))
}

/// An AES-CBC key that encrypts.
#[pyclass(frozen, module = "pyrind.cipher")]
struct AesCbcEncryptingKey(Box<cipher::AesCbcEncryptingKey>);

#[pymethods]
impl AesCbcEncryptingKey {
    /// Expands `key` for `algorithm`; raises `WrongLength` unless it is that size.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, key: Secret<'_>) -> PyResult<Self> {
        cipher::AesCbcEncryptingKey::new(algorithm.get().inner, &key)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Encrypts whole 16-byte blocks under the 16-byte `iv`, which an
    /// attacker must not be able to predict, without padding; raises
    /// `WrongLength` for a partial block.
    fn encrypt_blocks<'py>(
        &self,
        py: Python<'py>,
        iv: Bytes<'_>,
        plaintext: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let iv = CbcIv::assume_unpredictable(to_iv(&iv)?);
        bytes_with(py, &plaintext, plaintext.len(), |out| {
            self.0.encrypt_blocks(iv, out).map_err(error)
        })
    }
}

/// An AES-CBC key that decrypts, unauthenticated: check a MAC over the IV
/// and ciphertext first.
#[pyclass(frozen, module = "pyrind.cipher")]
struct AesCbcDecryptingKey(Box<cipher::AesCbcDecryptingKey>);

#[pymethods]
impl AesCbcDecryptingKey {
    /// Expands `key` for `algorithm`; raises `WrongLength` unless it is that size.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, key: Secret<'_>) -> PyResult<Self> {
        cipher::AesCbcDecryptingKey::new(algorithm.get().inner, &key)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Decrypts whole 16-byte blocks under the 16-byte `iv`, without
    /// padding; raises `DecryptFailed` for a partial block.
    fn decrypt_blocks<'py>(
        &self,
        py: Python<'py>,
        iv: Bytes<'_>,
        ciphertext: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let iv = to_iv(&iv)?;
        bytes_with(py, &ciphertext, ciphertext.len(), |out| {
            self.0.decrypt_blocks(&iv, out).map_err(error)
        })
    }
}

/// A key-wrap mode: AES-KW (RFC 3394), for keys a multiple of 8 bytes from
/// 16, or AES-KWP (RFC 5649), for keys of any length from 1 byte; equal
/// only to itself, never to an int, so its hash agrees with its equality.
#[pyclass(
    frozen,
    eq,
    hash,
    from_py_object,
    module = "pyrind.key_wrap",
    name = "Mode"
)]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum KeyWrapMode {
    #[pyo3(name = "KW")]
    Kw,
    #[pyo3(name = "KWP")]
    Kwp,
}

impl From<KeyWrapMode> for Mode {
    fn from(mode: KeyWrapMode) -> Self {
        match mode {
            KeyWrapMode::Kw => Self::Kw,
            KeyWrapMode::Kwp => Self::Kwp,
        }
    }
}

/// An AES key-encryption key, which wraps keys with AES-KW (RFC 3394) and
/// AES-KWP (RFC 5649).
#[pyclass(frozen, module = "pyrind.key_wrap", name = "AesKek")]
struct Kek(Box<AesKek>);

#[pymethods]
impl Kek {
    /// Expands `key` for `algorithm`; raises `WrongLength` unless it is that size.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, key: Secret<'_>) -> PyResult<Self> {
        AesKek::new(algorithm.get().inner, &key)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Wraps `key` with `mode`; raises `WrongLength` for a length the mode
    /// does not take.
    fn wrap_key<'py>(
        &self,
        py: Python<'py>,
        mode: KeyWrapMode,
        key: Secret<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        // Both modes' wrapped length, as KW takes only a multiple of 8.
        let len = key.len().next_multiple_of(8) + 8;
        bytes_with(py, &[], len, |out| {
            self.0.wrap_key(mode.into(), &key, out).map_err(error)
        })
    }

    /// Unwraps `wrapped` with `mode`; raises `DecryptFailed` unless this key
    /// wrapped it in that mode.
    fn unwrap_key<'py>(
        &self,
        py: Python<'py>,
        mode: KeyWrapMode,
        wrapped: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        // rind refuses a `wrapped` too short for `mode` before it reads the
        // buffer, and KWP's key may be shorter than it, so it is copied out,
        // to scratch that is wiped before it is freed.
        let mut key = Zeroizing::new(vec![0; wrapped.len().saturating_sub(8)]);
        let len = self
            .0
            .unwrap_key(mode.into(), &wrapped, &mut key)
            .map_err(error)?
            .len();
        Ok(bytes(py, &key[..len]))
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Algorithm>()?;
    m.add_class::<AesCbcEncryptingKey>()?;
    m.add_class::<AesCbcDecryptingKey>()?;
    constants!(m, Algorithm, "pyrind.cipher", {
        AES_128 => &cipher::AES_128,
        AES_192 => &cipher::AES_192,
        AES_256 => &cipher::AES_256,
    });
    Ok(())
}

pub(crate) fn register_key_wrap(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<KeyWrapMode>()?;
    m.add_class::<Kek>()?;
    constants!(m, Algorithm, "pyrind.key_wrap", {
        AES_128 => &cipher::AES_128,
        AES_192 => &cipher::AES_192,
        AES_256 => &cipher::AES_256,
    });
    Ok(())
}
