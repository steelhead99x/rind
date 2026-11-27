// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::aead;

use crate::{Bytes, Secret, WrongLength, algorithm, bytes, bytes_with, constants, error};

const TAG_LEN: usize = 16;

algorithm!(
    /// An AEAD algorithm.
    Algorithm(aead::Algorithm) as "pyrind.aead"."Algorithm" {
    /// The key's length in bytes.
    #[getter]
    fn key_len(&self) -> usize {
        self.inner.key_len()
    }

    /// The nonce's length in bytes.
    #[getter]
    fn nonce_len(&self) -> usize {
        self.inner.nonce_len()
    }

    /// The tag's length in bytes.
    #[getter]
    fn tag_len(&self) -> usize {
        self.inner.tag_len()
    }
    }
);

/// Copies `plaintext` into a new `bytes` one tag longer, and seals it there
/// with `seal`, which returns the tag.
fn seal_into<'py, T: AsRef<[u8]>>(
    py: Python<'py>,
    plaintext: &[u8],
    seal: impl FnOnce(&mut [u8]) -> Result<T, rind::Error>,
) -> PyResult<Bound<'py, PyBytes>> {
    bytes_with(py, plaintext, plaintext.len() + TAG_LEN, |out| {
        let (body, tag) = out.split_at_mut(plaintext.len());
        tag.copy_from_slice(seal(body).map_err(error)?.as_ref());
        Ok(())
    })
}

/// Copies `ciphertext`, less its tag, into a new `bytes`, and opens it there
/// with `open`, which takes the tag.
fn open_into<'py>(
    py: Python<'py>,
    ciphertext: &[u8],
    open: impl FnOnce(&mut [u8], [u8; TAG_LEN]) -> Result<(), rind::Error>,
) -> PyResult<Bound<'py, PyBytes>> {
    let (body, tag) = ciphertext
        .split_last_chunk::<TAG_LEN>()
        .ok_or_else(|| error(rind::Error::DecryptFailed))?;
    bytes_with(py, body, body.len(), |out| open(out, *tag).map_err(error))
}

/// An AEAD key, which seals with the caller's nonces.
///
/// Sealing two messages with one nonce under one key loses confidentiality
/// and lets anyone forge messages, so derive nonces from state that never
/// repeats, such as a sequence number, or use `RandomizedNonceKey`.
#[pyclass(frozen, module = "pyrind.aead")]
pub(crate) struct Key(pub(crate) Box<aead::Key>);

#[pymethods]
impl Key {
    /// Expands `key` for `algorithm`; raises `WrongLength` unless it is
    /// `algorithm.key_len` bytes.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, key: Secret<'_>) -> PyResult<Self> {
        aead::Key::new(algorithm.get().inner, &key)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Encrypts `plaintext` under `nonce`, authenticating `aad` with it, and
    /// returns the ciphertext with the tag appended.
    #[pyo3(signature = (nonce, plaintext, *, aad))]
    fn seal<'py>(
        &self,
        py: Python<'py>,
        nonce: Bytes<'_>,
        plaintext: Bytes<'_>,
        aad: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let nonce = nonce_of(&nonce)?;
        seal_into(py, &plaintext, |body| {
            self.0.seal_in_place_separate_tag(nonce, &aad, body)
        })
    }

    /// Decrypts and verifies `ciphertext`, sealed under `nonce` with `aad`,
    /// and returns the plaintext; raises `DecryptFailed` if it does not
    /// verify.
    #[pyo3(signature = (nonce, ciphertext, *, aad))]
    fn open<'py>(
        &self,
        py: Python<'py>,
        nonce: Bytes<'_>,
        ciphertext: Bytes<'_>,
        aad: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let nonce = nonce_of(&nonce)?;
        open_into(py, &ciphertext, |body, tag| {
            self.0
                .open_in_place_separate_tag(nonce, &aad, aead::Tag::try_from(&tag[..])?, body)
                .map(drop)
        })
    }
}

fn nonce_of(nonce: &[u8]) -> PyResult<aead::Nonce> {
    let nonce = nonce
        .try_into()
        .map_err(|_| WrongLength::new_err("a nonce is 12 bytes"))?;
    Ok(aead::Nonce::assume_unique_for_key(nonce))
}

/// An XChaCha20-Poly1305 key that picks a random 192-bit nonce for every
/// seal, so the caller tracks no nonce state.
#[pyclass(frozen, module = "pyrind.aead")]
struct RandomizedNonceKey(Box<aead::RandomizedNonceKey>);

#[pymethods]
impl RandomizedNonceKey {
    /// Makes a key from 32 bytes of key material; raises `WrongLength`
    /// otherwise.
    #[new]
    fn new(key: Secret<'_>) -> PyResult<Self> {
        let key = (*key)
            .try_into()
            .map_err(|_| error(rind::Error::WrongLength))?;
        Ok(Self(Box::new(aead::RandomizedNonceKey::new(key))))
    }

    /// Encrypts `plaintext` under a fresh random nonce, authenticating `aad`
    /// with it, and returns the nonce, which the opener needs, and the
    /// ciphertext with the tag appended.
    #[pyo3(signature = (plaintext, *, aad))]
    fn seal<'py>(
        &self,
        py: Python<'py>,
        plaintext: Bytes<'_>,
        aad: Bytes<'_>,
    ) -> PyResult<(Bound<'py, PyBytes>, Bound<'py, PyBytes>)> {
        let mut sealed = plaintext.to_vec();
        let nonce = self
            .0
            .seal_in_place_append_tag(&aad, &mut sealed)
            .map_err(error)?;
        Ok((bytes(py, nonce), bytes(py, sealed)))
    }

    /// Decrypts and verifies `ciphertext`, sealed under `nonce` with `aad`,
    /// and returns the plaintext; raises `DecryptFailed` if it does not
    /// verify.
    #[pyo3(signature = (nonce, ciphertext, *, aad))]
    fn open<'py>(
        &self,
        py: Python<'py>,
        nonce: Bytes<'_>,
        ciphertext: Bytes<'_>,
        aad: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let nonce: [u8; 24] = (*nonce)
            .try_into()
            .map_err(|_| WrongLength::new_err("a nonce is 24 bytes"))?;
        let mut sealed = ciphertext.to_vec();
        let plaintext = self
            .0
            .open_in_place(nonce.into(), &aad, &mut sealed)
            .map_err(error)?;
        Ok(bytes(py, plaintext))
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Algorithm>()?;
    m.add_class::<Key>()?;
    m.add_class::<RandomizedNonceKey>()?;
    constants!(m, Algorithm, "pyrind.aead", {
        AES_128_GCM => &aead::AES_128_GCM,
        AES_192_GCM => &aead::AES_192_GCM,
        AES_256_GCM => &aead::AES_256_GCM,
        CHACHA20_POLY1305 => &aead::CHACHA20_POLY1305,
    });
    Ok(())
}
