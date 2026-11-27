// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! `pyrind.ed25519`: Ed25519 signatures (RFC 8032), as `rind::ed25519`.

use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::ed25519;

use crate::{Bytes, PublicKeyCell, Secret, bytes, error};

/// An Ed25519 public key, whose `bytes` are its 32-byte encoding.
#[pyclass(frozen, module = "pyrind.ed25519")]
pub(crate) struct PublicKey(Box<ed25519::PublicKey>);

#[pymethods]
impl PublicKey {
    /// Parses a 32-byte public key, refusing one of small order.
    #[new]
    fn new(data: Bytes<'_>) -> PyResult<Self> {
        ed25519::PublicKey::new(&data)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Parses `SubjectPublicKeyInfo` DER, refusing one that names another
    /// algorithm.
    #[staticmethod]
    fn from_spki(der: Bytes<'_>) -> PyResult<Self> {
        ed25519::PublicKey::from_spki(&der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Checks `signature` over `message`; raises `BadSignature` if it does
    /// not verify.
    fn verify(&self, message: Bytes<'_>, signature: Bytes<'_>) -> PyResult<()> {
        self.0.verify(&message, &signature).map_err(error)
    }

    /// Encodes the key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_spki())
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, &*self.0)
    }
}

/// An Ed25519 key pair.
#[pyclass(frozen, module = "pyrind.ed25519")]
struct KeyPair {
    inner: Box<ed25519::KeyPair>,
    public_key: PublicKeyCell<PublicKey>,
}

impl KeyPair {
    /// Wraps `key_pair`, with the one `PublicKey` its `public_key` returns.
    fn wrap(key_pair: Result<ed25519::KeyPair, rind::Error>) -> PyResult<Self> {
        Ok(Self {
            inner: Box::new(key_pair.map_err(error)?),
            public_key: PublicKeyCell::new(),
        })
    }
}

#[pymethods]
impl KeyPair {
    /// Generates a key pair.
    #[staticmethod]
    fn generate() -> PyResult<Self> {
        Self::wrap(ed25519::KeyPair::generate())
    }

    /// Loads a key pair from PKCS#8 v1 or v2 DER, refused if a v2 key's
    /// public key does not match.
    #[staticmethod]
    fn from_pkcs8(der: Secret<'_>) -> PyResult<Self> {
        Self::wrap(ed25519::KeyPair::from_pkcs8(&der))
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    #[staticmethod]
    fn from_seed(seed: Secret<'_>) -> PyResult<Self> {
        Self::wrap(ed25519::KeyPair::from_seed(&seed))
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    #[staticmethod]
    fn from_seed_and_public_key(seed: Secret<'_>, public_key: Bytes<'_>) -> PyResult<Self> {
        Self::wrap(ed25519::KeyPair::from_seed_and_public_key(
            &seed,
            &public_key,
        ))
    }

    /// The public key, the same object each call.
    fn public_key(&self, py: Python<'_>) -> PyResult<Py<PublicKey>> {
        self.public_key
            .get(py, || PublicKey(Box::new(self.inner.public_key().clone())))
    }

    /// Signs `message`.
    fn sign<'py>(&self, py: Python<'py>, message: Bytes<'_>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.sign(&message))
    }

    /// Encodes the key pair as PKCS#8 v2 DER (RFC 5958), with its public key.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_pkcs8())
    }

    /// Encodes the private key as PKCS#8 v1 DER (RFC 8410), as OpenSSL
    /// writes it.
    fn to_pkcs8v1<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_pkcs8v1())
    }

    /// Returns the private key's 32-byte seed.
    fn to_seed<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_seed())
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PublicKey>()?;
    m.add_class::<KeyPair>()
}
