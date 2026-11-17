// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::agreement;

use crate::{Bytes, PublicKeyCell, algorithm, bytes, constants, error};

algorithm!(
    /// A key agreement algorithm.
    Algorithm(agreement::Algorithm) as "pyrind.agreement"."Algorithm" {}
);

/// A private key for key agreement.
#[pyclass(frozen, module = "pyrind.agreement")]
struct PrivateKey {
    inner: Box<agreement::PrivateKey>,
    public_key: PublicKeyCell<PublicKey>,
}

impl PrivateKey {
    /// Wraps `key`, with the one `PublicKey` its `public_key` returns.
    fn wrap(key: Result<agreement::PrivateKey, rind::Error>) -> PyResult<Self> {
        Ok(Self {
            inner: Box::new(key.map_err(error)?),
            public_key: PublicKeyCell::new(),
        })
    }
}

#[pymethods]
impl PrivateKey {
    /// Generates a key for `algorithm`.
    #[staticmethod]
    fn generate(algorithm: &Bound<'_, Algorithm>) -> PyResult<Self> {
        Self::wrap(agreement::PrivateKey::generate(algorithm.get().inner))
    }

    /// Loads a key for `algorithm` from its big-endian scalar, or for X25519
    /// its 32 bytes.
    #[staticmethod]
    fn from_scalar(algorithm: &Bound<'_, Algorithm>, scalar: Bytes<'_>) -> PyResult<Self> {
        Self::wrap(agreement::PrivateKey::from_scalar(
            algorithm.get().inner,
            &scalar,
        ))
    }

    /// Loads a key for `algorithm` from PKCS#8 DER.
    #[staticmethod]
    fn from_pkcs8(algorithm: &Bound<'_, Algorithm>, der: Bytes<'_>) -> PyResult<Self> {
        Self::wrap(agreement::PrivateKey::from_pkcs8(
            algorithm.get().inner,
            &der,
        ))
    }

    /// Loads an ECDH key for `algorithm` from SEC1 `ECPrivateKey` DER.
    #[staticmethod]
    fn from_sec1(algorithm: &Bound<'_, Algorithm>, der: Bytes<'_>) -> PyResult<Self> {
        Self::wrap(agreement::PrivateKey::from_sec1(
            algorithm.get().inner,
            &der,
        ))
    }

    /// The public key to send the peer, the same object each call.
    fn public_key(&self, py: Python<'_>) -> PyResult<Py<PublicKey>> {
        self.public_key
            .get(py, || PublicKey(Box::new(self.inner.public_key().clone())))
    }

    /// Agrees a shared secret with the peer's public key `peer`, as
    /// `bytes(PublicKey)` encodes it; raises `KeyRejected` for an invalid
    /// one.
    fn agree<'py>(&self, py: Python<'py>, peer: Bytes<'_>) -> PyResult<Bound<'py, PyBytes>> {
        let secret = self.inner.agree(&peer).map_err(error)?;
        Ok(bytes(py, secret))
    }

    /// Encodes the key as PKCS#8 DER.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_pkcs8())
    }

    /// Returns the key's scalar, as `from_scalar` takes it.
    fn to_scalar<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_scalar())
    }
}

/// A public key for key agreement, whose `bytes` are what `agree` takes:
/// 32 bytes for X25519, and an uncompressed SEC1 point for ECDH.
#[pyclass(frozen, module = "pyrind.agreement")]
struct PublicKey(Box<agreement::PublicKey>);

#[pymethods]
impl PublicKey {
    /// Parses a public key for `algorithm` from its `bytes` encoding.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, data: Bytes<'_>) -> PyResult<Self> {
        agreement::PublicKey::new(algorithm.get().inner, &data)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Parses a public key for `algorithm` from `SubjectPublicKeyInfo` DER.
    #[staticmethod]
    fn from_spki(algorithm: &Bound<'_, Algorithm>, der: Bytes<'_>) -> PyResult<Self> {
        agreement::PublicKey::from_spki(algorithm.get().inner, &der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Encodes the key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_spki())
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, &*self.0)
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Algorithm>()?;
    m.add_class::<PrivateKey>()?;
    m.add_class::<PublicKey>()?;
    constants!(m, Algorithm, "pyrind.agreement", {
        X25519 => &agreement::X25519,
        ECDH_P256 => &agreement::ECDH_P256,
        ECDH_P384 => &agreement::ECDH_P384,
        ECDH_P521 => &agreement::ECDH_P521,
    });
    Ok(())
}
