// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::rsa;

use crate::{Bytes, algorithm, bytes, constants, error, submodule};

/// An RSA modulus size for key generation.
#[pyclass(frozen, eq, eq_int, from_py_object, module = "pyrind.rsa")]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum KeySize {
    #[pyo3(name = "RSA_2048")]
    Rsa2048,
    #[pyo3(name = "RSA_3072")]
    Rsa3072,
    #[pyo3(name = "RSA_4096")]
    Rsa4096,
    #[pyo3(name = "RSA_6144")]
    Rsa6144,
    #[pyo3(name = "RSA_8192")]
    Rsa8192,
}

impl From<KeySize> for rsa::KeySize {
    fn from(size: KeySize) -> Self {
        match size {
            KeySize::Rsa2048 => Self::Rsa2048,
            KeySize::Rsa3072 => Self::Rsa3072,
            KeySize::Rsa4096 => Self::Rsa4096,
            KeySize::Rsa6144 => Self::Rsa6144,
            KeySize::Rsa8192 => Self::Rsa8192,
        }
    }
}

algorithm!(
    /// An RSA-OAEP algorithm.
    OaepAlgorithm(rsa::OaepAlgorithm) as "pyrind.rsa"."OaepAlgorithm" {}
);

/// An RSA-OAEP private key, which decrypts.
#[pyclass(frozen, module = "pyrind.rsa")]
struct DecryptingKey(Box<rsa::DecryptingKey>);

#[pymethods]
impl DecryptingKey {
    /// Generates a key of `size` for `algorithm`, releasing the GIL: about
    /// 30 milliseconds for 2048 bits, and seconds for the largest sizes.
    #[staticmethod]
    fn generate(
        py: Python<'_>,
        algorithm: &Bound<'_, OaepAlgorithm>,
        size: KeySize,
    ) -> PyResult<Self> {
        let algorithm = algorithm.get().inner;
        py.detach(|| rsa::DecryptingKey::generate(algorithm, size.into()))
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a PKCS#8 RSA private key for `algorithm`.
    #[staticmethod]
    fn from_pkcs8(algorithm: &Bound<'_, OaepAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        rsa::DecryptingKey::from_pkcs8(algorithm.get().inner, &der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a PKCS#1 `RSAPrivateKey` for `algorithm`.
    #[staticmethod]
    fn from_pkcs1(algorithm: &Bound<'_, OaepAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        rsa::DecryptingKey::from_pkcs1(algorithm.get().inner, &der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// The public key, which encrypts to this key with its algorithm.
    fn public_key(&self) -> EncryptingKey {
        EncryptingKey(Box::new(self.0.public_key().clone()))
    }

    /// Decrypts `ciphertext`, encrypted with `label`, releasing the GIL.
    ///
    /// Every malformed ciphertext raises the same `DecryptFailed`, and bad
    /// padding takes as long to find as good, so revealing the failure is no
    /// padding oracle.
    #[pyo3(signature = (ciphertext, *, label))]
    fn decrypt<'py>(
        &self,
        py: Python<'py>,
        ciphertext: Bytes<'_>,
        label: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let plaintext = py
            .detach(|| self.0.decrypt(&ciphertext, &label))
            .map_err(error)?;
        Ok(bytes(py, plaintext))
    }

    /// Encodes the private key as PKCS#8 DER.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_pkcs8())
    }

    /// Encodes the public key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.public_key().to_spki())
    }
}

/// An RSA-OAEP public key, which encrypts.
#[pyclass(frozen, module = "pyrind.rsa")]
struct EncryptingKey(Box<rsa::EncryptingKey>);

#[pymethods]
impl EncryptingKey {
    /// Parses a PKCS#1 `RSAPublicKey` or a `SubjectPublicKeyInfo` for
    /// `algorithm`.
    #[new]
    fn new(algorithm: &Bound<'_, OaepAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        let algorithm = algorithm.get().inner;
        rsa::EncryptingKey::new(algorithm, &der)
            .or_else(|_| rsa::EncryptingKey::from_spki(algorithm, &der))
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a key for `algorithm` from its big-endian modulus `n` and
    /// exponent `e`, as a JWK carries them.
    #[staticmethod]
    fn from_components(
        algorithm: &Bound<'_, OaepAlgorithm>,
        n: Bytes<'_>,
        e: Bytes<'_>,
    ) -> PyResult<Self> {
        let components = rsa::PublicKeyComponents { n: &*n, e: &*e };
        rsa::EncryptingKey::from_components(algorithm.get().inner, &components)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Encrypts `message` with `label`, returning a ciphertext as long as the
    /// modulus; raises `WrongLength` past `max_message_len`.
    #[pyo3(signature = (message, *, label))]
    fn encrypt<'py>(
        &self,
        py: Python<'py>,
        message: Bytes<'_>,
        label: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let ciphertext = self.0.encrypt(&message, &label).map_err(error)?;
        Ok(bytes(py, ciphertext))
    }

    /// The longest message this key encrypts.
    #[getter]
    fn max_message_len(&self) -> usize {
        self.0.max_message_len()
    }

    /// Encodes the key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_spki())
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<KeySize>()?;
    m.add_class::<OaepAlgorithm>()?;
    m.add_class::<DecryptingKey>()?;
    m.add_class::<EncryptingKey>()?;
    constants!(m, OaepAlgorithm, "pyrind.rsa", {
        OAEP_SHA256 => &rsa::OAEP_SHA256,
        OAEP_SHA384 => &rsa::OAEP_SHA384,
        OAEP_SHA512 => &rsa::OAEP_SHA512,
    });
    submodule(m, "pyrind.rsa.legacy", |legacy| {
        constants!(legacy, OaepAlgorithm, "pyrind.rsa.legacy", {
            OAEP_SHA1 => &rsa::legacy::OAEP_SHA1,
        });
        Ok(())
    })
}
