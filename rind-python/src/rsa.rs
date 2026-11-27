// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! `pyrind.rsa`: RSA signatures and RSA-OAEP, as `rind::rsa`.

use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::rsa;

use crate::{Bytes, PublicKeyCell, Secret, algorithm, bytes, constants, error, submodule};

/// An RSA modulus size for key generation, equal only to itself, never to
/// an int, so its hash agrees with its equality.
#[pyclass(frozen, eq, hash, from_py_object, module = "pyrind.rsa")]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
    /// An algorithm a `KeyPair` signs with.
    SigningAlgorithm(rsa::SigningAlgorithm) as "pyrind.rsa"."SigningAlgorithm" {}
);

algorithm!(
    /// An algorithm a `PublicKey` verifies with, each with its own floor on
    /// the modulus.
    VerificationAlgorithm(rsa::VerificationAlgorithm) as "pyrind.rsa"."VerificationAlgorithm" {}
);

/// An RSA public key of 1024 to 8192 bits, bound to no algorithm, whose
/// `bytes` are its PKCS#1 `RSAPublicKey`.
#[pyclass(frozen, module = "pyrind.rsa")]
pub(crate) struct PublicKey(Box<rsa::PublicKey>);

#[pymethods]
impl PublicKey {
    /// Parses a PKCS#1 `RSAPublicKey`.
    #[new]
    fn new(der: Bytes<'_>) -> PyResult<Self> {
        rsa::PublicKey::new(&der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Parses `SubjectPublicKeyInfo` DER.
    #[staticmethod]
    fn from_spki(der: Bytes<'_>) -> PyResult<Self> {
        rsa::PublicKey::from_spki(&der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a key from its big-endian modulus `n` and exponent `e`, as a
    /// JWK carries them.
    #[staticmethod]
    fn from_components(n: Bytes<'_>, e: Bytes<'_>) -> PyResult<Self> {
        let components = rsa::PublicKeyComponents { n: &*n, e: &*e };
        rsa::PublicKey::from_components(&components)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Checks `signature` over `message` with `algorithm`; raises
    /// `KeyRejected` if the modulus is below the algorithm's floor, before
    /// reading the signature, and `BadSignature` if it does not verify.
    fn verify(
        &self,
        algorithm: &Bound<'_, VerificationAlgorithm>,
        message: Bytes<'_>,
        signature: Bytes<'_>,
    ) -> PyResult<()> {
        self.0
            .verify(algorithm.get().inner, &message, &signature)
            .map_err(error)
    }

    /// The modulus's length in bytes.
    fn modulus_len(&self) -> usize {
        self.0.modulus_len()
    }

    /// Encodes the key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_spki())
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, &*self.0)
    }
}

/// An RSA key pair, which signs with any RSA signing algorithm.
#[pyclass(frozen, module = "pyrind.rsa")]
struct KeyPair {
    inner: Box<rsa::KeyPair>,
    public_key: PublicKeyCell<PublicKey>,
}

impl KeyPair {
    /// Wraps `key_pair`, with the one `PublicKey` its `public_key` returns.
    fn wrap(key_pair: Result<rsa::KeyPair, rind::Error>) -> PyResult<Self> {
        Ok(Self {
            inner: Box::new(key_pair.map_err(error)?),
            public_key: PublicKeyCell::new(),
        })
    }
}

#[pymethods]
impl KeyPair {
    /// Generates a key pair of `size`, releasing the GIL: about 30
    /// milliseconds for 2048 bits, and seconds for the largest sizes.
    #[staticmethod]
    fn generate(py: Python<'_>, size: KeySize) -> PyResult<Self> {
        let key_pair = py.detach(|| rsa::KeyPair::generate(size.into()));
        Self::wrap(key_pair)
    }

    /// Loads a PKCS#8 RSA private key.
    #[staticmethod]
    fn from_pkcs8(der: Secret<'_>) -> PyResult<Self> {
        Self::wrap(rsa::KeyPair::from_pkcs8(&der))
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    #[staticmethod]
    fn from_pkcs1(der: Secret<'_>) -> PyResult<Self> {
        Self::wrap(rsa::KeyPair::from_pkcs1(&der))
    }

    /// The public key, the same object each call, which verifies what this
    /// key pair signs with the verification algorithm of the same name.
    fn public_key(&self, py: Python<'_>) -> PyResult<Py<PublicKey>> {
        self.public_key
            .get(py, || PublicKey(Box::new(self.inner.public_key().clone())))
    }

    /// Signs `message` with `algorithm`, releasing the GIL.
    fn sign<'py>(
        &self,
        py: Python<'py>,
        algorithm: &Bound<'_, SigningAlgorithm>,
        message: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let algorithm = algorithm.get().inner;
        let signature = py
            .detach(|| self.inner.sign(algorithm, &message))
            .map_err(error)?;
        Ok(bytes(py, signature))
    }

    /// Encodes the private key as PKCS#8 DER.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_pkcs8())
    }
}

algorithm!(
    /// An RSA-OAEP algorithm.
    OaepAlgorithm(rsa::OaepAlgorithm) as "pyrind.rsa"."OaepAlgorithm" {}
);

/// An RSA-OAEP private key, which decrypts.
#[pyclass(frozen, module = "pyrind.rsa")]
struct DecryptingKey {
    inner: Box<rsa::DecryptingKey>,
    public_key: PublicKeyCell<EncryptingKey>,
}

impl DecryptingKey {
    /// Wraps `key`, with the one `EncryptingKey` its `public_key` returns.
    fn wrap(key: Result<rsa::DecryptingKey, rind::Error>) -> PyResult<Self> {
        Ok(Self {
            inner: Box::new(key.map_err(error)?),
            public_key: PublicKeyCell::new(),
        })
    }
}

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
        let key = py.detach(|| rsa::DecryptingKey::generate(algorithm, size.into()));
        Self::wrap(key)
    }

    /// Loads a PKCS#8 RSA private key for `algorithm`.
    #[staticmethod]
    fn from_pkcs8(algorithm: &Bound<'_, OaepAlgorithm>, der: Secret<'_>) -> PyResult<Self> {
        Self::wrap(rsa::DecryptingKey::from_pkcs8(algorithm.get().inner, &der))
    }

    /// Loads a PKCS#1 `RSAPrivateKey` for `algorithm`.
    #[staticmethod]
    fn from_pkcs1(algorithm: &Bound<'_, OaepAlgorithm>, der: Secret<'_>) -> PyResult<Self> {
        Self::wrap(rsa::DecryptingKey::from_pkcs1(algorithm.get().inner, &der))
    }

    /// The public key, the same object each call, which encrypts to this key
    /// with its algorithm.
    fn public_key(&self, py: Python<'_>) -> PyResult<Py<EncryptingKey>> {
        self.public_key.get(py, || {
            EncryptingKey(Box::new(self.inner.public_key().clone()))
        })
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
            .detach(|| self.inner.decrypt(&ciphertext, &label))
            .map_err(error)?;
        Ok(bytes(py, plaintext))
    }

    /// Encodes the private key as PKCS#8 DER.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_pkcs8())
    }
}

/// An RSA-OAEP public key, which encrypts.
#[pyclass(frozen, module = "pyrind.rsa")]
struct EncryptingKey(Box<rsa::EncryptingKey>);

#[pymethods]
impl EncryptingKey {
    /// Parses a PKCS#1 `RSAPublicKey` for `algorithm`.
    #[new]
    fn new(algorithm: &Bound<'_, OaepAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        rsa::EncryptingKey::new(algorithm.get().inner, &der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Parses `SubjectPublicKeyInfo` DER for `algorithm`.
    #[staticmethod]
    fn from_spki(algorithm: &Bound<'_, OaepAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        rsa::EncryptingKey::from_spki(algorithm.get().inner, &der)
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
    m.add_class::<SigningAlgorithm>()?;
    m.add_class::<VerificationAlgorithm>()?;
    m.add_class::<PublicKey>()?;
    m.add_class::<KeyPair>()?;
    m.add_class::<OaepAlgorithm>()?;
    m.add_class::<DecryptingKey>()?;
    m.add_class::<EncryptingKey>()?;
    constants!(m, OaepAlgorithm, "pyrind.rsa", {
        OAEP_SHA256 => &rsa::OAEP_SHA256,
        OAEP_SHA384 => &rsa::OAEP_SHA384,
        OAEP_SHA512 => &rsa::OAEP_SHA512,
    });
    submodule(m, "pyrind.rsa.sign", |m| {
        constants!(m, SigningAlgorithm, "pyrind.rsa.sign", {
            PKCS1_SHA256 => &rsa::sign::PKCS1_SHA256,
            PKCS1_SHA384 => &rsa::sign::PKCS1_SHA384,
            PKCS1_SHA512 => &rsa::sign::PKCS1_SHA512,
            PSS_SHA256 => &rsa::sign::PSS_SHA256,
            PSS_SHA384 => &rsa::sign::PSS_SHA384,
            PSS_SHA512 => &rsa::sign::PSS_SHA512,
        });
        Ok(())
    })?;
    submodule(m, "pyrind.rsa.verify", |m| {
        constants!(m, VerificationAlgorithm, "pyrind.rsa.verify", {
            PKCS1_SHA256 => &rsa::verify::PKCS1_SHA256,
            PKCS1_SHA384 => &rsa::verify::PKCS1_SHA384,
            PKCS1_SHA512 => &rsa::verify::PKCS1_SHA512,
            PSS_SHA256 => &rsa::verify::PSS_SHA256,
            PSS_SHA256_ANY_SALT => &rsa::verify::PSS_SHA256_ANY_SALT,
            PSS_SHA384 => &rsa::verify::PSS_SHA384,
            PSS_SHA384_ANY_SALT => &rsa::verify::PSS_SHA384_ANY_SALT,
            PSS_SHA512 => &rsa::verify::PSS_SHA512,
            PSS_SHA512_ANY_SALT => &rsa::verify::PSS_SHA512_ANY_SALT,
        });
        submodule(m, "pyrind.rsa.verify.legacy", |legacy| {
            constants!(legacy, VerificationAlgorithm, "pyrind.rsa.verify.legacy", {
                PKCS1_1024_SHA1 => &rsa::verify::legacy::PKCS1_1024_SHA1,
                PKCS1_1024_SHA256 => &rsa::verify::legacy::PKCS1_1024_SHA256,
                PKCS1_1024_SHA512 => &rsa::verify::legacy::PKCS1_1024_SHA512,
                PKCS1_3072_SHA384 => &rsa::verify::legacy::PKCS1_3072_SHA384,
                PKCS1_SHA1 => &rsa::verify::legacy::PKCS1_SHA1,
            });
            Ok(())
        })
    })?;
    submodule(m, "pyrind.rsa.legacy", |legacy| {
        constants!(legacy, OaepAlgorithm, "pyrind.rsa.legacy", {
            OAEP_SHA1 => &rsa::legacy::OAEP_SHA1,
        });
        Ok(())
    })
}
