// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! `pyrind.ecdsa`: ECDSA on P-256, P-384, and P-521, as `rind::ecdsa`.

use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::ecdsa;

use crate::{Bytes, PublicKeyCell, algorithm, bytes, constants, error, submodule};

algorithm!(
    /// An algorithm a `KeyPair` signs with.
    SigningAlgorithm(ecdsa::SigningAlgorithm) as "pyrind.ecdsa"."SigningAlgorithm" {}
);

algorithm!(
    /// An algorithm a `PublicKey` verifies with.
    VerificationAlgorithm(ecdsa::VerificationAlgorithm) as "pyrind.ecdsa"."VerificationAlgorithm" {}
);

/// An ECDSA public key, which verifies with one algorithm, and whose `bytes`
/// are its uncompressed SEC1 point.
#[pyclass(frozen, module = "pyrind.ecdsa")]
pub(crate) struct PublicKey(Box<ecdsa::PublicKey>);

#[pymethods]
impl PublicKey {
    /// Parses an uncompressed SEC1 point for `algorithm`.
    #[new]
    fn new(algorithm: &Bound<'_, VerificationAlgorithm>, point: Bytes<'_>) -> PyResult<Self> {
        ecdsa::PublicKey::new(algorithm.get().inner, &point)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Parses `SubjectPublicKeyInfo` DER for `algorithm`, refusing one that
    /// names another curve.
    #[staticmethod]
    fn from_spki(algorithm: &Bound<'_, VerificationAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        ecdsa::PublicKey::from_spki(algorithm.get().inner, &der)
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

/// An ECDSA key pair, which signs with one algorithm.
#[pyclass(frozen, module = "pyrind.ecdsa")]
struct KeyPair {
    inner: Box<ecdsa::KeyPair>,
    public_key: PublicKeyCell<PublicKey>,
}

impl KeyPair {
    /// Wraps `key_pair`, with the one `PublicKey` its `public_key` returns.
    fn wrap(key_pair: Result<ecdsa::KeyPair, rind::Error>) -> PyResult<Self> {
        Ok(Self {
            inner: Box::new(key_pair.map_err(error)?),
            public_key: PublicKeyCell::new(),
        })
    }
}

#[pymethods]
impl KeyPair {
    /// Generates a key pair for `algorithm`.
    #[staticmethod]
    fn generate(algorithm: &Bound<'_, SigningAlgorithm>) -> PyResult<Self> {
        Self::wrap(ecdsa::KeyPair::generate(algorithm.get().inner))
    }

    /// Loads a key pair for `algorithm` from PKCS#8 DER.
    #[staticmethod]
    fn from_pkcs8(algorithm: &Bound<'_, SigningAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        Self::wrap(ecdsa::KeyPair::from_pkcs8(algorithm.get().inner, &der))
    }

    /// Loads a key pair for `algorithm` from SEC1 `ECPrivateKey` DER.
    #[staticmethod]
    fn from_sec1(algorithm: &Bound<'_, SigningAlgorithm>, der: Bytes<'_>) -> PyResult<Self> {
        Self::wrap(ecdsa::KeyPair::from_sec1(algorithm.get().inner, &der))
    }

    /// Loads a key pair for `algorithm` from its big-endian scalar and its
    /// uncompressed public key, as a JWK's `d`, `x`, and `y` carry them,
    /// refused unless they match.
    #[staticmethod]
    fn from_scalar_and_public_key(
        algorithm: &Bound<'_, SigningAlgorithm>,
        scalar: Bytes<'_>,
        public_key: Bytes<'_>,
    ) -> PyResult<Self> {
        let algorithm = algorithm.get().inner;
        Self::wrap(ecdsa::KeyPair::from_scalar_and_public_key(
            algorithm,
            &scalar,
            &public_key,
        ))
    }

    /// The public key, the same object each call, which verifies with the
    /// verification algorithm of the same name.
    fn public_key(&self, py: Python<'_>) -> PyResult<Py<PublicKey>> {
        self.public_key
            .get(py, || PublicKey(Box::new(self.inner.public_key().clone())))
    }

    /// Signs `message`.
    fn sign<'py>(&self, py: Python<'py>, message: Bytes<'_>) -> PyResult<Bound<'py, PyBytes>> {
        let signature = self.inner.sign(&message).map_err(error)?;
        Ok(bytes(py, signature))
    }

    /// Encodes the key pair as PKCS#8 DER.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_pkcs8())
    }

    /// Encodes the key pair as SEC1 `ECPrivateKey` DER.
    fn to_sec1<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_sec1())
    }

    /// Returns the private key's big-endian scalar.
    fn to_scalar<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.inner.to_scalar())
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<SigningAlgorithm>()?;
    m.add_class::<VerificationAlgorithm>()?;
    m.add_class::<PublicKey>()?;
    m.add_class::<KeyPair>()?;
    submodule(m, "pyrind.ecdsa.sign", |m| {
        constants!(m, SigningAlgorithm, "pyrind.ecdsa.sign", {
            P256_SHA256_ASN1 => &ecdsa::sign::P256_SHA256_ASN1,
            P256_SHA256_FIXED => &ecdsa::sign::P256_SHA256_FIXED,
            P384_SHA384_ASN1 => &ecdsa::sign::P384_SHA384_ASN1,
            P384_SHA384_FIXED => &ecdsa::sign::P384_SHA384_FIXED,
            P521_SHA512_ASN1 => &ecdsa::sign::P521_SHA512_ASN1,
            P521_SHA512_FIXED => &ecdsa::sign::P521_SHA512_FIXED,
        });
        Ok(())
    })?;
    submodule(m, "pyrind.ecdsa.verify", |m| {
        constants!(m, VerificationAlgorithm, "pyrind.ecdsa.verify", {
            P256_SHA256_ASN1 => &ecdsa::verify::P256_SHA256_ASN1,
            P256_SHA256_FIXED => &ecdsa::verify::P256_SHA256_FIXED,
            P256_SHA384_ASN1 => &ecdsa::verify::P256_SHA384_ASN1,
            P256_SHA512_ASN1 => &ecdsa::verify::P256_SHA512_ASN1,
            P384_SHA256_ASN1 => &ecdsa::verify::P384_SHA256_ASN1,
            P384_SHA384_ASN1 => &ecdsa::verify::P384_SHA384_ASN1,
            P384_SHA384_FIXED => &ecdsa::verify::P384_SHA384_FIXED,
            P384_SHA512_ASN1 => &ecdsa::verify::P384_SHA512_ASN1,
            P521_SHA256_ASN1 => &ecdsa::verify::P521_SHA256_ASN1,
            P521_SHA384_ASN1 => &ecdsa::verify::P521_SHA384_ASN1,
            P521_SHA512_ASN1 => &ecdsa::verify::P521_SHA512_ASN1,
            P521_SHA512_FIXED => &ecdsa::verify::P521_SHA512_FIXED,
        });
        Ok(())
    })
}
