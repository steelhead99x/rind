// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::{ecdsa, ed25519, rsa};

use crate::rsa::KeySize;
use crate::{Bytes, Secret, algorithm, bytes, constants, error, submodule};

algorithm!(
    /// An algorithm an `EcdsaKeyPair` signs with.
    EcdsaSigningAlgorithm(ecdsa::SigningAlgorithm) as "pyrind.signature"."EcdsaSigningAlgorithm" {}
);

algorithm!(
    /// An algorithm an `RsaKeyPair` signs with.
    RsaSigningAlgorithm(RsaSigning) as "pyrind.signature"."RsaSigningAlgorithm" {}
);

algorithm!(
    /// An algorithm a `PublicKey` verifies with.
    VerificationAlgorithm(Verification) as "pyrind.signature"."VerificationAlgorithm" {}
);

algorithm!(
    /// An RSA algorithm a `PublicKey` verifies with, which also loads a key
    /// from its components.
    RsaVerificationAlgorithm(rsa::VerificationAlgorithm) as "pyrind.signature"."RsaVerificationAlgorithm" {}
);

/// rind's algorithm a non-RSA `VerificationAlgorithm` stands for, in its
/// module.
pub(crate) enum Verification {
    Ecdsa(&'static ecdsa::VerificationAlgorithm),
    Ed25519,
}

/// An RSA signing algorithm and the one that verifies what it signs.
pub(crate) struct RsaSigning {
    sign: &'static rsa::SigningAlgorithm,
    verify: &'static rsa::VerificationAlgorithm,
}

/// Either kind of verification algorithm.
#[derive(FromPyObject)]
enum AnyVerificationAlgorithm<'py> {
    Plain(Bound<'py, VerificationAlgorithm>),
    Rsa(Bound<'py, RsaVerificationAlgorithm>),
}

impl AnyVerificationAlgorithm<'_> {
    /// Parses a public key with `ecdsa`, `ed25519`, or `rsa`, as the
    /// algorithm's module names it.
    fn parse(
        &self,
        ecdsa: impl FnOnce(
            &'static ecdsa::VerificationAlgorithm,
        ) -> Result<ecdsa::PublicKey, rind::Error>,
        ed25519: impl FnOnce() -> Result<ed25519::PublicKey, rind::Error>,
        rsa: impl FnOnce() -> Result<rsa::PublicKey, rind::Error>,
    ) -> PyResult<PublicKey> {
        let key = match self {
            Self::Plain(algorithm) => match algorithm.get().inner {
                Verification::Ecdsa(algorithm) => ecdsa(algorithm).map(Key::Ecdsa),
                Verification::Ed25519 => ed25519().map(Key::Ed25519),
            },
            Self::Rsa(algorithm) => rsa().and_then(|key| rsa_key(key, algorithm.get().inner)),
        };
        key.map(Box::new).map(PublicKey).map_err(error)
    }
}

/// Binds an RSA key to `algorithm`, refusing it at load, as pyrind always
/// has, if its modulus is below the algorithm's floor.
///
/// rind's `rsa::PublicKey::verify` checks the floor before it reads the
/// signature, and refuses an empty signature by its length alone, so the only
/// key it refuses here is one below the floor.
fn rsa_key(
    key: rsa::PublicKey,
    algorithm: &'static rsa::VerificationAlgorithm,
) -> Result<Key, rind::Error> {
    match key.verify(algorithm, &[], &[]) {
        Err(error @ rind::Error::KeyRejected(_)) => Err(error),
        _ => Ok(Key::Rsa(key, algorithm)),
    }
}

/// A public key and, for RSA, the algorithm it verifies with.
#[allow(clippy::large_enum_variant)]
enum Key {
    Ecdsa(ecdsa::PublicKey),
    Ed25519(ed25519::PublicKey),
    Rsa(rsa::PublicKey, &'static rsa::VerificationAlgorithm),
}

/// A public key that verifies signatures for one algorithm, whose `bytes`
/// are its encoding: an uncompressed SEC1 point for ECDSA, 32 bytes for
/// Ed25519, and a PKCS#1 `RSAPublicKey` for RSA.
///
/// An RSA key with a modulus below the algorithm's floor raises
/// `KeyRejected` as it loads.
#[pyclass(frozen, module = "pyrind.signature")]
struct PublicKey(Box<Key>);

#[pymethods]
impl PublicKey {
    /// Parses a public key for `algorithm` from its `bytes` encoding.
    #[new]
    fn new(algorithm: AnyVerificationAlgorithm<'_>, data: Bytes<'_>) -> PyResult<Self> {
        algorithm.parse(
            |ecdsa| ecdsa::PublicKey::new(ecdsa, &data),
            || ed25519::PublicKey::new(&data),
            // PKCS#1 or SPKI, as the old shared loader took either.
            || rsa::PublicKey::new(&data).or_else(|_| rsa::PublicKey::from_spki(&data)),
        )
    }

    /// Parses a public key for `algorithm` from `SubjectPublicKeyInfo` DER,
    /// refusing one that names another algorithm or curve.
    #[staticmethod]
    fn from_spki(algorithm: AnyVerificationAlgorithm<'_>, der: Bytes<'_>) -> PyResult<Self> {
        algorithm.parse(
            |ecdsa| ecdsa::PublicKey::from_spki(ecdsa, &der),
            || ed25519::PublicKey::from_spki(&der),
            || rsa::PublicKey::from_spki(&der),
        )
    }

    /// Loads an RSA key for `algorithm` from its big-endian modulus `n` and
    /// exponent `e`, as a JWK carries them.
    #[staticmethod]
    fn from_components(
        algorithm: &Bound<'_, RsaVerificationAlgorithm>,
        n: Bytes<'_>,
        e: Bytes<'_>,
    ) -> PyResult<Self> {
        let components = rsa::PublicKeyComponents { n: &*n, e: &*e };
        rsa::PublicKey::from_components(&components)
            .and_then(|key| rsa_key(key, algorithm.get().inner))
            .map(|key| Self(Box::new(key)))
            .map_err(error)
    }

    /// Checks `signature` over `message`; raises `BadSignature` if it does
    /// not verify.
    fn verify(&self, message: Bytes<'_>, signature: Bytes<'_>) -> PyResult<()> {
        match &*self.0 {
            Key::Ecdsa(key) => key.verify(&message, &signature),
            Key::Ed25519(key) => key.verify(&message, &signature),
            Key::Rsa(key, algorithm) => key.verify(algorithm, &message, &signature),
        }
        .map_err(error)
    }

    /// Encodes the key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        let spki = match &*self.0 {
            Key::Ecdsa(key) => key.to_spki(),
            Key::Ed25519(key) => key.to_spki(),
            Key::Rsa(key, _) => key.to_spki(),
        };
        bytes(py, spki)
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        let encoding: &[u8] = match &*self.0 {
            Key::Ecdsa(key) => key.as_ref(),
            Key::Ed25519(key) => key.as_ref(),
            Key::Rsa(key, _) => key.as_ref(),
        };
        bytes(py, encoding)
    }
}

/// An ECDSA key pair, which signs with one algorithm.
#[pyclass(frozen, module = "pyrind.signature")]
struct EcdsaKeyPair(Box<ecdsa::KeyPair>);

#[pymethods]
impl EcdsaKeyPair {
    /// Generates a key pair for `algorithm`.
    #[staticmethod]
    fn generate(algorithm: &Bound<'_, EcdsaSigningAlgorithm>) -> PyResult<Self> {
        ecdsa::KeyPair::generate(algorithm.get().inner)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a key pair for `algorithm` from PKCS#8 DER.
    #[staticmethod]
    fn from_pkcs8(algorithm: &Bound<'_, EcdsaSigningAlgorithm>, der: Secret<'_>) -> PyResult<Self> {
        ecdsa::KeyPair::from_pkcs8(algorithm.get().inner, &der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a key pair for `algorithm` from SEC1 `ECPrivateKey` DER.
    #[staticmethod]
    fn from_sec1(algorithm: &Bound<'_, EcdsaSigningAlgorithm>, der: Secret<'_>) -> PyResult<Self> {
        ecdsa::KeyPair::from_sec1(algorithm.get().inner, &der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a key pair for `algorithm` from its big-endian scalar and its
    /// uncompressed public key, as a JWK's `d`, `x`, and `y` carry them,
    /// refused unless they match.
    #[staticmethod]
    fn from_scalar_and_public_key(
        algorithm: &Bound<'_, EcdsaSigningAlgorithm>,
        scalar: Secret<'_>,
        public_key: Bytes<'_>,
    ) -> PyResult<Self> {
        ecdsa::KeyPair::from_scalar_and_public_key(algorithm.get().inner, &scalar, &public_key)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// The public key, which verifies with the verification algorithm of the
    /// same name.
    fn public_key(&self) -> PublicKey {
        PublicKey(Box::new(Key::Ecdsa(self.0.public_key().clone())))
    }

    /// Signs `message`.
    fn sign<'py>(&self, py: Python<'py>, message: Bytes<'_>) -> PyResult<Bound<'py, PyBytes>> {
        let signature = self.0.sign(&message).map_err(error)?;
        Ok(bytes(py, signature))
    }

    /// Encodes the key pair as PKCS#8 DER.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_pkcs8())
    }

    /// Encodes the key pair as SEC1 `ECPrivateKey` DER.
    fn to_sec1<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_sec1())
    }

    /// Returns the private key's big-endian scalar.
    fn to_scalar<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_scalar())
    }

    /// Encodes the public key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.public_key().to_spki())
    }
}

/// An Ed25519 key pair.
#[pyclass(frozen, module = "pyrind.signature")]
struct Ed25519KeyPair(Box<ed25519::KeyPair>);

#[pymethods]
impl Ed25519KeyPair {
    /// Generates a key pair.
    #[staticmethod]
    fn generate() -> PyResult<Self> {
        ed25519::KeyPair::generate()
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a key pair from PKCS#8 v1 or v2 DER, refused if a v2 key's
    /// public key does not match.
    #[staticmethod]
    fn from_pkcs8(der: Secret<'_>) -> PyResult<Self> {
        ed25519::KeyPair::from_pkcs8(&der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public
    /// key.
    #[staticmethod]
    fn from_seed(seed: Secret<'_>) -> PyResult<Self> {
        ed25519::KeyPair::from_seed(&seed)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a 32-byte seed, refused unless `public_key` is its public key.
    #[staticmethod]
    fn from_seed_and_public_key(seed: Secret<'_>, public_key: Bytes<'_>) -> PyResult<Self> {
        ed25519::KeyPair::from_seed_and_public_key(&seed, &public_key)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// The public key, which verifies with `verify.ED25519`.
    fn public_key(&self) -> PublicKey {
        PublicKey(Box::new(Key::Ed25519(self.0.public_key().clone())))
    }

    /// Signs `message`.
    fn sign<'py>(&self, py: Python<'py>, message: Bytes<'_>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.sign(&message))
    }

    /// Encodes the key pair as PKCS#8 v2 DER (RFC 5958), with its public key.
    fn to_pkcs8<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_pkcs8())
    }

    /// Encodes the private key as PKCS#8 v1 DER (RFC 8410), as OpenSSL
    /// writes it.
    fn to_pkcs8v1<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_pkcs8v1())
    }

    /// Returns the private key's 32-byte seed.
    fn to_seed<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.to_seed())
    }

    /// Encodes the public key as `SubjectPublicKeyInfo` DER.
    fn to_spki<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, self.0.public_key().to_spki())
    }
}

/// An RSA key pair, which signs with any RSA signing algorithm.
#[pyclass(frozen, module = "pyrind.signature")]
struct RsaKeyPair(Box<rsa::KeyPair>);

#[pymethods]
impl RsaKeyPair {
    /// Generates a key pair of `size`, releasing the GIL: about 30
    /// milliseconds for 2048 bits, and seconds for the largest sizes.
    #[staticmethod]
    fn generate(py: Python<'_>, size: KeySize) -> PyResult<Self> {
        py.detach(|| rsa::KeyPair::generate(size.into()))
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a PKCS#8 RSA private key.
    #[staticmethod]
    fn from_pkcs8(der: Secret<'_>) -> PyResult<Self> {
        rsa::KeyPair::from_pkcs8(&der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    #[staticmethod]
    fn from_pkcs1(der: Secret<'_>) -> PyResult<Self> {
        rsa::KeyPair::from_pkcs1(&der)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// The public key, which verifies what this key pair signs with
    /// `algorithm`.
    fn public_key(&self, algorithm: &Bound<'_, RsaSigningAlgorithm>) -> PublicKey {
        let key = self.0.public_key().clone();
        PublicKey(Box::new(Key::Rsa(key, algorithm.get().inner.verify)))
    }

    /// Signs `message` with `algorithm`, releasing the GIL.
    fn sign<'py>(
        &self,
        py: Python<'py>,
        algorithm: &Bound<'_, RsaSigningAlgorithm>,
        message: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let algorithm = algorithm.get().inner.sign;
        let signature = py
            .detach(|| self.0.sign(algorithm, &message))
            .map_err(error)?;
        Ok(bytes(py, signature))
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

/// The non-RSA verification algorithms, which the `verify` module's
/// constants point at.
mod verification {
    use rind::ecdsa::verify;

    use super::Verification;

    macro_rules! ecdsa {
        ($($name:ident),* $(,)?) => {
            $(pub(super) static $name: Verification = Verification::Ecdsa(&verify::$name);)*
        };
    }

    ecdsa!(
        P256_SHA256_ASN1,
        P256_SHA256_FIXED,
        P256_SHA384_ASN1,
        P256_SHA512_ASN1,
        P384_SHA256_ASN1,
        P384_SHA384_ASN1,
        P384_SHA384_FIXED,
        P384_SHA512_ASN1,
        P521_SHA256_ASN1,
        P521_SHA384_ASN1,
        P521_SHA512_ASN1,
        P521_SHA512_FIXED,
    );

    pub(super) static ED25519: Verification = Verification::Ed25519;
}

/// The RSA signing algorithms, which the `sign` module's constants point at.
mod rsa_signing {
    use rind::rsa::{sign, verify};

    use super::RsaSigning;

    macro_rules! rsa {
        ($($name:ident),* $(,)?) => {
            $(pub(super) static $name: RsaSigning = RsaSigning {
                sign: &sign::$name,
                verify: &verify::$name,
            };)*
        };
    }

    rsa!(
        PKCS1_SHA256,
        PKCS1_SHA384,
        PKCS1_SHA512,
        PSS_SHA256,
        PSS_SHA384,
        PSS_SHA512,
    );
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<EcdsaSigningAlgorithm>()?;
    m.add_class::<RsaSigningAlgorithm>()?;
    m.add_class::<VerificationAlgorithm>()?;
    m.add_class::<RsaVerificationAlgorithm>()?;
    m.add_class::<PublicKey>()?;
    m.add_class::<EcdsaKeyPair>()?;
    m.add_class::<Ed25519KeyPair>()?;
    m.add_class::<RsaKeyPair>()?;
    submodule(m, "pyrind.signature.sign", |m| {
        constants!(m, EcdsaSigningAlgorithm, "pyrind.signature.sign", {
            ECDSA_P256_SHA256_ASN1 => &ecdsa::sign::P256_SHA256_ASN1,
            ECDSA_P256_SHA256_FIXED => &ecdsa::sign::P256_SHA256_FIXED,
            ECDSA_P384_SHA384_ASN1 => &ecdsa::sign::P384_SHA384_ASN1,
            ECDSA_P384_SHA384_FIXED => &ecdsa::sign::P384_SHA384_FIXED,
            ECDSA_P521_SHA512_ASN1 => &ecdsa::sign::P521_SHA512_ASN1,
            ECDSA_P521_SHA512_FIXED => &ecdsa::sign::P521_SHA512_FIXED,
        });
        constants!(m, RsaSigningAlgorithm, "pyrind.signature.sign", {
            RSA_PKCS1_SHA256 => &rsa_signing::PKCS1_SHA256,
            RSA_PKCS1_SHA384 => &rsa_signing::PKCS1_SHA384,
            RSA_PKCS1_SHA512 => &rsa_signing::PKCS1_SHA512,
            RSA_PSS_SHA256 => &rsa_signing::PSS_SHA256,
            RSA_PSS_SHA384 => &rsa_signing::PSS_SHA384,
            RSA_PSS_SHA512 => &rsa_signing::PSS_SHA512,
        });
        Ok(())
    })?;
    submodule(m, "pyrind.signature.verify", |m| {
        constants!(m, VerificationAlgorithm, "pyrind.signature.verify", {
            ECDSA_P256_SHA256_ASN1 => &verification::P256_SHA256_ASN1,
            ECDSA_P256_SHA256_FIXED => &verification::P256_SHA256_FIXED,
            ECDSA_P256_SHA384_ASN1 => &verification::P256_SHA384_ASN1,
            ECDSA_P256_SHA512_ASN1 => &verification::P256_SHA512_ASN1,
            ECDSA_P384_SHA256_ASN1 => &verification::P384_SHA256_ASN1,
            ECDSA_P384_SHA384_ASN1 => &verification::P384_SHA384_ASN1,
            ECDSA_P384_SHA384_FIXED => &verification::P384_SHA384_FIXED,
            ECDSA_P384_SHA512_ASN1 => &verification::P384_SHA512_ASN1,
            ECDSA_P521_SHA256_ASN1 => &verification::P521_SHA256_ASN1,
            ECDSA_P521_SHA384_ASN1 => &verification::P521_SHA384_ASN1,
            ECDSA_P521_SHA512_ASN1 => &verification::P521_SHA512_ASN1,
            ECDSA_P521_SHA512_FIXED => &verification::P521_SHA512_FIXED,
            ED25519 => &verification::ED25519,
        });
        constants!(m, RsaVerificationAlgorithm, "pyrind.signature.verify", {
            RSA_PKCS1_SHA256 => &rsa::verify::PKCS1_SHA256,
            RSA_PKCS1_SHA384 => &rsa::verify::PKCS1_SHA384,
            RSA_PKCS1_SHA512 => &rsa::verify::PKCS1_SHA512,
            RSA_PSS_SHA256 => &rsa::verify::PSS_SHA256,
            RSA_PSS_SHA256_ANY_SALT => &rsa::verify::PSS_SHA256_ANY_SALT,
            RSA_PSS_SHA384 => &rsa::verify::PSS_SHA384,
            RSA_PSS_SHA384_ANY_SALT => &rsa::verify::PSS_SHA384_ANY_SALT,
            RSA_PSS_SHA512 => &rsa::verify::PSS_SHA512,
            RSA_PSS_SHA512_ANY_SALT => &rsa::verify::PSS_SHA512_ANY_SALT,
        });
        submodule(m, "pyrind.signature.verify.legacy", |legacy| {
            constants!(legacy, RsaVerificationAlgorithm, "pyrind.signature.verify.legacy", {
                RSA_PKCS1_1024_SHA1 => &rsa::verify::legacy::PKCS1_1024_SHA1,
                RSA_PKCS1_1024_SHA256 => &rsa::verify::legacy::PKCS1_1024_SHA256,
                RSA_PKCS1_1024_SHA512 => &rsa::verify::legacy::PKCS1_1024_SHA512,
                RSA_PKCS1_3072_SHA384 => &rsa::verify::legacy::PKCS1_3072_SHA384,
                RSA_PKCS1_SHA1 => &rsa::verify::legacy::PKCS1_SHA1,
            });
            Ok(())
        })
    })
}
