use alloc::boxed::Box;
use alloc::format;
use alloc::string::ToString;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;

use rind::ecdsa::{KeyPair as EcdsaKeyPair, SigningAlgorithm as EcdsaSigningAlgorithm};
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::rsa::{KeyPair as RsaKeyPair, SigningAlgorithm as RsaSigningAlgorithm};
use rind::{ecdsa, rsa};
use rustls::SignatureScheme;
use rustls::pki_types::{PrivateKeyDer, PrivatePkcs8KeyDer, SubjectPublicKeyInfoDer};
use rustls::sign::{self, SigningKey};

/// Parses `der` as any supported key encoding and type, returning the first
/// that works.
pub fn any_supported_type(der: &PrivateKeyDer<'_>) -> Result<Arc<dyn SigningKey>, rustls::Error> {
    match der {
        PrivateKeyDer::Pkcs8(pkcs8) => match load_pkcs8(der, pkcs8)? {
            rind::KeyPair::Ed25519(key) => Ok(Arc::new(Ed25519(Arc::new(key)))),
            rind::KeyPair::Rsa(key) => Ok(Arc::new(RsaSigningKey(Arc::new(key)))),
            key => ecdsa_key(der, key, "which rind-rustls does not sign with"),
        },
        PrivateKeyDer::Pkcs1(_) => Ok(Arc::new(RsaSigningKey::new(der)?)),
        PrivateKeyDer::Sec1(_) => any_ecdsa_type(der),
        _ => Err(unsupported(der, "an encoding rind-rustls does not know")),
    }
}

/// Parses `der` as any ECDSA key type, returning the first that works.
///
/// Both SEC1 (PEM section starting with 'BEGIN EC PRIVATE KEY') and PKCS8
/// (PEM section starting with 'BEGIN PRIVATE KEY') encodings are supported.
pub fn any_ecdsa_type(der: &PrivateKeyDer<'_>) -> Result<Arc<dyn SigningKey>, rustls::Error> {
    match der {
        PrivateKeyDer::Pkcs8(pkcs8) => ecdsa_key(der, load_pkcs8(der, pkcs8)?, "not an ECDSA key"),
        PrivateKeyDer::Sec1(sec1) => {
            // SEC1 has no rind call that reads its curve, so this tries each.
            let mut errors = Vec::with_capacity(ECDSA_KEYS.len());
            for keys in ECDSA_KEYS {
                match EcdsaKeyPair::from_sec1(keys.algorithm, sec1.secret_sec1_der()) {
                    Ok(key) => return Ok(Arc::new(Ecdsa::new(key, keys.scheme))),
                    Err(err) => errors.push(format!("as {:?}: {err}", keys.scheme)),
                }
            }
            Err(unsupported(der, &errors.join("; ")))
        }
        _ => Err(unsupported(der, "not an ECDSA key encoding")),
    }
}

/// Parses `der` as any EdDSA key type, returning the first that works.
pub fn any_eddsa_type(der: &PrivatePkcs8KeyDer<'_>) -> Result<Arc<dyn SigningKey>, rustls::Error> {
    match Ed25519KeyPair::from_pkcs8(der.secret_pkcs8_der()) {
        Ok(key) => Ok(Arc::new(Ed25519(Arc::new(key)))),
        Err(err) => Err(rustls::Error::General(format!(
            "unsupported PKCS#8 key: as Ed25519: {err}"
        ))),
    }
}

/// Loads a PKCS#8 key of whichever type its algorithm identifier names.
fn load_pkcs8(
    der: &PrivateKeyDer<'_>,
    pkcs8: &PrivatePkcs8KeyDer<'_>,
) -> Result<rind::KeyPair, rustls::Error> {
    rind::KeyPair::from_pkcs8(pkcs8.secret_pkcs8_der())
        .map_err(|err| unsupported(der, &err.to_string()))
}

/// Wraps an ECDSA key with its curve's one scheme, refusing any other key
/// with `refusal`.
fn ecdsa_key(
    der: &PrivateKeyDer<'_>,
    key: rind::KeyPair,
    refusal: &str,
) -> Result<Arc<dyn SigningKey>, rustls::Error> {
    let (key, keys) = match key {
        rind::KeyPair::EcdsaP256(key) => (key, &ECDSA_P256_KEYS),
        rind::KeyPair::EcdsaP384(key) => (key, &ECDSA_P384_KEYS),
        rind::KeyPair::EcdsaP521(key) => (key, &ECDSA_P521_KEYS),
        key => return Err(unsupported(der, &format!("{key:?}, {refusal}"))),
    };
    Ok(Arc::new(Ecdsa::new(key, keys.scheme)))
}

fn unsupported(der: &PrivateKeyDer<'_>, reason: &str) -> rustls::Error {
    let encoding = match der {
        PrivateKeyDer::Pkcs1(_) => "PKCS#1",
        PrivateKeyDer::Sec1(_) => "SEC1",
        PrivateKeyDer::Pkcs8(_) => "PKCS#8",
        _ => "private",
    };
    rustls::Error::General(format!("unsupported {encoding} key: {reason}"))
}

/// Each curve's one scheme, since TLS 1.3 binds the hash to the curve.
static ECDSA_KEYS: [&EcdsaKeys; 3] = [&ECDSA_P256_KEYS, &ECDSA_P384_KEYS, &ECDSA_P521_KEYS];

static ECDSA_P256_KEYS: EcdsaKeys = EcdsaKeys {
    algorithm: &ecdsa::sign::P256_SHA256_ASN1,
    scheme: SignatureScheme::ECDSA_NISTP256_SHA256,
};

static ECDSA_P384_KEYS: EcdsaKeys = EcdsaKeys {
    algorithm: &ecdsa::sign::P384_SHA384_ASN1,
    scheme: SignatureScheme::ECDSA_NISTP384_SHA384,
};

static ECDSA_P521_KEYS: EcdsaKeys = EcdsaKeys {
    algorithm: &ecdsa::sign::P521_SHA512_ASN1,
    scheme: SignatureScheme::ECDSA_NISTP521_SHA512,
};

#[derive(Debug)]
struct EcdsaKeys {
    algorithm: &'static EcdsaSigningAlgorithm,
    scheme: SignatureScheme,
}

/// The RSA schemes in preference order: PSS over PKCS#1, then the longest hash.
/// SHA-1 is absent, so it is never chosen.
const RSA_SCHEMES: [(SignatureScheme, &RsaSigningAlgorithm); 6] = [
    (SignatureScheme::RSA_PSS_SHA512, &rsa::sign::PSS_SHA512),
    (SignatureScheme::RSA_PSS_SHA384, &rsa::sign::PSS_SHA384),
    (SignatureScheme::RSA_PSS_SHA256, &rsa::sign::PSS_SHA256),
    (SignatureScheme::RSA_PKCS1_SHA512, &rsa::sign::PKCS1_SHA512),
    (SignatureScheme::RSA_PKCS1_SHA384, &rsa::sign::PKCS1_SHA384),
    (SignatureScheme::RSA_PKCS1_SHA256, &rsa::sign::PKCS1_SHA256),
];

/// A `SigningKey` for RSA-PKCS1 or RSA-PSS.
///
/// rustls's providers make this `pub` for their test suite, outside their
/// stable API, so this one does too.
#[doc(hidden)]
pub struct RsaSigningKey(Arc<RsaKeyPair>);

impl RsaSigningKey {
    /// Makes a new `RsaSigningKey` from a DER encoding, in either PKCS#1 or
    /// PKCS#8 format.
    pub fn new(der: &PrivateKeyDer<'_>) -> Result<Self, rustls::Error> {
        let key = match der {
            PrivateKeyDer::Pkcs1(pkcs1) => RsaKeyPair::from_pkcs1(pkcs1.secret_pkcs1_der()),
            PrivateKeyDer::Pkcs8(pkcs8) => RsaKeyPair::from_pkcs8(pkcs8.secret_pkcs8_der()),
            _ => return Err(unsupported(der, "not an RSA key encoding")),
        };
        match key {
            Ok(key) => Ok(Self(Arc::new(key))),
            Err(err) => Err(unsupported(der, &format!("as RSA: {err}"))),
        }
    }
}

impl sign::SigningKey for RsaSigningKey {
    fn choose_scheme(
        &self,
        schemes: &[SignatureScheme],
    ) -> Option<Box<dyn sign::Signer + 'static>> {
        let (scheme, padding) = RSA_SCHEMES
            .into_iter()
            .find(|(scheme, _)| schemes.contains(scheme))?;
        Some(Box::new(RsaSigner {
            key: Arc::clone(&self.0),
            scheme,
            padding,
        }))
    }

    fn algorithm(&self) -> rustls::SignatureAlgorithm {
        rustls::SignatureAlgorithm::RSA
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'static>> {
        Some(SubjectPublicKeyInfoDer::from(
            self.0.public_key().to_spki().as_ref().to_vec(),
        ))
    }
}

impl fmt::Debug for RsaSigningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("RsaSigningKey").finish_non_exhaustive()
    }
}

struct RsaSigner {
    key: Arc<RsaKeyPair>,
    scheme: SignatureScheme,
    padding: &'static RsaSigningAlgorithm,
}

impl sign::Signer for RsaSigner {
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, rustls::Error> {
        let sig = self
            .key
            .sign(self.padding, message)
            .map_err(|err| rustls::Error::General(format!("signing failed: {err}")))?;

        Ok(sig.as_ref().to_vec())
    }

    fn scheme(&self) -> SignatureScheme {
        self.scheme
    }
}

impl fmt::Debug for RsaSigner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("RsaSigner").finish_non_exhaustive()
    }
}

/// An ECDSA key, which signs only with its curve's scheme.
#[derive(Clone)]
struct Ecdsa {
    key: Arc<EcdsaKeyPair>,
    scheme: SignatureScheme,
}

impl Ecdsa {
    fn new(key: EcdsaKeyPair, scheme: SignatureScheme) -> Self {
        Self {
            key: Arc::new(key),
            scheme,
        }
    }
}

impl sign::SigningKey for Ecdsa {
    fn choose_scheme(
        &self,
        schemes: &[SignatureScheme],
    ) -> Option<Box<dyn sign::Signer + 'static>> {
        if schemes.contains(&self.scheme) {
            Some(Box::new(self.clone()))
        } else {
            None
        }
    }

    fn algorithm(&self) -> rustls::SignatureAlgorithm {
        rustls::SignatureAlgorithm::ECDSA
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'static>> {
        Some(SubjectPublicKeyInfoDer::from(
            self.key.public_key().to_spki().as_ref().to_vec(),
        ))
    }
}

impl sign::Signer for Ecdsa {
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, rustls::Error> {
        let sig = self
            .key
            .sign(message)
            .map_err(|err| rustls::Error::General(format!("signing failed: {err}")))?;

        Ok(sig.as_ref().to_vec())
    }

    fn scheme(&self) -> SignatureScheme {
        self.scheme
    }
}

impl fmt::Debug for Ecdsa {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Ecdsa")
            .field("scheme", &self.scheme)
            .finish_non_exhaustive()
    }
}

struct Ed25519(Arc<Ed25519KeyPair>);

impl sign::SigningKey for Ed25519 {
    fn choose_scheme(
        &self,
        schemes: &[SignatureScheme],
    ) -> Option<Box<dyn sign::Signer + 'static>> {
        if schemes.contains(&SignatureScheme::ED25519) {
            Some(Box::new(Self(self.0.clone())))
        } else {
            None
        }
    }

    fn algorithm(&self) -> rustls::SignatureAlgorithm {
        rustls::SignatureAlgorithm::ED25519
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'static>> {
        Some(SubjectPublicKeyInfoDer::from(
            self.0.public_key().to_spki().as_ref().to_vec(),
        ))
    }
}

impl sign::Signer for Ed25519 {
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>, rustls::Error> {
        Ok(self.0.sign(message).as_ref().to_vec())
    }

    fn scheme(&self) -> SignatureScheme {
        SignatureScheme::ED25519
    }
}

impl fmt::Debug for Ed25519 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("Ed25519").finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use std::{println, vec};

    use rustls::pki_types;
    use rustls::pki_types::pem::PemObject;
    #[cfg(all(target_arch = "wasm32", target_os = "unknown"))]
    use wasm_bindgen_test::wasm_bindgen_test as test;

    use super::*;

    #[test]
    fn test_load_signing_key() {
        let load = |der: PrivateKeyDer<'_>| any_supported_type(&der);

        // Valid inputs: RSA private keys in PKCS#1 and PKCS#8 DER format
        let rsa2048_pkcs1 = pki_types::PrivateKeyDer::Pkcs1(pki_types::PrivatePkcs1KeyDer::from(
            include_bytes!("../../rind/src/high/rsa/rsa2048.der").to_vec(),
        ));
        assert!(load(rsa2048_pkcs1).is_ok());
        let rsa2048_pkcs8 = pki_types::PrivateKeyDer::Pkcs8(pki_types::PrivatePkcs8KeyDer::from(
            include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der").to_vec(),
        ));
        assert!(load(rsa2048_pkcs8).is_ok());

        // Valid inputs: ECDSA P256, P384, and P521 keys in SEC1 and PKCS#8
        // DER format, each choosing only its curve's scheme.
        for (sec1, pkcs8, scheme) in [
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp256r1.der")[..],
                &include_bytes!("../../rind/src/high/ecdsa/secp256r1.pkcs8.der")[..],
                SignatureScheme::ECDSA_NISTP256_SHA256,
            ),
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp384r1.der")[..],
                &include_bytes!("../../rind/src/high/ecdsa/secp384r1.pkcs8.der")[..],
                SignatureScheme::ECDSA_NISTP384_SHA384,
            ),
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp521r1.der")[..],
                &include_bytes!("../../rind/src/high/ecdsa/secp521r1.pkcs8.der")[..],
                SignatureScheme::ECDSA_NISTP521_SHA512,
            ),
        ] {
            let keys = [
                pki_types::PrivateKeyDer::Sec1(pki_types::PrivateSec1KeyDer::from(sec1.to_vec())),
                pki_types::PrivateKeyDer::Pkcs8(pki_types::PrivatePkcs8KeyDer::from(
                    pkcs8.to_vec(),
                )),
            ];
            for key in keys {
                let key = load(key).unwrap();
                let schemes = [
                    SignatureScheme::ECDSA_NISTP256_SHA256,
                    SignatureScheme::ECDSA_NISTP384_SHA384,
                    SignatureScheme::ECDSA_NISTP521_SHA512,
                ];
                assert_eq!(key.choose_scheme(&schemes).unwrap().scheme(), scheme);
            }
        }

        // Error case: invalid key file
        let invalid_pkcs1 = pki_types::PrivateKeyDer::Pkcs1(pki_types::PrivatePkcs1KeyDer::from(
            [0u8; 1024].to_vec(),
        ));
        assert!(load(invalid_pkcs1).is_err());
        let invalid_pkcs8 = pki_types::PrivateKeyDer::Pkcs8(pki_types::PrivatePkcs8KeyDer::from(
            [0u8; 1024].to_vec(),
        ));
        assert!(load(invalid_pkcs8).is_err());
        let invalid_sec1 = pki_types::PrivateKeyDer::Sec1(pki_types::PrivateSec1KeyDer::from(
            [0u8; 1024].to_vec(),
        ));
        assert!(load(invalid_sec1).is_err());
        let ecdsap256_sec1 = pki_types::PrivateKeyDer::Sec1(pki_types::PrivateSec1KeyDer::from(
            include_bytes!("../../rind/src/high/ecdsa/secp256r1.wrong-version.der").to_vec(),
        ));
        assert!(load(ecdsap256_sec1).is_err());

        // A refused key keeps rind's reason, and a key of another type is
        // named.
        let mut p256 = include_bytes!("../../rind/src/high/ecdsa/secp256r1.pkcs8.der").to_vec();
        *p256.last_mut().unwrap() ^= 1;
        let x25519 = rind::agreement::PrivateKey::generate(&rind::agreement::X25519).unwrap();
        for (pkcs8, reason) in [
            (
                p256,
                "unsupported PKCS#8 key: a key was rejected: mismatched SEC1 public key",
            ),
            (
                x25519.to_pkcs8().as_ref().to_vec(),
                "unsupported PKCS#8 key: a key was rejected: an X25519 key, which cannot sign",
            ),
        ] {
            let err = load(pki_types::PrivateKeyDer::Pkcs8(pkcs8.into())).unwrap_err();
            assert_eq!(err, rustls::Error::General(reason.into()));
        }

        // An ML-DSA-65 key in RFC 9881's seed form, which rind-rustls does
        // not sign with. It builds rind without ML-DSA, so rind refuses the
        // key unless another crate in the build turns ML-DSA on, and then
        // this crate refuses the key rind loads.
        let ml_dsa = [
            &[0x30, 0x34, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09][..],
            &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12],
            &[0x04, 0x22, 0x80, 0x20],
            &[0x42; 32],
        ]
        .concat();
        let err = load(pki_types::PrivateKeyDer::Pkcs8(ml_dsa.into())).unwrap_err();
        assert!(
            [
                "unsupported PKCS#8 key: a key was rejected: a key of an algorithm this build \
                 leaves out, rind's `ml-dsa` feature",
                "unsupported PKCS#8 key: MlDsa65(KeyPair { algorithm: ML-DSA-65, .. }), which \
                 rind-rustls does not sign with",
            ]
            .map(|reason| rustls::Error::General(reason.into()))
            .contains(&err),
            "{err}"
        );
    }

    // Each key type's loader loads its own type in each encoding it comes in,
    // and refuses every other type's key.
    #[test]
    fn test_key_type_loaders() {
        let pkcs8 = |pem: &[u8]| PrivateKeyDer::from_pem_slice(pem).unwrap();
        let sec1 = |der: &[u8]| PrivateKeyDer::Sec1(der.to_vec().into());
        let pkcs1 = |der: &[u8]| PrivateKeyDer::Pkcs1(der.to_vec().into());
        type Loader = fn(&PrivateKeyDer<'_>) -> Result<(), rustls::Error>;
        let types: [(Loader, Vec<PrivateKeyDer<'static>>); 3] = [
            (
                |der| RsaSigningKey::new(der).map(drop),
                vec![
                    pkcs8(include_bytes!("../tests/keys/rsa-2048/end.key")),
                    pkcs1(include_bytes!("../../rind/src/high/rsa/rsa2048.der")),
                ],
            ),
            (
                |der| any_ecdsa_type(der).map(drop),
                vec![
                    pkcs8(include_bytes!("../tests/keys/ecdsa-p256/end.key")),
                    sec1(include_bytes!("../../rind/src/high/ecdsa/secp256r1.der")),
                    pkcs8(include_bytes!("../tests/keys/ecdsa-p384/end.key")),
                    sec1(include_bytes!("../../rind/src/high/ecdsa/secp384r1.der")),
                    pkcs8(include_bytes!("../tests/keys/ecdsa-p521/end.key")),
                    sec1(include_bytes!("../../rind/src/high/ecdsa/secp521r1.der")),
                ],
            ),
            (
                |der| match der {
                    PrivateKeyDer::Pkcs8(der) => any_eddsa_type(der).map(drop),
                    _ => Err(rustls::Error::General("not PKCS#8".into())),
                },
                vec![pkcs8(include_bytes!("../tests/keys/ed25519/end.key"))],
            ),
        ];
        for (i, (load, _)) in types.iter().enumerate() {
            for (j, (_, keys)) in types.iter().enumerate() {
                for key in keys {
                    assert_eq!(load(key).is_ok(), i == j, "{i} {key:?}");
                    assert!(any_supported_type(key).is_ok());
                }
            }
        }
    }

    #[test]
    fn test_rsa_signing_key() {
        let signing_key = Arc::new(
            RsaKeyPair::from_pkcs1(include_bytes!("../../rind/src/high/rsa/rsa2048.der")).unwrap(),
        );
        let rsa = RsaSigningKey(signing_key.clone());
        println!("{:?}", rsa);
        assert_eq!(rsa.algorithm(), rustls::SignatureAlgorithm::RSA);

        // If multiple schemes are specified, choose PSS over PKCS#1 and then longest specified hash length.
        assert!(rsa.choose_scheme(&[]).is_none());
        assert_eq!(
            rsa.choose_scheme(&[SignatureScheme::RSA_PKCS1_SHA256])
                .unwrap()
                .scheme(),
            SignatureScheme::RSA_PKCS1_SHA256
        );
        assert_eq!(
            rsa.choose_scheme(&[
                SignatureScheme::RSA_PKCS1_SHA256,
                SignatureScheme::RSA_PSS_SHA256
            ])
            .unwrap()
            .scheme(),
            SignatureScheme::RSA_PSS_SHA256
        );
        assert_eq!(
            rsa.choose_scheme(&[
                SignatureScheme::RSA_PSS_SHA256,
                SignatureScheme::RSA_PKCS1_SHA384
            ])
            .unwrap()
            .scheme(),
            SignatureScheme::RSA_PSS_SHA256
        );
        assert_eq!(
            rsa.choose_scheme(&[
                SignatureScheme::RSA_PSS_SHA512,
                SignatureScheme::RSA_PSS_SHA256,
                SignatureScheme::RSA_PSS_SHA384
            ])
            .unwrap()
            .scheme(),
            SignatureScheme::RSA_PSS_SHA512
        );
        // Don't choose non-RSA schemes.
        assert!(
            rsa.choose_scheme(&[SignatureScheme::ECDSA_NISTP256_SHA256])
                .is_none()
        );
        assert_eq!(
            rsa.choose_scheme(&[SignatureScheme::ED25519, SignatureScheme::RSA_PSS_SHA384])
                .unwrap()
                .scheme(),
            SignatureScheme::RSA_PSS_SHA384
        );
        assert_eq!(
            rsa.choose_scheme(&[
                SignatureScheme::ECDSA_NISTP521_SHA512,
                SignatureScheme::RSA_PKCS1_SHA384
            ])
            .unwrap()
            .scheme(),
            SignatureScheme::RSA_PKCS1_SHA384
        );
        assert_eq!(
            rsa.choose_scheme(&[SignatureScheme::ED448, SignatureScheme::RSA_PKCS1_SHA512])
                .unwrap()
                .scheme(),
            SignatureScheme::RSA_PKCS1_SHA512
        );
        // Don't choose SHA1.
        assert!(
            rsa.choose_scheme(&[SignatureScheme::RSA_PKCS1_SHA1])
                .is_none()
        );

        // Each chosen scheme signs.
        let message = vec![0u8; 64];
        for (scheme, _) in RSA_SCHEMES {
            let signer = rsa.choose_scheme(&[scheme]).unwrap();
            assert_eq!(signer.sign(&message).unwrap().len(), 256);
            println!("{:?}", signer);
        }
    }

    #[test]
    fn test_ecdsa_signing_key() {
        for (pkcs8, keys) in [
            &include_bytes!("../../rind/src/high/ecdsa/secp256r1.pkcs8.der")[..],
            &include_bytes!("../../rind/src/high/ecdsa/secp384r1.pkcs8.der")[..],
            &include_bytes!("../../rind/src/high/ecdsa/secp521r1.pkcs8.der")[..],
        ]
        .into_iter()
        .zip([&ECDSA_P256_KEYS, &ECDSA_P384_KEYS, &ECDSA_P521_KEYS])
        {
            let EcdsaKeys { algorithm, scheme } = *keys;
            let ecdsa = Ecdsa::new(EcdsaKeyPair::from_pkcs8(algorithm, pkcs8).unwrap(), scheme);
            println!("{:?}", ecdsa);
            assert_eq!(ecdsa.algorithm(), rustls::SignatureAlgorithm::ECDSA);

            // Choose only a matching scheme.
            assert!(ecdsa.choose_scheme(&[]).is_none());
            let others = [
                SignatureScheme::ECDSA_SHA1_Legacy,
                SignatureScheme::RSA_PKCS1_SHA256,
                SignatureScheme::RSA_PKCS1_SHA384,
                SignatureScheme::ECDSA_NISTP256_SHA256,
                SignatureScheme::ECDSA_NISTP384_SHA384,
                SignatureScheme::RSA_PKCS1_SHA512,
                SignatureScheme::ECDSA_NISTP521_SHA512,
                SignatureScheme::RSA_PSS_SHA256,
                SignatureScheme::RSA_PSS_SHA384,
                SignatureScheme::RSA_PSS_SHA512,
                SignatureScheme::ED25519,
                SignatureScheme::ED448,
                SignatureScheme::ML_DSA_44,
                SignatureScheme::ML_DSA_65,
                SignatureScheme::ML_DSA_87,
            ]
            .into_iter()
            .filter(|other| *other != scheme)
            .collect::<Vec<_>>();
            assert!(ecdsa.choose_scheme(&others).is_none());
            assert_eq!(
                ecdsa
                    .choose_scheme(&[
                        SignatureScheme::RSA_PSS_SHA256,
                        scheme,
                        SignatureScheme::ED25519
                    ])
                    .unwrap()
                    .scheme(),
                scheme
            );

            // TLS carries ECDSA signatures ASN.1-encoded.
            let signer = ecdsa.choose_scheme(&[scheme]).unwrap();
            assert!(signer.sign(b"hello").unwrap().starts_with(&[0x30]));
        }
    }

    #[test]
    fn test_ed25519_signing_key() {
        let signing_key = Arc::new(Ed25519KeyPair::generate().unwrap());
        let ed25519 = Ed25519(signing_key.clone());
        assert_eq!(ed25519.algorithm(), rustls::SignatureAlgorithm::ED25519);
        assert!(ed25519.choose_scheme(&[]).is_none());
        assert_eq!(format!("{ed25519:?}"), "Ed25519 { .. }");
    }
}
