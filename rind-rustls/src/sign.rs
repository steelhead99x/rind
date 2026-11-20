use core::fmt;
use std::sync::Arc;

use rind::ecdsa::{KeyPair as EcdsaKeyPair, SigningAlgorithm as EcdsaSigningAlgorithm};
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::ml_dsa::{KeyPair as MlDsaKeyPair, ParameterSet};
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
            // Each ML-DSA parameter set's one scheme, which only a PKCS#8 key
            // (RFC 9881) comes in. Like aws-lc-rs's provider, only
            // `any_supported_type` loads them.
            rind::KeyPair::MlDsa44(key) => Ok(ml_dsa(key, SignatureScheme::ML_DSA_44)),
            rind::KeyPair::MlDsa65(key) => Ok(ml_dsa(key, SignatureScheme::ML_DSA_65)),
            rind::KeyPair::MlDsa87(key) => Ok(ml_dsa(key, SignatureScheme::ML_DSA_87)),
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

/// Wraps an ML-DSA key with its parameter set's one scheme.
fn ml_dsa<P: ParameterSet>(key: MlDsaKeyPair<P>, scheme: SignatureScheme) -> Arc<dyn SigningKey> {
    Arc::new(MlDsa {
        key: Arc::new(key),
        scheme,
    })
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

/// An ML-DSA key, which signs only with its parameter set's scheme.
struct MlDsa<P: ParameterSet> {
    key: Arc<MlDsaKeyPair<P>>,
    scheme: SignatureScheme,
}

impl<P: ParameterSet> sign::SigningKey for MlDsa<P> {
    fn choose_scheme(
        &self,
        schemes: &[SignatureScheme],
    ) -> Option<Box<dyn sign::Signer + 'static>> {
        if schemes.contains(&self.scheme) {
            Some(Box::new(Self {
                key: Arc::clone(&self.key),
                scheme: self.scheme,
            }))
        } else {
            None
        }
    }

    // As aws-lc-rs's provider answers: TLS has no `SignatureAlgorithm` for ML-DSA.
    fn algorithm(&self) -> rustls::SignatureAlgorithm {
        rustls::SignatureAlgorithm::Unknown(0)
    }

    fn public_key(&self) -> Option<SubjectPublicKeyInfoDer<'static>> {
        Some(SubjectPublicKeyInfoDer::from(
            self.key.public_key().to_spki().as_ref().to_vec(),
        ))
    }
}

impl<P: ParameterSet> sign::Signer for MlDsa<P> {
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

impl<P: ParameterSet> fmt::Debug for MlDsa<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("MlDsa")
            .field("scheme", &self.scheme)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use rind::ml_dsa::{MlDsa44, MlDsa65, MlDsa87};
    use rustls::pki_types;
    use rustls::pki_types::pem::PemObject;

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
        let slh_dsa = rind::slh_dsa::KeyPair::<rind::slh_dsa::SlhDsaSha2_128s>::generate().unwrap();
        for (pkcs8, reason) in [
            (
                p256,
                "unsupported PKCS#8 key: a key was rejected: mismatched SEC1 public key",
            ),
            (
                x25519.to_pkcs8().as_ref().to_vec(),
                "unsupported PKCS#8 key: a key was rejected: an X25519 key, which cannot sign",
            ),
            (
                slh_dsa.to_pkcs8().as_ref().to_vec(),
                "unsupported PKCS#8 key: SlhDsaSha2_128s(KeyPair { algorithm: SLH-DSA-SHA2-128s, .. }), \
                 which rind-rustls does not sign with",
            ),
        ] {
            let err = load(pki_types::PrivateKeyDer::Pkcs8(pkcs8.into())).unwrap_err();
            assert_eq!(err, rustls::Error::General(reason.into()));
        }
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

    /// Each ML-DSA parameter set's scheme, public key and signature lengths,
    /// and its `tests/keys/ml-dsa-*` files. pyca/cryptography 50.0.1 over
    /// OpenSSL 4.0.2 made those keys and certificates.
    fn ml_dsa_test_keys() -> [(SignatureScheme, usize, usize, PrivateKeyDer<'static>); 3] {
        let pem = |pem: &[u8]| PrivateKeyDer::from_pem_slice(pem).unwrap();
        [
            (
                SignatureScheme::ML_DSA_44,
                1312,
                2420,
                pem(include_bytes!("../tests/keys/ml-dsa-44/end.key")),
            ),
            (
                SignatureScheme::ML_DSA_65,
                1952,
                3309,
                pem(include_bytes!("../tests/keys/ml-dsa-65/end.key")),
            ),
            (
                SignatureScheme::ML_DSA_87,
                2592,
                4627,
                pem(include_bytes!("../tests/keys/ml-dsa-87/end.key")),
            ),
        ]
    }

    // Every scheme TLS names, which a key chooses only if it is its own.
    const ALL_SCHEMES: [SignatureScheme; 15] = [
        SignatureScheme::RSA_PKCS1_SHA1,
        SignatureScheme::ECDSA_SHA1_Legacy,
        SignatureScheme::RSA_PKCS1_SHA256,
        SignatureScheme::ECDSA_NISTP256_SHA256,
        SignatureScheme::RSA_PKCS1_SHA384,
        SignatureScheme::ECDSA_NISTP384_SHA384,
        SignatureScheme::RSA_PKCS1_SHA512,
        SignatureScheme::ECDSA_NISTP521_SHA512,
        SignatureScheme::RSA_PSS_SHA256,
        SignatureScheme::RSA_PSS_SHA384,
        SignatureScheme::RSA_PSS_SHA512,
        SignatureScheme::ED25519,
        SignatureScheme::ML_DSA_44,
        SignatureScheme::ML_DSA_65,
        SignatureScheme::ML_DSA_87,
    ];

    #[test]
    fn test_ml_dsa_signing_key() {
        fn check<P: ParameterSet>(
            scheme: SignatureScheme,
            signature_len: usize,
            der: &PrivateKeyDer<'_>,
            pair: &MlDsaKeyPair<P>,
        ) {
            let key = any_supported_type(der).unwrap();
            assert_eq!(
                format!("{key:?}"),
                format!("MlDsa {{ scheme: {scheme:?}, .. }}")
            );
            assert_eq!(key.algorithm(), rustls::SignatureAlgorithm::Unknown(0));
            assert_eq!(
                key.public_key().unwrap().as_ref(),
                pair.public_key().to_spki().as_ref()
            );

            // Choose only its own scheme.
            assert!(key.choose_scheme(&[]).is_none());
            let others = ALL_SCHEMES
                .into_iter()
                .filter(|other| *other != scheme)
                .collect::<Vec<_>>();
            assert!(key.choose_scheme(&others).is_none());
            for offered in [
                &[scheme][..],
                &[
                    SignatureScheme::RSA_PSS_SHA256,
                    scheme,
                    SignatureScheme::ED25519,
                ],
                &ALL_SCHEMES,
            ] {
                let signer = key.choose_scheme(offered).unwrap();
                assert_eq!(signer.scheme(), scheme);
                assert_eq!(
                    format!("{signer:?}"),
                    format!("MlDsa {{ scheme: {scheme:?}, .. }}")
                );

                // The signature is the parameter set's size, and its key
                // verifies it.
                let signature = signer.sign(b"hello").unwrap();
                assert_eq!(signature.len(), signature_len);
                pair.public_key().verify(b"hello", &signature).unwrap();
                assert!(pair.public_key().verify(b"hullo", &signature).is_err());
            }
        }

        for (scheme, _, signature_len, der) in ml_dsa_test_keys() {
            let PrivateKeyDer::Pkcs8(pkcs8) = &der else {
                unreachable!("a PKCS#8 PEM")
            };
            let pkcs8 = pkcs8.secret_pkcs8_der();
            match scheme {
                SignatureScheme::ML_DSA_44 => check(
                    scheme,
                    signature_len,
                    &der,
                    &MlDsaKeyPair::<MlDsa44>::from_pkcs8(pkcs8).unwrap(),
                ),
                SignatureScheme::ML_DSA_65 => check(
                    scheme,
                    signature_len,
                    &der,
                    &MlDsaKeyPair::<MlDsa65>::from_pkcs8(pkcs8).unwrap(),
                ),
                _ => check(
                    scheme,
                    signature_len,
                    &der,
                    &MlDsaKeyPair::<MlDsa87>::from_pkcs8(pkcs8).unwrap(),
                ),
            }
        }

        // A key rind made loads too.
        let pair = MlDsaKeyPair::<MlDsa65>::generate().unwrap();
        let der = PrivateKeyDer::Pkcs8(pair.to_pkcs8().as_ref().to_vec().into());
        check(SignatureScheme::ML_DSA_65, 3309, &der, &pair);
    }

    // Like aws-lc-rs's provider, only `any_supported_type` loads an ML-DSA
    // key, and only from PKCS#8.
    #[test]
    fn test_ml_dsa_key_loading() {
        for (_, _, _, der) in ml_dsa_test_keys() {
            let PrivateKeyDer::Pkcs8(pkcs8) = &der else {
                unreachable!("a PKCS#8 PEM")
            };
            assert!(any_supported_type(&der).is_ok());
            assert!(any_ecdsa_type(&der).is_err());
            assert!(any_eddsa_type(pkcs8).is_err());
            assert!(RsaSigningKey::new(&der).is_err());

            // No other encoding carries one.
            let bytes = pkcs8.secret_pkcs8_der().to_vec();
            for other in [
                PrivateKeyDer::Pkcs1(bytes.clone().into()),
                PrivateKeyDer::Sec1(bytes.clone().into()),
            ] {
                assert!(any_supported_type(&other).is_err());
            }

            // A refused key keeps rind's reason.
            let mut truncated = bytes.clone();
            truncated.pop();
            let err = any_supported_type(&PrivateKeyDer::Pkcs8(truncated.into())).unwrap_err();
            let err = err.to_string();
            assert!(err.contains("unsupported PKCS#8 key: "), "{err}");
        }
    }

    // Each key loads, names its scheme, signs, and verifies as aws-lc-rs's
    // provider's does, with its signatures and by its public key.
    // aws-lc-rs does not build for wasm.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn test_ml_dsa_signing_key_matches_aws_lc_rs() {
        use rustls::crypto::aws_lc_rs;

        let provider = aws_lc_rs::default_provider();
        let theirs_verify = |scheme| {
            let (_, algorithms) = provider
                .signature_verification_algorithms
                .mapping
                .iter()
                .find(|(theirs, _)| *theirs == scheme)
                .unwrap();
            algorithms[0]
        };
        let ours_verify = |scheme| {
            let (_, algorithms) = crate::SUPPORTED_SIG_ALGS
                .mapping
                .iter()
                .find(|(ours, _)| *ours == scheme)
                .unwrap();
            algorithms[0]
        };

        for (scheme, key_len, signature_len, der) in ml_dsa_test_keys() {
            let ours = any_supported_type(&der).unwrap();
            let theirs = aws_lc_rs::sign::any_supported_type(&der).unwrap();
            assert_eq!(ours.algorithm(), theirs.algorithm());
            let (ours_spki, theirs_spki) =
                (ours.public_key().unwrap(), theirs.public_key().unwrap());
            assert_eq!(ours_spki.as_ref(), theirs_spki.as_ref());

            for offered in [
                &[][..],
                &[scheme],
                &ALL_SCHEMES,
                &[SignatureScheme::ED25519, scheme],
                &[SignatureScheme::ED25519],
            ] {
                assert_eq!(
                    ours.choose_scheme(offered).map(|signer| signer.scheme()),
                    theirs.choose_scheme(offered).map(|signer| signer.scheme()),
                    "{offered:?}"
                );
            }

            // The key's raw bytes, which end its `SubjectPublicKeyInfo`.
            let public_key = &ours_spki.as_ref()[ours_spki.as_ref().len() - key_len..];
            let message = b"hello world";
            let ours_signature = ours
                .choose_scheme(&[scheme])
                .unwrap()
                .sign(message)
                .unwrap();
            let theirs_signature = theirs
                .choose_scheme(&[scheme])
                .unwrap()
                .sign(message)
                .unwrap();
            assert_eq!(ours_signature.len(), signature_len);
            assert_eq!(theirs_signature.len(), signature_len);
            for verify in [ours_verify(scheme), theirs_verify(scheme)] {
                for signature in [&ours_signature, &theirs_signature] {
                    verify
                        .verify_signature(public_key, message, signature)
                        .unwrap();
                    assert!(
                        verify
                            .verify_signature(public_key, b"other", signature)
                            .is_err()
                    );
                }
            }
        }
    }

    // RFC 9881's three private key forms (the seed, the expanded key, and both),
    // and their mismatches, load or fail as aws-lc-rs's loader does, and a key
    // that loads has the same public key. The expanded key comes from aws-lc-rs
    // expanding each fixture's seed.
    // aws-lc-rs does not build for wasm.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn test_ml_dsa_key_forms_match_aws_lc_rs() {
        use ::aws_lc_rs::encoding::AsRawBytes;
        use ::aws_lc_rs::signature::{
            ML_DSA_44_SIGNING, ML_DSA_65_SIGNING, ML_DSA_87_SIGNING, PqdsaKeyPair,
        };
        use rustls::crypto::aws_lc_rs as theirs_provider;

        fn tlv(tag: u8, content: &[u8]) -> Vec<u8> {
            let mut out = vec![tag];
            match content.len() {
                len @ 0..=0x7f => out.push(len as u8),
                len @ 0x80..=0xff => out.extend([0x81, len as u8]),
                len => out.extend([0x82, (len >> 8) as u8, len as u8]),
            }
            out.extend_from_slice(content);
            out
        }

        let signing = [&ML_DSA_44_SIGNING, &ML_DSA_65_SIGNING, &ML_DSA_87_SIGNING];
        for ((_, _, _, der), algorithm) in ml_dsa_test_keys().into_iter().zip(signing) {
            let PrivateKeyDer::Pkcs8(pkcs8) = &der else {
                unreachable!()
            };
            let pkcs8 = pkcs8.secret_pkcs8_der();
            // `SEQUENCE { INTEGER 0, AlgorithmIdentifier, OCTET STRING { [0] seed } }`.
            assert_eq!(
                (pkcs8.len(), &pkcs8[18..22]),
                (54, &[0x04, 0x22, 0x80, 0x20][..])
            );
            let (algorithm_id, seed) = (&pkcs8[5..18], &pkcs8[22..]);
            let expanded = PqdsaKeyPair::from_seed(algorithm, seed)
                .unwrap()
                .private_key()
                .as_raw_bytes()
                .unwrap();
            let expanded = expanded.as_ref();

            let key = |private_key: Vec<u8>| {
                let mut body = vec![0x02, 0x01, 0x00];
                body.extend_from_slice(algorithm_id);
                body.extend(tlv(0x04, &private_key));
                PrivateKeyDer::Pkcs8(tlv(0x30, &body).into())
            };
            let both = |seed: &[u8], expanded: &[u8]| {
                let mut inner = tlv(0x04, seed);
                inner.extend(tlv(0x04, expanded));
                tlv(0x30, &inner)
            };
            let flipped = |bytes: &[u8], at: usize| {
                let mut bytes = bytes.to_vec();
                bytes[at] ^= 1;
                bytes
            };

            let cases = [
                ("seed", key(tlv(0x80, seed)), true),
                ("expanded", key(tlv(0x04, expanded)), true),
                ("both", key(both(seed, expanded)), true),
                (
                    "both, other seed",
                    key(both(&flipped(seed, 0), expanded)),
                    false,
                ),
                (
                    "both, other expanded key",
                    key(both(seed, &flipped(expanded, expanded.len() - 1))),
                    false,
                ),
                (
                    "expanded, flipped first byte",
                    key(tlv(0x04, &flipped(expanded, 0))),
                    false,
                ),
                (
                    "expanded, flipped last byte",
                    key(tlv(0x04, &flipped(expanded, expanded.len() - 1))),
                    false,
                ),
                (
                    "expanded, one byte short",
                    key(tlv(0x04, &expanded[..expanded.len() - 1])),
                    false,
                ),
                ("seed, one byte short", key(tlv(0x80, &seed[..31])), false),
            ];
            for (name, der, loads) in cases {
                let ours = any_supported_type(&der);
                let theirs = theirs_provider::sign::any_supported_type(&der);
                assert_eq!(ours.is_ok(), theirs.is_ok(), "{algorithm:?}: {name}");
                if loads {
                    let (ours, theirs) = (ours.unwrap(), theirs.unwrap());
                    assert_eq!(ours.algorithm(), theirs.algorithm(), "{name}");
                    assert_eq!(
                        ours.public_key().unwrap().as_ref(),
                        theirs.public_key().unwrap().as_ref(),
                        "{name}"
                    );
                }
            }
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
