use std::fmt;

use dimpl::crypto::{
    Buf, HashAlgorithm, KeyProvider, NamedGroup, SignatureAlgorithm, SignatureVerifier, SigningKey,
    check_verify_scheme,
};
use dimpl::{CryptoError, CryptoOperation};
use rind::signature::{
    EcdsaKeyPair, EcdsaSigningAlgorithm, PublicKey, VerificationAlgorithm, sign, verify,
};
use rustls_pki_types::pem;
use x509_cert::Certificate;
use x509_cert::der::Decode;
use x509_cert::spki::ObjectIdentifier;

const ID_EC_PUBLIC_KEY: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.2.840.10045.2.1");
const SECP256R1: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.2.840.10045.3.1.7");
const SECP384R1: ObjectIdentifier = ObjectIdentifier::new_unwrap("1.3.132.0.34");

/// Each curve, and the one hash its key signs with.
///
/// A key is bound to its hash when loaded, as with dimpl's aws-lc-rs
/// provider, so each curve signs with its own hash only.
const CURVES: [(NamedGroup, HashAlgorithm, &EcdsaSigningAlgorithm); 2] = [
    (
        NamedGroup::Secp256r1,
        HashAlgorithm::SHA256,
        &sign::ECDSA_P256_SHA256_ASN1,
    ),
    (
        NamedGroup::Secp384r1,
        HashAlgorithm::SHA384,
        &sign::ECDSA_P384_SHA384_ASN1,
    ),
];

#[derive(Debug)]
pub(crate) struct Keys;

pub(crate) static KEYS: Keys = Keys;

impl KeyProvider for Keys {
    fn load_private_key(&self, der: &[u8]) -> Result<Box<dyn SigningKey>, CryptoError> {
        type Load = fn(&'static EcdsaSigningAlgorithm, &[u8]) -> Result<EcdsaKeyPair, rind::Error>;
        let load = |load: Load, der: &[u8]| {
            CURVES.into_iter().find_map(|(group, hash, algorithm)| {
                let key = load(algorithm, der).ok()?;
                Some(Box::new(Key { key, group, hash }) as Box<dyn SigningKey>)
            })
        };
        let der_key = |der: &[u8]| {
            load(EcdsaKeyPair::from_pkcs8, der).or_else(|| load(EcdsaKeyPair::from_sec1, der))
        };
        // dimpl's own providers also take a PEM-wrapped key, under any label.
        der_key(der)
            .or_else(|| {
                let relabeled = relabel(der)?;
                let mut rest = relabeled.as_slice();
                let (_, key) = pem::from_buf(&mut rest).ok()??;
                // A second footer would otherwise outlive the section.
                if !rest.is_empty() {
                    return None;
                }
                der_key(&key)
            })
            .ok_or(CryptoError::InvalidPrivateKey)
    }
}

struct Key {
    key: EcdsaKeyPair,
    group: NamedGroup,
    hash: HashAlgorithm,
}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("group", &self.group)
            .field("hash", &self.hash)
            .finish_non_exhaustive()
    }
}

impl SigningKey for Key {
    fn sign(&mut self, data: &[u8], hash: HashAlgorithm, out: &mut Buf) -> Result<(), CryptoError> {
        if hash != self.hash {
            return Err(CryptoError::SigningKeyHashMismatch {
                key_hash: self.hash,
                requested: hash,
            });
        }
        let signature = self
            .key
            .sign(data)
            .map_err(|_| CryptoError::OperationFailed(CryptoOperation::Sign))?;
        out.clear();
        out.extend_from_slice(signature.as_ref());
        Ok(())
    }

    fn algorithm(&self) -> SignatureAlgorithm {
        SignatureAlgorithm::ECDSA
    }

    fn hash_algorithm(&self) -> HashAlgorithm {
        self.hash
    }

    fn supported_hash_algorithms(&self) -> &[HashAlgorithm] {
        core::slice::from_ref(&self.hash)
    }
}

#[derive(Debug)]
pub(crate) struct Verifier;

pub(crate) static VERIFIER: Verifier = Verifier;

impl SignatureVerifier for Verifier {
    fn verify_signature(
        &self,
        cert_der: &[u8],
        data: &[u8],
        signature: &[u8],
        hash: HashAlgorithm,
        algorithm: SignatureAlgorithm,
    ) -> Result<(), CryptoError> {
        if algorithm != SignatureAlgorithm::ECDSA {
            return Err(CryptoError::UnsupportedSignatureAlgorithm(algorithm));
        }

        let cert =
            Certificate::from_der(cert_der).map_err(|_| CryptoError::CertificateParseFailed)?;
        let spki = cert.tbs_certificate().subject_public_key_info();
        if spki.algorithm.oid != ID_EC_PUBLIC_KEY {
            return Err(CryptoError::UnsupportedPublicKeyAlgorithm);
        }
        let curve: ObjectIdentifier = spki
            .algorithm
            .parameters
            .as_ref()
            .ok_or(CryptoError::MissingEcCurveParameter)?
            .decode_as()
            .map_err(|_| CryptoError::InvalidEcCurveParameter)?;
        let group = match curve {
            SECP256R1 => NamedGroup::Secp256r1,
            SECP384R1 => NamedGroup::Secp384r1,
            _ => return Err(CryptoError::UnsupportedEcCurve),
        };
        check_verify_scheme(algorithm, hash, group)?;

        // DTLS 1.2 may pair either curve with either hash.
        let verification: &'static VerificationAlgorithm = match (group, hash) {
            (NamedGroup::Secp256r1, HashAlgorithm::SHA256) => &verify::ECDSA_P256_SHA256_ASN1,
            (NamedGroup::Secp256r1, HashAlgorithm::SHA384) => &verify::ECDSA_P256_SHA384_ASN1,
            (NamedGroup::Secp384r1, HashAlgorithm::SHA256) => &verify::ECDSA_P384_SHA256_ASN1,
            (NamedGroup::Secp384r1, HashAlgorithm::SHA384) => &verify::ECDSA_P384_SHA384_ASN1,
            _ => {
                return Err(CryptoError::UnsupportedSignatureVerification {
                    signature: algorithm,
                    hash,
                    group,
                });
            }
        };

        let point = spki
            .subject_public_key
            .as_bytes()
            .ok_or(CryptoError::InvalidSubjectPublicKey)?;
        PublicKey::new(verification, point)
            .map_err(|_| CryptoError::InvalidPublicKey(group))?
            .verify(data, signature)
            .map_err(|_| CryptoError::SignatureVerificationFailed {
                signature: algorithm,
                hash,
                group,
            })
    }
}

/// Rewrites a PEM key's label to `PRIVATE KEY`, which rustls-pki-types
/// decodes as a secret; it skips sections whose label it does not know.
///
/// Like dimpl's pem-rfc7468, it takes one section ending the input, up to one
/// line ending, after an optional preamble that holds no NUL and ends in a line
/// feed. Input starting with the DER SEQUENCE tag is refused first, since a DER
/// key's later bytes are secret, and the searches stop at the boundaries, so
/// none reads key bytes.
fn relabel(pem: &[u8]) -> Option<Vec<u8>> {
    const BEGIN: &[u8] = b"-----BEGIN ";
    const DASHES: &[u8] = b"-----";
    if pem.first() == Some(&0x30) {
        return None;
    }
    let start = match pem.starts_with(BEGIN) {
        true => 0,
        false => {
            pem.windows(BEGIN.len() + 1)
                .position(|w| w == b"\n-----BEGIN ")?
                + 1
        }
    };
    let preamble = &pem[..start];
    if preamble.contains(&0) || str::from_utf8(preamble).is_err() {
        return None;
    }
    let rest = &pem[start + BEGIN.len()..];
    let label_len = rest.windows(DASHES.len()).position(|w| w == DASHES)?;
    let (label, rest) = rest.split_at(label_len);
    // pem-rfc7468's label grammar: printable characters other than hyphens,
    // with single spaces or tabs between or after them.
    let mut separated = true;
    for &c in label {
        let separator = matches!(c, b' ' | b'\t');
        if c == b'-' || !(separator || (0x21..=0x7e).contains(&c)) || (separator && separated) {
            return None;
        }
        separated = separator;
    }
    let rest = &rest[DASHES.len()..];
    let rest = [&b"\r\n"[..], b"\n", b"\r"]
        .into_iter()
        .find_map(|eol| rest.strip_suffix(eol))
        .unwrap_or(rest);
    let end = [b"-----END ", label, DASHES].concat();
    let body = rest.strip_suffix(end.as_slice())?;
    Some(
        [
            b"-----BEGIN PRIVATE KEY-----",
            body,
            b"-----END PRIVATE KEY-----",
        ]
        .concat(),
    )
}
