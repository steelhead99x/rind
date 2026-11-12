use core::fmt;

use rind::signature::{self, VerificationAlgorithm, verify};
use rustls::pki_types::{
    AlgorithmIdentifier, InvalidSignature, SignatureVerificationAlgorithm, alg_id,
};

/// Verifies ECDSA signatures by P-256 keys over SHA-256.
pub static ECDSA_P256_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA256,
    algorithm: &verify::ECDSA_P256_SHA256_ASN1,
};

/// Verifies ECDSA signatures by P-256 keys over SHA-384.
pub static ECDSA_P256_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA384,
    algorithm: &verify::ECDSA_P256_SHA384_ASN1,
};

/// Verifies ECDSA signatures by P-256 keys over SHA-512.
pub static ECDSA_P256_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA512,
    algorithm: &verify::ECDSA_P256_SHA512_ASN1,
};

/// Verifies ECDSA signatures by P-384 keys over SHA-256.
pub static ECDSA_P384_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA256,
    algorithm: &verify::ECDSA_P384_SHA256_ASN1,
};

/// Verifies ECDSA signatures by P-384 keys over SHA-384.
pub static ECDSA_P384_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA384,
    algorithm: &verify::ECDSA_P384_SHA384_ASN1,
};

/// Verifies ECDSA signatures by P-384 keys over SHA-512.
pub static ECDSA_P384_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA512,
    algorithm: &verify::ECDSA_P384_SHA512_ASN1,
};

/// Verifies ECDSA signatures by P-521 keys over SHA-256.
pub static ECDSA_P521_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA256,
    algorithm: &verify::ECDSA_P521_SHA256_ASN1,
};

/// Verifies ECDSA signatures by P-521 keys over SHA-384.
pub static ECDSA_P521_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA384,
    algorithm: &verify::ECDSA_P521_SHA384_ASN1,
};

/// Verifies ECDSA signatures by P-521 keys over SHA-512.
pub static ECDSA_P521_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA512,
    algorithm: &verify::ECDSA_P521_SHA512_ASN1,
};

/// Verifies Ed25519 signatures.
pub static ED25519: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ED25519,
    signature_alg_id: alg_id::ED25519,
    algorithm: &verify::ED25519,
};

/// Verifies RSASSA-PSS signatures over SHA-256 by 2048- to 8192-bit RSA keys.
pub static RSA_PSS_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PSS_SHA256,
    algorithm: &verify::RSA_PSS_SHA256,
};

/// Verifies RSASSA-PSS signatures over SHA-384 by 2048- to 8192-bit RSA keys.
pub static RSA_PSS_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PSS_SHA384,
    algorithm: &verify::RSA_PSS_SHA384,
};

/// Verifies RSASSA-PSS signatures over SHA-512 by 2048- to 8192-bit RSA keys.
pub static RSA_PSS_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PSS_SHA512,
    algorithm: &verify::RSA_PSS_SHA512,
};

/// Verifies RSASSA-PKCS1-v1_5 signatures over SHA-256 by 2048- to 8192-bit RSA keys.
pub static RSA_PKCS1_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PKCS1_SHA256,
    algorithm: &verify::RSA_PKCS1_SHA256,
};

/// Verifies RSASSA-PKCS1-v1_5 signatures over SHA-384 by 2048- to 8192-bit RSA keys.
pub static RSA_PKCS1_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PKCS1_SHA384,
    algorithm: &verify::RSA_PKCS1_SHA384,
};

/// Verifies RSASSA-PKCS1-v1_5 signatures over SHA-512 by 2048- to 8192-bit RSA keys.
pub static RSA_PKCS1_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PKCS1_SHA512,
    algorithm: &verify::RSA_PKCS1_SHA512,
};

/// [`RSA_PKCS1_SHA256`] for certificates that omit RFC 4055's NULL parameters, as webpki allows.
pub static RSA_PKCS1_SHA256_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    // sha256WithRSAEncryption
    signature_alg_id: AlgorithmIdentifier::from_slice(&[
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b,
    ]),
    algorithm: &verify::RSA_PKCS1_SHA256,
};

/// [`RSA_PKCS1_SHA384`] for certificates that omit RFC 4055's NULL parameters, as webpki allows.
pub static RSA_PKCS1_SHA384_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    // sha384WithRSAEncryption
    signature_alg_id: AlgorithmIdentifier::from_slice(&[
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0c,
    ]),
    algorithm: &verify::RSA_PKCS1_SHA384,
};

/// [`RSA_PKCS1_SHA512`] for certificates that omit RFC 4055's NULL parameters, as webpki allows.
pub static RSA_PKCS1_SHA512_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    // sha512WithRSAEncryption
    signature_alg_id: AlgorithmIdentifier::from_slice(&[
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0d,
    ]),
    algorithm: &verify::RSA_PKCS1_SHA512,
};

/// A webpki algorithm: its identifiers, and the rind constant that verifies it.
///
/// webpki hands over the `subjectPublicKey` bit string, which is the encoding
/// each constant takes: an X9.62 point, a PKCS#1 `RSAPublicKey`, or Ed25519's
/// 32 bytes.
struct Verify {
    public_key_alg_id: AlgorithmIdentifier,
    signature_alg_id: AlgorithmIdentifier,
    // RSA's constants are their own type, which converts to this.
    algorithm: &'static (dyn AsRef<VerificationAlgorithm> + Sync),
}

impl fmt::Debug for Verify {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Verify")
            .field("public_key_alg_id", &self.public_key_alg_id)
            .field("signature_alg_id", &self.signature_alg_id)
            .field("algorithm", self.algorithm.as_ref())
            .finish()
    }
}

impl SignatureVerificationAlgorithm for Verify {
    fn public_key_alg_id(&self) -> AlgorithmIdentifier {
        self.public_key_alg_id
    }

    fn signature_alg_id(&self) -> AlgorithmIdentifier {
        self.signature_alg_id
    }

    fn verify_signature(
        &self,
        public_key: &[u8],
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), InvalidSignature> {
        signature::PublicKey::new(self.algorithm.as_ref(), public_key)
            .and_then(|key| key.verify(message, signature))
            .map_err(|_| InvalidSignature)
    }
}

#[cfg(test)]
mod tests {
    use rind::rand;
    use rind::signature::{EcdsaKeyPair, Ed25519KeyPair, RsaKeyPair, sign};
    use rustls::SignatureScheme;

    use super::*;

    fn message() -> [u8; 64] {
        let mut message = [0u8; 64];
        rand::fill(&mut message).unwrap();
        message
    }

    // TLS 1.3 binds each ECDSA scheme to a curve and verifies with the first
    // entry only, so that entry must be for the scheme's curve.
    #[test]
    fn test_ecdsa_scheme_curves() {
        for (scheme, algorithms) in crate::SUPPORTED_SIG_ALGS.mapping {
            let curve = match scheme {
                SignatureScheme::ECDSA_NISTP256_SHA256 => alg_id::ECDSA_P256,
                SignatureScheme::ECDSA_NISTP384_SHA384 => alg_id::ECDSA_P384,
                SignatureScheme::ECDSA_NISTP521_SHA512 => alg_id::ECDSA_P521,
                _ => continue,
            };
            assert_eq!(algorithms[0].public_key_alg_id(), curve, "{scheme:?}");
        }
    }

    // A signature verifies under its own algorithm, and under no other
    // algorithm for the same key type. rind signs ECDSA only with each
    // curve's own hash; Wycheproof covers the other pairs.
    #[test]
    fn test_ecdsa_verify() {
        for (pkcs8, signing, algorithm, others) in [
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp256r1.pkcs8.der")[..],
                &sign::ECDSA_P256_SHA256_ASN1,
                ECDSA_P256_SHA256,
                [ECDSA_P256_SHA384, ECDSA_P256_SHA512, ECDSA_P384_SHA256],
            ),
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp384r1.pkcs8.der")[..],
                &sign::ECDSA_P384_SHA384_ASN1,
                ECDSA_P384_SHA384,
                [ECDSA_P384_SHA256, ECDSA_P384_SHA512, ECDSA_P256_SHA384],
            ),
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp521r1.pkcs8.der")[..],
                &sign::ECDSA_P521_SHA512_ASN1,
                ECDSA_P521_SHA512,
                [ECDSA_P521_SHA256, ECDSA_P521_SHA384, ECDSA_P384_SHA512],
            ),
        ] {
            let key = EcdsaKeyPair::from_pkcs8(signing, pkcs8).unwrap();
            let message = message();
            let signature = key.sign(&message).unwrap();
            let public_key = key.public_key();
            let public_key = public_key.as_ref();
            algorithm
                .verify_signature(public_key, &message, signature.as_ref())
                .unwrap();
            for other in others {
                assert!(
                    other
                        .verify_signature(public_key, &message, signature.as_ref())
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn test_ed25519_verify() {
        let key = Ed25519KeyPair::generate().unwrap();
        let message = message();
        let signature = key.sign(&message);
        ED25519
            .verify_signature(key.public_key().as_ref(), &message, signature.as_ref())
            .unwrap();
    }

    #[test]
    fn test_rsa_verify() {
        let key =
            RsaKeyPair::from_pkcs8(include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der"))
                .unwrap();
        let message = message();
        let schemes = [
            (
                RSA_PSS_SHA256,
                alg_id::RSA_PSS_SHA256,
                &sign::RSA_PSS_SHA256,
            ),
            (
                RSA_PSS_SHA384,
                alg_id::RSA_PSS_SHA384,
                &sign::RSA_PSS_SHA384,
            ),
            (
                RSA_PSS_SHA512,
                alg_id::RSA_PSS_SHA512,
                &sign::RSA_PSS_SHA512,
            ),
            (
                RSA_PKCS1_SHA256,
                alg_id::RSA_PKCS1_SHA256,
                &sign::RSA_PKCS1_SHA256,
            ),
            (
                RSA_PKCS1_SHA384,
                alg_id::RSA_PKCS1_SHA384,
                &sign::RSA_PKCS1_SHA384,
            ),
            (
                RSA_PKCS1_SHA512,
                alg_id::RSA_PKCS1_SHA512,
                &sign::RSA_PKCS1_SHA512,
            ),
        ];
        for (i, (algorithm, alg_id, padding)) in schemes.iter().enumerate() {
            assert_eq!(algorithm.signature_alg_id(), *alg_id);
            let signature = key.sign(padding, &message).unwrap();
            let public_key = key.public_key(padding);
            for (j, (other, ..)) in schemes.iter().enumerate() {
                let result =
                    other.verify_signature(public_key.as_ref(), &message, signature.as_ref());
                assert_eq!(result.is_ok(), i == j);
            }
        }
    }

    // Each absent-parameters algorithm is its PKCS#1 sibling, with the
    // identifier's trailing NULL dropped.
    #[test]
    fn test_rsa_absent_params() {
        let key =
            RsaKeyPair::from_pkcs8(include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der"))
                .unwrap();
        let message = message();
        for (absent, present, padding) in [
            (
                RSA_PKCS1_SHA256_ABSENT_PARAMS,
                RSA_PKCS1_SHA256,
                &sign::RSA_PKCS1_SHA256,
            ),
            (
                RSA_PKCS1_SHA384_ABSENT_PARAMS,
                RSA_PKCS1_SHA384,
                &sign::RSA_PKCS1_SHA384,
            ),
            (
                RSA_PKCS1_SHA512_ABSENT_PARAMS,
                RSA_PKCS1_SHA512,
                &sign::RSA_PKCS1_SHA512,
            ),
        ] {
            let present_id = present.signature_alg_id();
            let (oid, null) = present_id.as_ref().split_at(present_id.as_ref().len() - 2);
            assert_eq!(null, [0x05, 0x00]);
            assert_eq!(absent.signature_alg_id().as_ref(), oid);
            assert_eq!(absent.public_key_alg_id(), present.public_key_alg_id());

            let signature = key.sign(padding, &message).unwrap();
            let public_key = key.public_key(padding);
            absent
                .verify_signature(public_key.as_ref(), &message, signature.as_ref())
                .unwrap();
        }
    }

    #[test]
    fn verify_debug_matches_aws_lc() {
        let aws = rustls::crypto::aws_lc_rs::default_provider();
        for alg in crate::SUPPORTED_SIG_ALGS.all {
            let rendered = format!("{alg:?}");
            // rustls names its type `AwsLcRsAlgorithm`. rind names `Verify`.
            // The identifiers are the values that have to match; an empty
            // `Debug` contains neither.
            assert!(rendered.contains("Verify"), "{rendered}");
            assert!(
                aws.signature_verification_algorithms
                    .all
                    .iter()
                    .any(|other| {
                        other.public_key_alg_id() == alg.public_key_alg_id()
                            && other.signature_alg_id() == alg.signature_alg_id()
                    }),
                "{rendered}"
            );
        }
    }

    // Like rustls's own providers: `all` holds no algorithm twice.
    #[test]
    fn test_no_duplicate_algorithms() {
        let ids = crate::SUPPORTED_SIG_ALGS
            .all
            .iter()
            .map(|alg| (alg.public_key_alg_id(), alg.signature_alg_id()))
            .collect::<Vec<_>>();
        for (i, id) in ids.iter().enumerate() {
            assert!(!ids[..i].contains(id), "{id:?}");
        }
    }
}
