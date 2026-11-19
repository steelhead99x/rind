use rind::ml_dsa::{self, MlDsa44, MlDsa65, MlDsa87};
use rind::{ecdsa, ed25519, rsa};
use rustls::pki_types::{
    AlgorithmIdentifier, InvalidSignature, SignatureVerificationAlgorithm, alg_id,
};

/// Verifies ECDSA signatures by P-256 keys over SHA-256.
pub static ECDSA_P256_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA256,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P256_SHA256_ASN1),
};

/// Verifies ECDSA signatures by P-256 keys over SHA-384.
pub static ECDSA_P256_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA384,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P256_SHA384_ASN1),
};

/// Verifies ECDSA signatures by P-256 keys over SHA-512.
pub static ECDSA_P256_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P256,
    signature_alg_id: alg_id::ECDSA_SHA512,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P256_SHA512_ASN1),
};

/// Verifies ECDSA signatures by P-384 keys over SHA-256.
pub static ECDSA_P384_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA256,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P384_SHA256_ASN1),
};

/// Verifies ECDSA signatures by P-384 keys over SHA-384.
pub static ECDSA_P384_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA384,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P384_SHA384_ASN1),
};

/// Verifies ECDSA signatures by P-384 keys over SHA-512.
pub static ECDSA_P384_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P384,
    signature_alg_id: alg_id::ECDSA_SHA512,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P384_SHA512_ASN1),
};

/// Verifies ECDSA signatures by P-521 keys over SHA-256.
pub static ECDSA_P521_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA256,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P521_SHA256_ASN1),
};

/// Verifies ECDSA signatures by P-521 keys over SHA-384.
pub static ECDSA_P521_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA384,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P521_SHA384_ASN1),
};

/// Verifies ECDSA signatures by P-521 keys over SHA-512.
pub static ECDSA_P521_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ECDSA_P521,
    signature_alg_id: alg_id::ECDSA_SHA512,
    algorithm: Algorithm::Ecdsa(&ecdsa::verify::P521_SHA512_ASN1),
};

/// Verifies Ed25519 signatures.
pub static ED25519: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ED25519,
    signature_alg_id: alg_id::ED25519,
    algorithm: Algorithm::Ed25519,
};

/// Verifies RSASSA-PSS signatures over SHA-256 by 2048- to 8192-bit RSA keys.
pub static RSA_PSS_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PSS_SHA256,
    algorithm: Algorithm::Rsa(&rsa::verify::PSS_SHA256),
};

/// Verifies RSASSA-PSS signatures over SHA-384 by 2048- to 8192-bit RSA keys.
pub static RSA_PSS_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PSS_SHA384,
    algorithm: Algorithm::Rsa(&rsa::verify::PSS_SHA384),
};

/// Verifies RSASSA-PSS signatures over SHA-512 by 2048- to 8192-bit RSA keys.
pub static RSA_PSS_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PSS_SHA512,
    algorithm: Algorithm::Rsa(&rsa::verify::PSS_SHA512),
};

/// Verifies RSASSA-PKCS1-v1_5 signatures over SHA-256 by 2048- to 8192-bit RSA keys.
pub static RSA_PKCS1_SHA256: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PKCS1_SHA256,
    algorithm: Algorithm::Rsa(&rsa::verify::PKCS1_SHA256),
};

/// Verifies RSASSA-PKCS1-v1_5 signatures over SHA-384 by 2048- to 8192-bit RSA keys.
pub static RSA_PKCS1_SHA384: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PKCS1_SHA384,
    algorithm: Algorithm::Rsa(&rsa::verify::PKCS1_SHA384),
};

/// Verifies RSASSA-PKCS1-v1_5 signatures over SHA-512 by 2048- to 8192-bit RSA keys.
pub static RSA_PKCS1_SHA512: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    signature_alg_id: alg_id::RSA_PKCS1_SHA512,
    algorithm: Algorithm::Rsa(&rsa::verify::PKCS1_SHA512),
};

/// [`RSA_PKCS1_SHA256`] for certificates that omit RFC 4055's NULL parameters, as webpki allows.
pub static RSA_PKCS1_SHA256_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    // sha256WithRSAEncryption
    signature_alg_id: AlgorithmIdentifier::from_slice(&[
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b,
    ]),
    algorithm: Algorithm::Rsa(&rsa::verify::PKCS1_SHA256),
};

/// [`RSA_PKCS1_SHA384`] for certificates that omit RFC 4055's NULL parameters, as webpki allows.
pub static RSA_PKCS1_SHA384_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    // sha384WithRSAEncryption
    signature_alg_id: AlgorithmIdentifier::from_slice(&[
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0c,
    ]),
    algorithm: Algorithm::Rsa(&rsa::verify::PKCS1_SHA384),
};

/// [`RSA_PKCS1_SHA512`] for certificates that omit RFC 4055's NULL parameters, as webpki allows.
pub static RSA_PKCS1_SHA512_ABSENT_PARAMS: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::RSA_ENCRYPTION,
    // sha512WithRSAEncryption
    signature_alg_id: AlgorithmIdentifier::from_slice(&[
        0x06, 0x09, 0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0d,
    ]),
    algorithm: Algorithm::Rsa(&rsa::verify::PKCS1_SHA512),
};

/// Verifies ML-DSA-44 signatures (FIPS 204, security category 2), pure with the empty context.
pub static ML_DSA_44: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ML_DSA_44,
    signature_alg_id: alg_id::ML_DSA_44,
    algorithm: Algorithm::MlDsa44,
};

/// Verifies ML-DSA-65 signatures (FIPS 204, security category 3), pure with the empty context.
pub static ML_DSA_65: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ML_DSA_65,
    signature_alg_id: alg_id::ML_DSA_65,
    algorithm: Algorithm::MlDsa65,
};

/// Verifies ML-DSA-87 signatures (FIPS 204, security category 5), pure with the empty context.
pub static ML_DSA_87: &dyn SignatureVerificationAlgorithm = &Verify {
    public_key_alg_id: alg_id::ML_DSA_87,
    signature_alg_id: alg_id::ML_DSA_87,
    algorithm: Algorithm::MlDsa87,
};

/// A webpki algorithm: its identifiers, and the rind constant that verifies it.
///
/// webpki hands over the `subjectPublicKey` bit string, which is the encoding
/// each public key's `new` takes: an X9.62 point, a PKCS#1 `RSAPublicKey`,
/// Ed25519's 32 bytes, or FIPS 204's encoding of an ML-DSA key (RFC 9881).
#[derive(Debug)]
struct Verify {
    public_key_alg_id: AlgorithmIdentifier,
    signature_alg_id: AlgorithmIdentifier,
    algorithm: Algorithm,
}

/// The rind algorithm that verifies a webpki one, by key type.
#[derive(Debug)]
enum Algorithm {
    Ecdsa(&'static ecdsa::VerificationAlgorithm),
    Ed25519,
    Rsa(&'static rsa::VerificationAlgorithm),
    MlDsa44,
    MlDsa65,
    MlDsa87,
}

fn verify_ml_dsa<P: ml_dsa::ParameterSet>(
    public_key: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), rind::Error> {
    ml_dsa::PublicKey::<P>::new(public_key).and_then(|key| key.verify(message, signature))
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
        match self.algorithm {
            Algorithm::Ecdsa(algorithm) => ecdsa::PublicKey::new(algorithm, public_key)
                .and_then(|key| key.verify(message, signature)),
            Algorithm::Ed25519 => {
                ed25519::PublicKey::new(public_key).and_then(|key| key.verify(message, signature))
            }
            Algorithm::Rsa(algorithm) => rsa::PublicKey::new(public_key)
                .and_then(|key| key.verify(algorithm, message, signature)),
            Algorithm::MlDsa44 => verify_ml_dsa::<MlDsa44>(public_key, message, signature),
            Algorithm::MlDsa65 => verify_ml_dsa::<MlDsa65>(public_key, message, signature),
            Algorithm::MlDsa87 => verify_ml_dsa::<MlDsa87>(public_key, message, signature),
        }
        .map_err(|_| InvalidSignature)
    }
}

#[cfg(test)]
mod tests {
    use rind::ecdsa::KeyPair as EcdsaKeyPair;
    use rind::ed25519::KeyPair as Ed25519KeyPair;
    use rind::ml_dsa::KeyPair as MlDsaKeyPair;
    use rind::rand;
    use rind::rsa::KeyPair as RsaKeyPair;
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
                &ecdsa::sign::P256_SHA256_ASN1,
                ECDSA_P256_SHA256,
                [ECDSA_P256_SHA384, ECDSA_P256_SHA512, ECDSA_P384_SHA256],
            ),
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp384r1.pkcs8.der")[..],
                &ecdsa::sign::P384_SHA384_ASN1,
                ECDSA_P384_SHA384,
                [ECDSA_P384_SHA256, ECDSA_P384_SHA512, ECDSA_P256_SHA384],
            ),
            (
                &include_bytes!("../../rind/src/high/ecdsa/secp521r1.pkcs8.der")[..],
                &ecdsa::sign::P521_SHA512_ASN1,
                ECDSA_P521_SHA512,
                [ECDSA_P521_SHA256, ECDSA_P521_SHA384, ECDSA_P384_SHA512],
            ),
        ] {
            let key = EcdsaKeyPair::from_pkcs8(signing, pkcs8).unwrap();
            let message = message();
            let signature = key.sign(&message).unwrap();
            let public_key = key.public_key().as_ref();
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

    // A signature verifies under its own parameter set's algorithm, and under
    // neither other's; the key, the message, and the signature each refuse any
    // change, and webpki's raw key bytes are the only encoding of a key.
    #[test]
    fn test_ml_dsa_verify() {
        fn check<P: ml_dsa::ParameterSet>(
            algorithm: &dyn SignatureVerificationAlgorithm,
            id: AlgorithmIdentifier,
            others: [&dyn SignatureVerificationAlgorithm; 2],
            (key_len, signature_len): (usize, usize),
        ) {
            assert_eq!(algorithm.public_key_alg_id(), id);
            assert_eq!(algorithm.signature_alg_id(), id);

            let key = MlDsaKeyPair::<P>::generate().unwrap();
            let message = message();
            let signature = key.sign(&message).unwrap();
            let (public_key, signature) = (key.public_key().as_ref(), signature.as_ref());
            assert_eq!(
                (public_key.len(), signature.len()),
                (key_len, signature_len)
            );
            let verify = |public_key: &[u8], message: &[u8], signature: &[u8]| {
                algorithm.verify_signature(public_key, message, signature)
            };
            verify(public_key, &message, signature).unwrap();
            for other in others {
                assert!(
                    other
                        .verify_signature(public_key, &message, signature)
                        .is_err()
                );
            }

            let mut changed = message;
            changed[0] ^= 1;
            assert!(verify(public_key, &changed, signature).is_err());
            assert!(verify(public_key, &[], signature).is_err());

            for at in [0, signature_len / 2, signature_len - 1] {
                let mut changed = signature.to_vec();
                changed[at] ^= 1;
                assert!(verify(public_key, &message, &changed).is_err(), "{at}");
            }
            for len in [0, 1, signature_len - 1] {
                assert!(verify(public_key, &message, &signature[..len]).is_err());
            }
            let longer = [signature, &[0]].concat();
            assert!(verify(public_key, &message, &longer).is_err());

            for at in [0, key_len / 2, key_len - 1] {
                let mut changed = public_key.to_vec();
                changed[at] ^= 1;
                assert!(verify(&changed, &message, signature).is_err(), "{at}");
            }
            for len in [0, 1, key_len - 1] {
                assert!(verify(&public_key[..len], &message, signature).is_err());
            }
            let longer = [public_key, &[0]].concat();
            assert!(verify(&longer, &message, signature).is_err());

            // webpki hands over the bit string, not the `SubjectPublicKeyInfo`.
            let spki = key.public_key().to_spki();
            assert!(verify(spki.as_ref(), &message, signature).is_err());
        }

        check::<MlDsa44>(
            ML_DSA_44,
            alg_id::ML_DSA_44,
            [ML_DSA_65, ML_DSA_87],
            (1312, 2420),
        );
        check::<MlDsa65>(
            ML_DSA_65,
            alg_id::ML_DSA_65,
            [ML_DSA_44, ML_DSA_87],
            (1952, 3309),
        );
        check::<MlDsa87>(
            ML_DSA_87,
            alg_id::ML_DSA_87,
            [ML_DSA_44, ML_DSA_65],
            (2592, 4627),
        );
    }

    // Each algorithm accepts what aws-lc-rs's accepts and refuses what it
    // refuses, whether or not the input is well formed.
    // aws-lc-rs does not build for wasm.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn test_ml_dsa_verify_matches_aws_lc_rs() {
        fn check<P: ml_dsa::ParameterSet>(
            ours: &dyn SignatureVerificationAlgorithm,
            theirs: &dyn SignatureVerificationAlgorithm,
        ) {
            let key = MlDsaKeyPair::<P>::generate().unwrap();
            let message = message();
            let signature = key.sign(&message).unwrap();
            let (public_key, signature) = (key.public_key().as_ref(), signature.as_ref());

            let mut bad_key = public_key.to_vec();
            bad_key[0] ^= 1;
            let mut bad_signature = signature.to_vec();
            *bad_signature.last_mut().unwrap() ^= 1;
            let cases = [
                (public_key, &message[..], signature),
                (public_key, &message[1..], signature),
                (public_key, &message[..], &signature[1..]),
                (public_key, &message[..], &[][..]),
                (public_key, &message[..], &bad_signature),
                (&public_key[1..], &message[..], signature),
                (&[][..], &message[..], signature),
                (&bad_key, &message[..], signature),
            ];
            for (i, (public_key, message, signature)) in cases.into_iter().enumerate() {
                assert_eq!(
                    ours.verify_signature(public_key, message, signature)
                        .is_ok(),
                    theirs
                        .verify_signature(public_key, message, signature)
                        .is_ok(),
                    "case {i}"
                );
            }
            assert!(
                ours.verify_signature(public_key, &message, signature)
                    .is_ok()
            );
        }

        let theirs =
            rustls::crypto::aws_lc_rs::default_provider().signature_verification_algorithms;
        let theirs = |scheme| {
            let (_, algorithms) = theirs
                .mapping
                .iter()
                .find(|(theirs, _)| *theirs == scheme)
                .unwrap();
            algorithms[0]
        };
        check::<MlDsa44>(ML_DSA_44, theirs(SignatureScheme::ML_DSA_44));
        check::<MlDsa65>(ML_DSA_65, theirs(SignatureScheme::ML_DSA_65));
        check::<MlDsa87>(ML_DSA_87, theirs(SignatureScheme::ML_DSA_87));
    }

    // TLS 1.3 verifies a scheme with its mapping's first algorithm only, so
    // each ML-DSA scheme names its own parameter set, and no other scheme
    // names an ML-DSA algorithm.
    #[test]
    fn test_ml_dsa_scheme_mapping() {
        for (scheme, algorithms) in crate::SUPPORTED_SIG_ALGS.mapping {
            let expected = match scheme {
                SignatureScheme::ML_DSA_44 => Some(alg_id::ML_DSA_44),
                SignatureScheme::ML_DSA_65 => Some(alg_id::ML_DSA_65),
                SignatureScheme::ML_DSA_87 => Some(alg_id::ML_DSA_87),
                _ => None,
            };
            let ml_dsa = [alg_id::ML_DSA_44, alg_id::ML_DSA_65, alg_id::ML_DSA_87];
            match expected {
                Some(id) => {
                    assert_eq!(algorithms.len(), 1, "{scheme:?}");
                    assert_eq!(algorithms[0].public_key_alg_id(), id, "{scheme:?}");
                    assert_eq!(algorithms[0].signature_alg_id(), id, "{scheme:?}");
                }
                None => assert!(
                    algorithms
                        .iter()
                        .all(|alg| !ml_dsa.contains(&alg.public_key_alg_id())),
                    "{scheme:?}"
                ),
            }
        }
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
                &rsa::sign::PSS_SHA256,
            ),
            (
                RSA_PSS_SHA384,
                alg_id::RSA_PSS_SHA384,
                &rsa::sign::PSS_SHA384,
            ),
            (
                RSA_PSS_SHA512,
                alg_id::RSA_PSS_SHA512,
                &rsa::sign::PSS_SHA512,
            ),
            (
                RSA_PKCS1_SHA256,
                alg_id::RSA_PKCS1_SHA256,
                &rsa::sign::PKCS1_SHA256,
            ),
            (
                RSA_PKCS1_SHA384,
                alg_id::RSA_PKCS1_SHA384,
                &rsa::sign::PKCS1_SHA384,
            ),
            (
                RSA_PKCS1_SHA512,
                alg_id::RSA_PKCS1_SHA512,
                &rsa::sign::PKCS1_SHA512,
            ),
        ];
        for (i, (algorithm, alg_id, padding)) in schemes.iter().enumerate() {
            assert_eq!(algorithm.signature_alg_id(), *alg_id);
            let signature = key.sign(padding, &message).unwrap();
            let public_key = key.public_key();
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
                &rsa::sign::PKCS1_SHA256,
            ),
            (
                RSA_PKCS1_SHA384_ABSENT_PARAMS,
                RSA_PKCS1_SHA384,
                &rsa::sign::PKCS1_SHA384,
            ),
            (
                RSA_PKCS1_SHA512_ABSENT_PARAMS,
                RSA_PKCS1_SHA512,
                &rsa::sign::PKCS1_SHA512,
            ),
        ] {
            let present_id = present.signature_alg_id();
            let (oid, null) = present_id.as_ref().split_at(present_id.as_ref().len() - 2);
            assert_eq!(null, [0x05, 0x00]);
            assert_eq!(absent.signature_alg_id().as_ref(), oid);
            assert_eq!(absent.public_key_alg_id(), present.public_key_alg_id());

            let signature = key.sign(padding, &message).unwrap();
            let public_key = key.public_key();
            absent
                .verify_signature(public_key.as_ref(), &message, signature.as_ref())
                .unwrap();
        }
    }

    // aws-lc-rs does not build for wasm.
    #[cfg(not(target_family = "wasm"))]
    #[test]
    fn ids_match_aws_lc() {
        let aws = rustls::crypto::aws_lc_rs::default_provider();
        let ours = crate::SUPPORTED_SIG_ALGS.all;
        // Equal lengths mean a missing rind algorithm cannot hide behind
        // `any`.
        let theirs = aws.signature_verification_algorithms.all;
        assert_eq!(ours.len(), theirs.len());
        for alg in ours {
            assert!(
                theirs.iter().any(|other| {
                    other.public_key_alg_id() == alg.public_key_alg_id()
                        && other.signature_alg_id() == alg.signature_alg_id()
                }),
                "{alg:?}"
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
