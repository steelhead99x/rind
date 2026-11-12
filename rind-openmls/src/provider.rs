use openmls_traits::crypto::OpenMlsCrypto;
use openmls_traits::random::OpenMlsRand;
use openmls_traits::types::{
    AeadType, Ciphersuite, CryptoError, ExporterSecret, HashType, HpkeAeadType, HpkeCiphertext,
    HpkeConfig, HpkeKdfType, HpkeKemType, HpkeKeyPair, SignatureScheme,
};
use rind::signature::{
    EcdsaKeyPair, EcdsaSigningAlgorithm, Ed25519KeyPair, PublicKey, sign, verify,
};
use rind::{aead, digest, hmac, hpke};
use tls_codec::SecretVLBytes;

/// The ciphersuites openmls_rust_crypto offers.
const CIPHERSUITES: [Ciphersuite; 3] = [
    Ciphersuite::MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519,
    Ciphersuite::MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519,
    Ciphersuite::MLS_128_DHKEMP256_AES128GCM_SHA256_P256,
];

/// OpenMLS's cryptography and randomness on rind.
#[derive(Debug, Default)]
#[cfg_attr(feature = "test-utils", derive(Clone))]
pub struct RustCrypto {
    // rind draws every random byte from the system, so there is no state, but
    // the type stays opaque as upstream's is.
    _private: (),
}

impl OpenMlsCrypto for RustCrypto {
    fn supports(&self, ciphersuite: Ciphersuite) -> Result<(), CryptoError> {
        match CIPHERSUITES.contains(&ciphersuite) {
            true => Ok(()),
            false => Err(CryptoError::UnsupportedCiphersuite),
        }
    }

    fn supported_ciphersuites(&self) -> Vec<Ciphersuite> {
        CIPHERSUITES.to_vec()
    }

    fn hkdf_extract(
        &self,
        hash_type: HashType,
        salt: &[u8],
        ikm: &[u8],
    ) -> Result<SecretVLBytes, CryptoError> {
        self.hmac(hash_type, salt, ikm)
    }

    fn hmac(
        &self,
        hash_type: HashType,
        key: &[u8],
        message: &[u8],
    ) -> Result<SecretVLBytes, CryptoError> {
        let key = hmac::Key::new(hmac_algorithm(hash_type), key);
        Ok(hmac::sign(&key, message).as_ref().into())
    }

    // rind's `hkdf::Prk` cannot be loaded from bytes, so this is RFC 5869's
    // expand over HMAC.
    fn hkdf_expand(
        &self,
        hash_type: HashType,
        prk: &[u8],
        info: &[u8],
        okm_len: usize,
    ) -> Result<SecretVLBytes, CryptoError> {
        let hash_len = hash_type.size();
        if prk.len() < hash_len || okm_len > 255 * hash_len {
            return Err(CryptoError::HkdfOutputLengthInvalid);
        }
        let key = hmac::Key::new(hmac_algorithm(hash_type), prk);
        let mut okm = Vec::with_capacity(okm_len.next_multiple_of(hash_len));
        let mut previous = 0..0;
        for counter in 1..=okm_len.div_ceil(hash_len) {
            let mut ctx = hmac::Context::with_key(&key);
            ctx.update(&okm[previous.clone()]);
            ctx.update(info);
            // At most 255 blocks, checked above.
            ctx.update(&[counter as u8]);
            let start = okm.len();
            okm.extend_from_slice(ctx.sign().as_ref());
            previous = start..okm.len();
        }
        okm.truncate(okm_len);
        Ok(okm.into())
    }

    fn hash(&self, hash_type: HashType, data: &[u8]) -> Result<Vec<u8>, CryptoError> {
        let algorithm = match hash_type {
            HashType::Sha2_256 => &digest::SHA256,
            HashType::Sha2_384 => &digest::SHA384,
            HashType::Sha2_512 => &digest::SHA512,
        };
        Ok(digest::digest(algorithm, data).as_ref().to_vec())
    }

    fn aead_encrypt(
        &self,
        alg: AeadType,
        key: &[u8],
        data: &[u8],
        nonce: &[u8],
        aad: &[u8],
    ) -> Result<Vec<u8>, CryptoError> {
        let (key, nonce) = aead_key(alg, key, nonce)?;
        let mut in_out = data.to_vec();
        key.seal_in_place_append_tag(nonce, aad, &mut in_out)
            .map_err(|_| CryptoError::CryptoLibraryError)?;
        Ok(in_out)
    }

    fn aead_decrypt(
        &self,
        alg: AeadType,
        key: &[u8],
        ct_tag: &[u8],
        nonce: &[u8],
        aad: &[u8],
    ) -> Result<Vec<u8>, CryptoError> {
        let (key, nonce) = aead_key(alg, key, nonce)?;
        let mut in_out = ct_tag.to_vec();
        let len = key
            .open_in_place(nonce, aad, &mut in_out)
            .map_err(|_| CryptoError::AeadDecryptionError)?
            .len();
        in_out.truncate(len);
        Ok(in_out)
    }

    /// Returns the private key as Ed25519's 32-byte seed or ECDSA's
    /// big-endian scalar, and the public key as Ed25519's 32 bytes or an
    /// uncompressed point.
    fn signature_key_gen(&self, alg: SignatureScheme) -> Result<(Vec<u8>, Vec<u8>), CryptoError> {
        if alg == SignatureScheme::ED25519 {
            let key =
                Ed25519KeyPair::generate().map_err(|_| CryptoError::InsufficientRandomness)?;
            return Ok((
                key.to_seed().as_ref().to_vec(),
                key.public_key().as_ref().to_vec(),
            ));
        }
        let (algorithm, _) = ecdsa(alg)?;
        let key = EcdsaKeyPair::generate(algorithm.signing)
            .map_err(|_| CryptoError::InsufficientRandomness)?;
        Ok((
            key.to_scalar().as_ref().to_vec(),
            key.public_key().as_ref().to_vec(),
        ))
    }

    fn verify_signature(
        &self,
        alg: SignatureScheme,
        data: &[u8],
        pk: &[u8],
        signature: &[u8],
    ) -> Result<(), CryptoError> {
        let key = match alg {
            SignatureScheme::ED25519 => PublicKey::new(&verify::ED25519, pk),
            _ => {
                let (algorithm, _) = ecdsa(alg)?;
                // openmls_rust_crypto takes a compressed point too, which rind
                // decompresses only inside a `SubjectPublicKeyInfo`:
                // SEQUENCE { SEQUENCE { id-ecPublicKey, curve }, BIT STRING point }.
                if pk.len() > MAX_POINT_LEN {
                    return Err(CryptoError::CryptoLibraryError);
                }
                let id_len = EC_PUBLIC_KEY.len() + algorithm.curve.len();
                let spki = [
                    &[0x30, (5 + id_len + pk.len()) as u8, 0x30, id_len as u8],
                    &EC_PUBLIC_KEY[..],
                    algorithm.curve,
                    &[0x03, 1 + pk.len() as u8, 0x00],
                    pk,
                ]
                .concat();
                PublicKey::from_spki(algorithm.verification, &spki)
            }
        };
        key.map_err(|_| CryptoError::CryptoLibraryError)?
            .verify(data, signature)
            .map_err(|_| CryptoError::InvalidSignature)
    }

    fn sign(&self, alg: SignatureScheme, data: &[u8], key: &[u8]) -> Result<Vec<u8>, CryptoError> {
        if alg == SignatureScheme::ED25519 {
            let key =
                Ed25519KeyPair::from_seed(key).map_err(|_| CryptoError::CryptoLibraryError)?;
            return Ok(key.sign(data).as_ref().to_vec());
        }
        let (algorithm, scalar_len) = ecdsa(alg)?;
        if key.len() != scalar_len {
            return Err(CryptoError::CryptoLibraryError);
        }
        // `key` is the scalar alone, which rind loads only beside its public
        // key or inside a SEC1 `ECPrivateKey`, whose public key is optional:
        // SEQUENCE { INTEGER 1, OCTET STRING scalar }. Deriving the public
        // key just to check it would double the cost of signing.
        let mut sec1 = [0u8; 7 + MAX_SCALAR_LEN];
        let sec1 = &mut sec1[..7 + scalar_len];
        sec1[..7].copy_from_slice(&[
            0x30,
            5 + scalar_len as u8,
            0x02,
            0x01,
            0x01,
            0x04,
            scalar_len as u8,
        ]);
        sec1[7..].copy_from_slice(key);
        let key = EcdsaKeyPair::from_sec1(algorithm.signing, sec1)
            .map_err(|_| CryptoError::CryptoLibraryError)?;
        let signature = key.sign(data).map_err(|_| CryptoError::SigningError)?;
        Ok(signature.as_ref().to_vec())
    }

    fn hpke_seal(
        &self,
        config: HpkeConfig,
        pk_r: &[u8],
        info: &[u8],
        aad: &[u8],
        ptxt: &[u8],
    ) -> Result<HpkeCiphertext, CryptoError> {
        let (kem, suite) = hpke_suite(&config)?;
        let suite = suite.ok_or(CryptoError::UnsupportedAeadAlgorithm)?;
        let pk_r = hpke::PublicKey::new(kem, pk_r).map_err(|_| CryptoError::InvalidPublicKey)?;
        let (enc, mut sender) =
            hpke::Sender::new(suite, &pk_r, info).map_err(|_| CryptoError::SenderSetupError)?;
        let mut ciphertext = ptxt.to_vec();
        sender
            .seal_in_place_append_tag(aad, &mut ciphertext)
            .map_err(|_| CryptoError::HpkeEncryptionError)?;
        Ok(HpkeCiphertext {
            kem_output: enc.as_ref().into(),
            ciphertext: ciphertext.into(),
        })
    }

    fn hpke_open(
        &self,
        config: HpkeConfig,
        input: &HpkeCiphertext,
        sk_r: &[u8],
        info: &[u8],
        aad: &[u8],
    ) -> Result<Vec<u8>, CryptoError> {
        let (kem, suite) = hpke_suite(&config)?;
        let suite = suite.ok_or(CryptoError::UnsupportedAeadAlgorithm)?;
        let open = || {
            let sk_r = hpke::PrivateKey::from_scalar(kem, sk_r)?;
            let mut recipient =
                hpke::Recipient::new(suite, &sk_r, input.kem_output.as_slice(), info)?;
            let mut plaintext = input.ciphertext.as_slice().to_vec();
            let len = recipient.open_in_place(aad, &mut plaintext)?.len();
            plaintext.truncate(len);
            Ok::<_, rind::Error>(plaintext)
        };
        open().map_err(|_| CryptoError::HpkeDecryptionError)
    }

    fn hpke_setup_sender_and_export(
        &self,
        config: HpkeConfig,
        pk_r: &[u8],
        info: &[u8],
        exporter_context: &[u8],
        exporter_length: usize,
    ) -> Result<(Vec<u8>, ExporterSecret), CryptoError> {
        let (kem, suite) = hpke_suite(&config)?;
        let pk_r = hpke::PublicKey::new(kem, pk_r).map_err(|_| CryptoError::InvalidPublicKey)?;
        let mut secret = exporter_buffer(&config, exporter_length)?;
        // The AEAD is part of the context, so a suite with one exports from
        // its full context, not an export-only one.
        let (enc, exported) = match suite {
            Some(suite) => hpke::Sender::new(suite, &pk_r, info)
                .map(|(enc, sender)| (enc, sender.export(exporter_context, &mut secret))),
            None => hpke::Exporter::sender(hpke_kdf(config.1), &pk_r, info)
                .map(|(enc, exporter)| (enc, exporter.export(exporter_context, &mut secret))),
        }
        .map_err(|_| CryptoError::SenderSetupError)?;
        exported.map_err(|_| CryptoError::ExporterError)?;
        Ok((enc.as_ref().to_vec(), secret.into()))
    }

    fn hpke_setup_receiver_and_export(
        &self,
        config: HpkeConfig,
        enc: &[u8],
        sk_r: &[u8],
        info: &[u8],
        exporter_context: &[u8],
        exporter_length: usize,
    ) -> Result<ExporterSecret, CryptoError> {
        let (kem, suite) = hpke_suite(&config)?;
        let sk_r = hpke::PrivateKey::from_scalar(kem, sk_r)
            .map_err(|_| CryptoError::ReceiverSetupError)?;
        let mut secret = exporter_buffer(&config, exporter_length)?;
        match suite {
            Some(suite) => hpke::Recipient::new(suite, &sk_r, enc, info)
                .map(|recipient| recipient.export(exporter_context, &mut secret)),
            None => hpke::Exporter::recipient(hpke_kdf(config.1), &sk_r, enc, info)
                .map(|exporter| exporter.export(exporter_context, &mut secret)),
        }
        .map_err(|_| CryptoError::ReceiverSetupError)?
        .map_err(|_| CryptoError::ExporterError)?;
        Ok(secret.into())
    }

    /// Returns the private key as RFC 9180 serializes it: X25519's 32 bytes,
    /// or a NIST curve's big-endian scalar.
    fn derive_hpke_keypair(
        &self,
        config: HpkeConfig,
        ikm: &[u8],
    ) -> Result<HpkeKeyPair, CryptoError> {
        let (kem, _) = hpke_suite(&config)?;
        let key =
            hpke::PrivateKey::derive(kem, ikm).map_err(|_| CryptoError::CryptoLibraryError)?;
        Ok(HpkeKeyPair {
            private: key.to_scalar().as_ref().into(),
            public: key.public_key().as_ref().to_vec(),
        })
    }
}

impl OpenMlsRand for RustCrypto {
    type Error = RandError;

    fn random_array<const N: usize>(&self) -> Result<[u8; N], Self::Error> {
        let mut out = [0u8; N];
        rind::rand::fill(&mut out).map_err(|_| RandError::NotEnoughRandomness)?;
        Ok(out)
    }

    fn random_vec(&self, len: usize) -> Result<Vec<u8>, Self::Error> {
        let mut out = vec![0u8; len];
        rind::rand::fill(&mut out).map_err(|_| RandError::NotEnoughRandomness)?;
        Ok(out)
    }
}

/// Why randomness could not be drawn.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RandError {
    /// A lock around the random source was poisoned; rind holds none, so
    /// this is never returned.
    LockPoisoned,
    /// The system's random source failed.
    NotEnoughRandomness,
}

impl std::fmt::Display for RandError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::LockPoisoned => "Rng lock is poisoned.",
            Self::NotEnoughRandomness => "Unable to collect enough randomness.",
        })
    }
}

impl std::error::Error for RandError {}

/// The longest ECDSA scalar, P-384's.
const MAX_SCALAR_LEN: usize = 48;

/// The longest ECDSA public key, P-384's uncompressed point.
const MAX_POINT_LEN: usize = 1 + 2 * MAX_SCALAR_LEN;

/// The DER of `id-ecPublicKey`'s OID.
const EC_PUBLIC_KEY: [u8; 9] = [0x06, 0x07, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];

struct Ecdsa {
    signing: &'static EcdsaSigningAlgorithm,
    verification: &'static rind::signature::VerificationAlgorithm,
    /// The DER of the curve's OID.
    curve: &'static [u8],
}

/// Returns the ECDSA algorithms for `alg`, with DER signatures as MLS
/// carries them, and its scalar's length. P-521, like openmls_rust_crypto,
/// is unsupported.
fn ecdsa(alg: SignatureScheme) -> Result<(Ecdsa, usize), CryptoError> {
    let (signing, verification, curve, scalar_len): (_, _, &[u8], _) = match alg {
        SignatureScheme::ECDSA_SECP256R1_SHA256 => (
            &sign::ECDSA_P256_SHA256_ASN1,
            &verify::ECDSA_P256_SHA256_ASN1,
            &[0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07],
            32,
        ),
        SignatureScheme::ECDSA_SECP384R1_SHA384 => (
            &sign::ECDSA_P384_SHA384_ASN1,
            &verify::ECDSA_P384_SHA384_ASN1,
            &[0x06, 0x05, 0x2b, 0x81, 0x04, 0x00, 0x22],
            48,
        ),
        _ => return Err(CryptoError::UnsupportedSignatureScheme),
    };
    Ok((
        Ecdsa {
            signing,
            verification,
            curve,
        },
        scalar_len,
    ))
}

fn hmac_algorithm(hash_type: HashType) -> &'static hmac::Algorithm {
    match hash_type {
        HashType::Sha2_256 => &hmac::HMAC_SHA256,
        HashType::Sha2_384 => &hmac::HMAC_SHA384,
        HashType::Sha2_512 => &hmac::HMAC_SHA512,
    }
}

fn aead_key(
    alg: AeadType,
    key: &[u8],
    nonce: &[u8],
) -> Result<(aead::Key, aead::Nonce), CryptoError> {
    let algorithm = match alg {
        AeadType::Aes128Gcm => &aead::AES_128_GCM,
        AeadType::Aes256Gcm => &aead::AES_256_GCM,
        AeadType::ChaCha20Poly1305 => &aead::CHACHA20_POLY1305,
    };
    let key = aead::Key::new(algorithm, key).map_err(|_| CryptoError::CryptoLibraryError)?;
    let nonce = nonce
        .try_into()
        .map_err(|_| CryptoError::CryptoLibraryError)?;
    Ok((key, aead::Nonce::assume_unique_for_key(nonce)))
}

/// Returns a buffer for an export of `len` bytes, refusing one longer than
/// RFC 9180 allows, 255 of the KDF's hash outputs, before allocating it.
fn exporter_buffer(config: &HpkeConfig, len: usize) -> Result<Vec<u8>, CryptoError> {
    let hash_len = match config.1 {
        HpkeKdfType::HkdfSha256 => 32,
        HpkeKdfType::HkdfSha384 => 48,
        HpkeKdfType::HkdfSha512 => 64,
    };
    if len > 255 * hash_len {
        return Err(CryptoError::ExporterError);
    }
    Ok(vec![0; len])
}

fn hpke_kdf(kdf: HpkeKdfType) -> &'static hpke::Kdf {
    match kdf {
        HpkeKdfType::HkdfSha256 => &hpke::HKDF_SHA256,
        HpkeKdfType::HkdfSha384 => &hpke::HKDF_SHA384,
        HpkeKdfType::HkdfSha512 => &hpke::HKDF_SHA512,
    }
}

/// Returns `config`'s KEM, and its suite unless its AEAD is export-only.
/// P-521, like openmls_rust_crypto, is unsupported.
fn hpke_suite(
    config: &HpkeConfig,
) -> Result<(&'static hpke::Kem, Option<hpke::Suite>), CryptoError> {
    let kem = match config.0 {
        HpkeKemType::DhKemP256 => &hpke::DHKEM_P256_HKDF_SHA256,
        HpkeKemType::DhKemP384 => &hpke::DHKEM_P384_HKDF_SHA384,
        HpkeKemType::DhKem25519 => &hpke::DHKEM_X25519_HKDF_SHA256,
        _ => return Err(CryptoError::UnsupportedCiphersuite),
    };
    let aead = match config.2 {
        HpkeAeadType::AesGcm128 => &hpke::AES_128_GCM,
        HpkeAeadType::AesGcm256 => &hpke::AES_256_GCM,
        HpkeAeadType::ChaCha20Poly1305 => &hpke::CHACHA20_POLY1305,
        HpkeAeadType::Export => return Ok((kem, None)),
    };
    Ok((
        kem,
        Some(hpke::Suite {
            kdf: hpke_kdf(config.1),
            aead,
        }),
    ))
}
