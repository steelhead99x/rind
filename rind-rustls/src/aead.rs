use rind::aead;
use rustls::crypto::cipher::{
    AeadKey, InboundOpaqueMessage, InboundPlainMessage, Iv, MessageDecrypter, MessageEncrypter,
    Nonce, OutboundOpaqueMessage, OutboundPlainMessage, PrefixedPayload, Tls13AeadAlgorithm,
    UnsupportedOperationError, make_tls13_aad,
};
#[cfg(feature = "tls12")]
use rustls::crypto::cipher::{KeyBlockShape, NONCE_LEN, Tls12AeadAlgorithm, make_tls12_aad};
use rustls::{ConnectionTrafficSecrets, ContentType, ProtocolVersion};

/// rustls derives `key` at the algorithm's key length.
fn aead_key(algorithm: &'static aead::Algorithm, key: &AeadKey) -> aead::Key {
    aead::Key::new(algorithm, key.as_ref()).unwrap()
}

/// The record nonce for `seq`, which never repeats under one key.
fn nonce(iv: &Iv, seq: u64) -> aead::Nonce {
    aead::Nonce::assume_unique_for_key(Nonce::new(iv, seq).0)
}

pub struct Chacha20Poly1305;

impl Tls13AeadAlgorithm for Chacha20Poly1305 {
    fn encrypter(&self, key: AeadKey, iv: Iv) -> Box<dyn MessageEncrypter> {
        Box::new(Tls13Cipher(aead_key(&aead::CHACHA20_POLY1305, &key), iv))
    }

    fn decrypter(&self, key: AeadKey, iv: Iv) -> Box<dyn MessageDecrypter> {
        Box::new(Tls13Cipher(aead_key(&aead::CHACHA20_POLY1305, &key), iv))
    }

    fn key_len(&self) -> usize {
        aead::CHACHA20_POLY1305.key_len()
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        iv: Iv,
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        Ok(ConnectionTrafficSecrets::Chacha20Poly1305 { key, iv })
    }
}

#[cfg(feature = "tls12")]
impl Tls12AeadAlgorithm for Chacha20Poly1305 {
    fn encrypter(&self, key: AeadKey, iv: &[u8], _: &[u8]) -> Box<dyn MessageEncrypter> {
        Box::new(ChaChaTls12Cipher(
            aead_key(&aead::CHACHA20_POLY1305, &key),
            Iv::copy(iv),
        ))
    }

    fn decrypter(&self, key: AeadKey, iv: &[u8]) -> Box<dyn MessageDecrypter> {
        Box::new(ChaChaTls12Cipher(
            aead_key(&aead::CHACHA20_POLY1305, &key),
            Iv::copy(iv),
        ))
    }

    fn key_block_shape(&self) -> KeyBlockShape {
        KeyBlockShape {
            enc_key_len: aead::CHACHA20_POLY1305.key_len(),
            fixed_iv_len: 12,
            explicit_nonce_len: 0,
        }
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        iv: &[u8],
        _explicit: &[u8],
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        // This should always be true because KeyBlockShape and the Iv nonce len are in agreement.
        debug_assert_eq!(NONCE_LEN, iv.len());
        Ok(ConnectionTrafficSecrets::Chacha20Poly1305 {
            key,
            iv: Iv::new(iv[..].try_into().unwrap()),
        })
    }
}

/// TLS 1.3 record protection, which is the same for every AEAD.
struct Tls13Cipher(aead::Key, Iv);

impl MessageEncrypter for Tls13Cipher {
    fn encrypt(
        &mut self,
        m: OutboundPlainMessage<'_>,
        seq: u64,
    ) -> Result<OutboundOpaqueMessage, rustls::Error> {
        let total_len = self.encrypted_payload_len(m.payload.len());
        let mut payload = PrefixedPayload::with_capacity(total_len);

        payload.extend_from_chunks(&m.payload);
        payload.extend_from_slice(&m.typ.to_array());
        let aad = make_tls13_aad(total_len);

        let tag = self
            .0
            .seal_in_place_separate_tag(nonce(&self.1, seq), &aad, payload.as_mut())
            .map_err(|_| rustls::Error::EncryptError)?;
        payload.extend_from_slice(tag.as_ref());

        Ok(OutboundOpaqueMessage::new(
            ContentType::ApplicationData,
            ProtocolVersion::TLSv1_2, // sic
            payload,
        ))
    }

    fn encrypted_payload_len(&self, payload_len: usize) -> usize {
        payload_len + 1 + TAG_LEN
    }
}

impl MessageDecrypter for Tls13Cipher {
    fn decrypt<'a>(
        &mut self,
        mut m: InboundOpaqueMessage<'a>,
        seq: u64,
    ) -> Result<InboundPlainMessage<'a>, rustls::Error> {
        let payload = &mut m.payload;
        let aad = make_tls13_aad(payload.len());
        let plain_len = self
            .0
            .open_in_place(nonce(&self.1, seq), &aad, payload)
            .map_err(|_| rustls::Error::DecryptError)?
            .len();

        payload.truncate(plain_len);
        m.into_tls13_unpadded_message()
    }
}

#[cfg(feature = "tls12")]
struct ChaChaTls12Cipher(aead::Key, Iv);

#[cfg(feature = "tls12")]
impl MessageEncrypter for ChaChaTls12Cipher {
    fn encrypt(
        &mut self,
        m: OutboundPlainMessage<'_>,
        seq: u64,
    ) -> Result<OutboundOpaqueMessage, rustls::Error> {
        let total_len = self.encrypted_payload_len(m.payload.len());
        let mut payload = PrefixedPayload::with_capacity(total_len);

        payload.extend_from_chunks(&m.payload);
        let aad = make_tls12_aad(seq, m.typ, m.version, m.payload.len());

        let tag = self
            .0
            .seal_in_place_separate_tag(nonce(&self.1, seq), &aad, payload.as_mut())
            .map_err(|_| rustls::Error::EncryptError)?;
        payload.extend_from_slice(tag.as_ref());

        Ok(OutboundOpaqueMessage::new(m.typ, m.version, payload))
    }

    fn encrypted_payload_len(&self, payload_len: usize) -> usize {
        payload_len + TAG_LEN
    }
}

#[cfg(feature = "tls12")]
impl MessageDecrypter for ChaChaTls12Cipher {
    fn decrypt<'a>(
        &mut self,
        mut m: InboundOpaqueMessage<'a>,
        seq: u64,
    ) -> Result<InboundPlainMessage<'a>, rustls::Error> {
        let cipher_len = m
            .payload
            .len()
            .checked_sub(TAG_LEN)
            .ok_or(rustls::Error::DecryptError)?;
        let aad = make_tls12_aad(seq, m.typ, m.version, cipher_len);
        self.0
            .open_in_place(nonce(&self.1, seq), &aad, &mut m.payload)
            .map_err(|_| rustls::Error::DecryptError)?;

        if cipher_len > MAX_FRAGMENT_LEN {
            return Err(rustls::Error::PeerSentOversizedRecord);
        }

        m.payload.truncate(cipher_len);
        Ok(m.into_plain_message())
    }
}

pub struct TlsAesGcm {
    algorithm: &'static aead::Algorithm,
    traffic_secrets: fn(AeadKey, Iv) -> ConnectionTrafficSecrets,
}

/// TLS record protection with AES-128-GCM.
pub static AES_128_GCM: TlsAesGcm = TlsAesGcm {
    algorithm: &aead::AES_128_GCM,
    traffic_secrets: |key, iv| ConnectionTrafficSecrets::Aes128Gcm { key, iv },
};

/// TLS record protection with AES-256-GCM.
pub static AES_256_GCM: TlsAesGcm = TlsAesGcm {
    algorithm: &aead::AES_256_GCM,
    traffic_secrets: |key, iv| ConnectionTrafficSecrets::Aes256Gcm { key, iv },
};

impl Tls13AeadAlgorithm for TlsAesGcm {
    fn encrypter(&self, key: AeadKey, iv: Iv) -> Box<dyn MessageEncrypter> {
        Box::new(Tls13Cipher(aead_key(self.algorithm, &key), iv))
    }

    fn decrypter(&self, key: AeadKey, iv: Iv) -> Box<dyn MessageDecrypter> {
        Box::new(Tls13Cipher(aead_key(self.algorithm, &key), iv))
    }

    fn key_len(&self) -> usize {
        self.algorithm.key_len()
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        iv: Iv,
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        Ok((self.traffic_secrets)(key, iv))
    }
}

#[cfg(feature = "tls12")]
impl Tls12AeadAlgorithm for TlsAesGcm {
    fn encrypter(
        &self,
        key: AeadKey,
        write_iv: &[u8],
        explicit: &[u8],
    ) -> Box<dyn MessageEncrypter> {
        let iv = gcm_iv(write_iv, explicit);
        Box::new(GcmTls12MessageEncrypter(aead_key(self.algorithm, &key), iv))
    }

    fn decrypter(&self, key: AeadKey, iv: &[u8]) -> Box<dyn MessageDecrypter> {
        Box::new(GcmTls12MessageDecrypter(
            aead_key(self.algorithm, &key),
            iv.try_into().unwrap(),
        ))
    }

    fn key_block_shape(&self) -> KeyBlockShape {
        KeyBlockShape {
            enc_key_len: self.algorithm.key_len(),
            fixed_iv_len: 4,
            explicit_nonce_len: 8,
        }
    }

    fn extract_keys(
        &self,
        key: AeadKey,
        iv: &[u8],
        explicit: &[u8],
    ) -> Result<ConnectionTrafficSecrets, UnsupportedOperationError> {
        Ok((self.traffic_secrets)(key, gcm_iv(iv, explicit)))
    }
}

#[cfg(feature = "tls12")]
struct GcmTls12MessageDecrypter(aead::Key, [u8; 4]);

#[cfg(feature = "tls12")]
impl MessageDecrypter for GcmTls12MessageDecrypter {
    fn decrypt<'a>(
        &mut self,
        mut msg: InboundOpaqueMessage<'a>,
        seq: u64,
    ) -> Result<InboundPlainMessage<'a>, rustls::Error> {
        let payload = &msg.payload;
        if payload.len() < AESGCM_OVERHEAD {
            return Err(rustls::Error::DecryptError);
        }

        let nonce = {
            let mut nonce = [0u8; 12];
            nonce[..4].copy_from_slice(&self.1);
            nonce[4..].copy_from_slice(&payload[..8]);
            // The peer picks the explicit part; opening needs no uniqueness.
            aead::Nonce::assume_unique_for_key(nonce)
        };

        let plain_len = payload.len() - AESGCM_OVERHEAD;
        let aad = make_tls12_aad(seq, msg.typ, msg.version, plain_len);

        let payload = &mut msg.payload;
        let (_explicit_iv, sealed) = payload.split_at_mut(AESGCM_EXPLICIT_NONCE_LEN);
        self.0
            .open_in_place(nonce, &aad, sealed)
            .map_err(|_| rustls::Error::DecryptError)?;

        if plain_len > MAX_FRAGMENT_LEN {
            return Err(rustls::Error::PeerSentOversizedRecord);
        }

        Ok(msg.into_plain_message_range(
            AESGCM_EXPLICIT_NONCE_LEN..AESGCM_EXPLICIT_NONCE_LEN + plain_len,
        ))
    }
}

#[cfg(feature = "tls12")]
struct GcmTls12MessageEncrypter(aead::Key, Iv);

#[cfg(feature = "tls12")]
impl MessageEncrypter for GcmTls12MessageEncrypter {
    fn encrypt(
        &mut self,
        msg: OutboundPlainMessage<'_>,
        seq: u64,
    ) -> Result<OutboundOpaqueMessage, rustls::Error> {
        let total_len = self.encrypted_payload_len(msg.payload.len());
        let mut payload = PrefixedPayload::with_capacity(total_len);

        let nonce = Nonce::new(&self.1, seq);
        let aad = make_tls12_aad(seq, msg.typ, msg.version, msg.payload.len());
        payload.extend_from_slice(&nonce.0[4..]);
        payload.extend_from_chunks(&msg.payload);

        let tag = self
            .0
            .seal_in_place_separate_tag(
                aead::Nonce::assume_unique_for_key(nonce.0),
                &aad,
                &mut payload.as_mut()[AESGCM_EXPLICIT_NONCE_LEN..],
            )
            .map_err(|_| rustls::Error::EncryptError)?;
        payload.extend_from_slice(tag.as_ref());

        Ok(OutboundOpaqueMessage::new(msg.typ, msg.version, payload))
    }

    fn encrypted_payload_len(&self, payload_len: usize) -> usize {
        payload_len + AESGCM_EXPLICIT_NONCE_LEN + TAG_LEN
    }
}

#[cfg(feature = "tls12")]
fn gcm_iv(write_iv: &[u8], explicit: &[u8]) -> Iv {
    debug_assert_eq!(write_iv.len(), 4);
    debug_assert_eq!(explicit.len(), 8);

    // The GCM nonce is constructed from a 32-bit 'salt' derived
    // from the master-secret, and a 64-bit explicit part,
    // with no specified construction.  Thanks for that.
    //
    // We use the same construction as TLS1.3/ChaCha20Poly1305:
    // a starting point extracted from the key block, xored with
    // the sequence number.
    let mut iv = [0; NONCE_LEN];
    iv[..4].copy_from_slice(write_iv);
    iv[4..].copy_from_slice(explicit);

    Iv::new(iv)
}

const TAG_LEN: usize = 16;

#[cfg(feature = "tls12")]
const MAX_FRAGMENT_LEN: usize = 16384;

#[cfg(feature = "tls12")]
// TLS1.2-specific
const AESGCM_EXPLICIT_NONCE_LEN: usize = 8;
#[cfg(feature = "tls12")]
const AESGCM_OVERHEAD: usize = AESGCM_EXPLICIT_NONCE_LEN + TAG_LEN;

#[cfg(test)]
mod tests {
    use rustls::Error;

    use super::*;

    fn random_bytes<const L: usize>() -> Result<[u8; L], Error> {
        let mut bytes = [0; L];
        rind::rand::fill(&mut bytes).map_err(|_| rustls::crypto::GetRandomFailed)?;
        Ok(bytes)
    }

    #[test]
    fn test_chacha20_poly1305_tls13() {
        let cipher = Chacha20Poly1305;
        assert_eq!(cipher.key_len(), 32);
        let cipher_key = random_bytes::<32>().unwrap();
        let cipher_iv = random_bytes::<12>().unwrap();
        match rustls::crypto::cipher::Tls13AeadAlgorithm::extract_keys(
            &cipher,
            AeadKey::from(cipher_key),
            Iv::from(cipher_iv),
        )
        .unwrap()
        {
            ConnectionTrafficSecrets::Chacha20Poly1305 { key, iv } => {
                assert_eq!(key.as_ref(), cipher_key);
                assert_eq!(iv.as_ref(), cipher_iv);
            }
            _ => panic!("Unexpected secret type extracted from ChaCha20-Poly1305 cipher"),
        }
    }

    #[cfg(feature = "tls12")]
    #[test]
    fn test_chacha20_poly1305_tls12() {
        let cipher = Chacha20Poly1305;
        assert_eq!(cipher.key_len(), 32);
        let cipher_key = random_bytes::<32>().unwrap();
        let cipher_iv = random_bytes::<12>().unwrap();
        let unused = [0u8; 1];
        match rustls::crypto::cipher::Tls12AeadAlgorithm::extract_keys(
            &cipher,
            AeadKey::from(cipher_key),
            &cipher_iv,
            &unused,
        )
        .unwrap()
        {
            ConnectionTrafficSecrets::Chacha20Poly1305 { key, iv } => {
                assert_eq!(key.as_ref(), cipher_key);
                assert_eq!(iv.as_ref(), cipher_iv);
            }
            _ => panic!("Unexpected secret type extracted from ChaCha20-Poly1305 cipher"),
        }
    }

    #[test]
    fn test_aes_gcm_tls13() {
        fn test_aes_gcm_tls13(key_bits: usize) {
            let key_bytes = key_bits / 8;
            let cipher = if key_bits == 128 {
                &AES_128_GCM
            } else {
                &AES_256_GCM
            };
            assert_eq!(cipher.key_len(), key_bytes);
            let cipher_key = &random_bytes::<32>().unwrap();
            let cipher_iv = random_bytes::<12>().unwrap();
            match Tls13AeadAlgorithm::extract_keys(
                cipher,
                AeadKey::from(*cipher_key),
                Iv::from(cipher_iv),
            )
            .unwrap()
            {
                ConnectionTrafficSecrets::Aes128Gcm { key, iv } => {
                    assert_eq!(key_bits, 128);
                    assert_eq!(key.as_ref(), cipher_key);
                    assert_eq!(iv.as_ref(), cipher_iv);
                }
                ConnectionTrafficSecrets::Aes256Gcm { key, iv } => {
                    assert_eq!(key_bits, 256);
                    assert_eq!(key.as_ref(), cipher_key);
                    assert_eq!(iv.as_ref(), cipher_iv);
                }
                _ => panic!(
                    "Unexpected secret type extracted from AES{}-GCM cipher",
                    key_bits
                ),
            }
        }

        test_aes_gcm_tls13(128);
        test_aes_gcm_tls13(256);
    }

    #[cfg(feature = "tls12")]
    #[test]
    fn test_aes_gcm_tls12() {
        fn test_aes_gcm_tls12(key_bits: usize) {
            let key_bytes = key_bits / 8;
            let cipher = if key_bits == 128 {
                &AES_128_GCM
            } else {
                &AES_256_GCM
            };
            assert_eq!(cipher.key_len(), key_bytes);
            let cipher_key = &random_bytes::<32>().unwrap();
            let cipher_iv = random_bytes::<4>().unwrap();
            let cipher_explicit = random_bytes::<8>().unwrap();
            match Tls12AeadAlgorithm::extract_keys(
                cipher,
                AeadKey::from(*cipher_key),
                &cipher_iv,
                &cipher_explicit,
            )
            .unwrap()
            {
                ConnectionTrafficSecrets::Aes128Gcm { key, iv } => {
                    assert_eq!(key_bits, 128);
                    assert_eq!(key.as_ref(), cipher_key);
                    assert_eq!(iv.as_ref().len(), 12);
                }
                ConnectionTrafficSecrets::Aes256Gcm { key, iv } => {
                    assert_eq!(key_bits, 256);
                    assert_eq!(key.as_ref(), cipher_key);
                    assert_eq!(iv.as_ref().len(), 12);
                }
                _ => panic!(
                    "Unexpected secret type extracted from AES{}-GCM cipher",
                    key_bits
                ),
            }
        }

        test_aes_gcm_tls12(128);
        test_aes_gcm_tls12(256);
    }

    /// rustls bounds TLS 1.2 plaintext only through the decrypter, so each
    /// must refuse a record over 2^14 bytes that its encrypter would seal.
    #[cfg(feature = "tls12")]
    #[test]
    fn tls12_refuses_oversized_records() {
        // rustls only builds a 32-byte `AeadKey`; AES-128-GCM shares the GCM decrypter.
        let algorithms: [&dyn Tls12AeadAlgorithm; 2] = [&Chacha20Poly1305, &AES_256_GCM];
        for algorithm in algorithms {
            let shape = algorithm.key_block_shape();
            let key = random_bytes::<32>().unwrap();
            let block = random_bytes::<20>().unwrap();
            let (iv, explicit) = block.split_at(shape.fixed_iv_len);
            let explicit = &explicit[..shape.explicit_nonce_len];
            let mut encrypter = algorithm.encrypter(AeadKey::from(key), iv, explicit);
            let mut decrypter = algorithm.decrypter(AeadKey::from(key), iv);

            for (seq, len) in [MAX_FRAGMENT_LEN, MAX_FRAGMENT_LEN + 1]
                .into_iter()
                .enumerate()
            {
                let plain = vec![0x42; len];
                let sealed = encrypter
                    .encrypt(
                        OutboundPlainMessage {
                            typ: ContentType::ApplicationData,
                            version: ProtocolVersion::TLSv1_2,
                            payload: plain.as_slice().into(),
                        },
                        seq as u64,
                    )
                    .unwrap();
                let mut payload = sealed.payload.as_ref().to_vec();
                let opened = decrypter.decrypt(
                    InboundOpaqueMessage::new(sealed.typ, sealed.version, &mut payload),
                    seq as u64,
                );

                match opened {
                    Ok(m) => assert!(
                        len <= MAX_FRAGMENT_LEN && m.payload == plain,
                        "{len}-byte record opened"
                    ),
                    Err(e) => assert!(
                        len > MAX_FRAGMENT_LEN && e == Error::PeerSentOversizedRecord,
                        "{len}-byte record: {e:?}"
                    ),
                }
            }
        }
    }
}
