use rind::aead::{self, quic::SAMPLE_LEN};
use rustls::Error;
use rustls::crypto::cipher::{AeadKey, Iv, Nonce};
use rustls::quic;

/// QUIC packet and header protection for one cipher suite.
pub(crate) struct Algorithm {
    packet: &'static aead::Algorithm,
    header: &'static aead::quic::Algorithm,
    // RFC 9001 section 6.6
    confidentiality_limit: u64,
    integrity_limit: u64,
}

/// QUIC protection with AES-128-GCM.
pub(crate) static AES_128_GCM: Algorithm = Algorithm {
    packet: &aead::AES_128_GCM,
    header: &aead::quic::AES_128,
    confidentiality_limit: 1 << 23,
    integrity_limit: 1 << 52,
};

/// QUIC protection with AES-256-GCM.
pub(crate) static AES_256_GCM: Algorithm = Algorithm {
    packet: &aead::AES_256_GCM,
    header: &aead::quic::AES_256,
    confidentiality_limit: 1 << 23,
    integrity_limit: 1 << 52,
};

/// QUIC protection with ChaCha20-Poly1305.
pub(crate) static CHACHA20_POLY1305: Algorithm = Algorithm {
    packet: &aead::CHACHA20_POLY1305,
    header: &aead::quic::CHACHA20,
    confidentiality_limit: u64::MAX,
    integrity_limit: 1 << 36,
};

impl quic::Algorithm for Algorithm {
    fn packet_key(&self, key: AeadKey, iv: Iv) -> Box<dyn quic::PacketKey> {
        Box::new(PacketKey {
            key: aead::Key::new(self.packet, key.as_ref()).unwrap(),
            iv,
            confidentiality_limit: self.confidentiality_limit,
            integrity_limit: self.integrity_limit,
        })
    }

    fn header_protection_key(&self, key: AeadKey) -> Box<dyn quic::HeaderProtectionKey> {
        Box::new(HeaderProtectionKey(
            aead::quic::HeaderProtectionKey::new(self.header, key.as_ref()).unwrap(),
        ))
    }

    fn aead_key_len(&self) -> usize {
        self.packet.key_len()
    }
}

struct PacketKey {
    key: aead::Key,
    iv: Iv,
    confidentiality_limit: u64,
    integrity_limit: u64,
}

impl quic::PacketKey for PacketKey {
    fn encrypt_in_place(
        &self,
        packet_number: u64,
        header: &[u8],
        payload: &mut [u8],
    ) -> Result<quic::Tag, Error> {
        let nonce = aead::Nonce::assume_unique_for_key(Nonce::new(&self.iv, packet_number).0);
        let tag = self
            .key
            .seal_in_place_separate_tag(nonce, header, payload)
            .map_err(|_| Error::EncryptError)?;
        Ok(quic::Tag::from(tag.as_ref()))
    }

    fn decrypt_in_place<'a>(
        &self,
        packet_number: u64,
        header: &[u8],
        payload: &'a mut [u8],
    ) -> Result<&'a [u8], Error> {
        let nonce = aead::Nonce::assume_unique_for_key(Nonce::new(&self.iv, packet_number).0);
        let plain = self
            .key
            .open_in_place(nonce, header, payload)
            .map_err(|_| Error::DecryptError)?;
        Ok(plain)
    }

    fn tag_len(&self) -> usize {
        TAG_LEN
    }

    fn confidentiality_limit(&self) -> u64 {
        self.confidentiality_limit
    }

    fn integrity_limit(&self) -> u64 {
        self.integrity_limit
    }
}

struct HeaderProtectionKey(aead::quic::HeaderProtectionKey);

impl HeaderProtectionKey {
    /// RFC 9001 section 5.4.1, leaving `first` and `packet_number` unchanged on error.
    fn xor_in_place(
        &self,
        sample: &[u8],
        first: &mut u8,
        packet_number: &mut [u8],
        masked: bool,
    ) -> Result<(), Error> {
        let sample: &[u8; SAMPLE_LEN] = sample
            .try_into()
            .map_err(|_| Error::General("sample of invalid length".into()))?;
        let [first_mask, pn_mask @ ..] = self.0.mask(sample);
        if packet_number.len() > pn_mask.len() {
            return Err(Error::General("packet number too long".into()));
        }

        // Long headers protect 4 bits of the first byte, short headers 5.
        let bits = match *first & 0x80 {
            0 => 0x1f,
            _ => 0x0f,
        };
        // The packet number length is in the unprotected first byte.
        let first_plain = match masked {
            true => *first ^ (first_mask & bits),
            false => *first,
        };
        let pn_len = (first_plain & 0x03) as usize + 1;

        *first ^= first_mask & bits;
        for (pn, mask) in packet_number.iter_mut().zip(pn_mask).take(pn_len) {
            *pn ^= mask;
        }
        Ok(())
    }
}

impl quic::HeaderProtectionKey for HeaderProtectionKey {
    fn encrypt_in_place(
        &self,
        sample: &[u8],
        first: &mut u8,
        packet_number: &mut [u8],
    ) -> Result<(), Error> {
        self.xor_in_place(sample, first, packet_number, false)
    }

    fn decrypt_in_place(
        &self,
        sample: &[u8],
        first: &mut u8,
        packet_number: &mut [u8],
    ) -> Result<(), Error> {
        self.xor_in_place(sample, first, packet_number, true)
    }

    fn sample_len(&self) -> usize {
        SAMPLE_LEN
    }
}

const TAG_LEN: usize = 16;

#[cfg(test)]
mod tests {
    use rustls::Side;
    use rustls::SupportedCipherSuite;
    use rustls::quic::{Algorithm as _, DirectionalKeys, Keys, Version};

    use super::*;
    use crate::cipher_suite;

    fn initial_keys(suite: SupportedCipherSuite, side: Side) -> Keys {
        // RFC 9001 appendix A.1
        let dcid = hex::decode("8394c8f03e515708").unwrap();
        let suite = suite.tls13().unwrap().quic_suite().unwrap();
        suite.keys(&dcid, side, Version::V1)
    }

    /// Adds or removes header protection on `packet`, whose packet number starts at `pn_offset`.
    fn header_protection(
        key: &dyn quic::HeaderProtectionKey,
        packet: &mut [u8],
        pn_offset: usize,
        protect: bool,
    ) {
        // The sample assumes a 4-byte packet number (RFC 9001 section 5.4.2).
        let (header, rest) = packet.split_at_mut(pn_offset + 4);
        let sample = &rest[..key.sample_len()];
        let (first, rest) = header.split_first_mut().unwrap();
        let packet_number = &mut rest[pn_offset - 1..];
        match protect {
            true => key.encrypt_in_place(sample, first, packet_number),
            false => key.decrypt_in_place(sample, first, packet_number),
        }
        .unwrap();
    }

    /// Protects a packet with `send`, compares it to `expected`, then unprotects it with `recv`.
    fn check_packet(
        send: &DirectionalKeys,
        recv: &DirectionalKeys,
        packet_number: u64,
        header: &str,
        payload: &str,
        expected: &str,
    ) {
        let (header, payload) = (hex::decode(header).unwrap(), hex::decode(payload).unwrap());
        let pn_offset = header.len() - 1 - (header[0] & 0x03) as usize;

        let mut packet = [&header[..], &payload[..]].concat();
        let (head, body) = packet.split_at_mut(header.len());
        let tag = send
            .packet
            .encrypt_in_place(packet_number, head, body)
            .unwrap();
        packet.extend_from_slice(tag.as_ref());
        header_protection(&*send.header, &mut packet, pn_offset, true);
        assert_eq!(hex::encode(&packet), expected);

        header_protection(&*recv.header, &mut packet, pn_offset, false);
        let (head, body) = packet.split_at_mut(header.len());
        assert_eq!(head, &header[..]);
        let plain = recv
            .packet
            .decrypt_in_place(packet_number, head, body)
            .unwrap();
        assert_eq!(plain, &payload[..]);
    }

    #[test]
    fn aes128_limits_match_aes256() {
        // Both AES suites use the same bounds. A mutant of one suite's shift
        // no longer matches the other, and the public test checks AES-256
        // against rustls's aws-lc-rs provider.
        assert_eq!(
            AES_128_GCM.confidentiality_limit,
            AES_256_GCM.confidentiality_limit
        );
        assert_eq!(AES_128_GCM.integrity_limit, AES_256_GCM.integrity_limit);
    }

    #[test]
    fn rfc9001_client_initial_header() {
        // RFC 9001 appendix A.2, header protection only: the payload is padded to 1162 bytes.
        let keys = initial_keys(cipher_suite::TLS13_AES_128_GCM_SHA256, Side::Client);
        let sample = hex::decode("d1b1c98dd7689fb8ec11d242b123dc9b").unwrap();
        let (mut first, mut packet_number) = (0xc3, [0x00, 0x00, 0x00, 0x02]);

        keys.local
            .header
            .encrypt_in_place(&sample, &mut first, &mut packet_number)
            .unwrap();
        assert_eq!((first, packet_number), (0xc0, [0x7b, 0x9a, 0xec, 0x34]));
    }

    #[test]
    fn rfc9001_server_initial() {
        // RFC 9001 appendix A.3
        check_packet(
            &initial_keys(cipher_suite::TLS13_AES_128_GCM_SHA256, Side::Server).local,
            &initial_keys(cipher_suite::TLS13_AES_128_GCM_SHA256, Side::Client).remote,
            1,
            "c1000000010008f067a5502a4262b50040750001",
            "02000000000600405a020000560303eefce7f7b37ba1d1632e96677825ddf739\
             88cfc79825df566dc5430b9a045a1200130100002e00330024001d00209d3c94\
             0d89690b84d08a60993c144eca684d1081287c834d5311bcf32bb9da1a002b00\
             020304",
            "cf000000010008f067a5502a4262b5004075c0d95a482cd0991cd25b0aac406a\
             5816b6394100f37a1c69797554780bb38cc5a99f5ede4cf73c3ec2493a1839b3\
             dbcba3f6ea46c5b7684df3548e7ddeb9c3bf9c73cc3f3bded74b562bfb19fb84\
             022f8ef4cdd93795d77d06edbb7aaf2f58891850abbdca3d20398c276456cbc4\
             2158407dd074ee",
        );
    }

    #[test]
    fn rfc9001_chacha20_short_header() {
        // RFC 9001 appendix A.5
        let keys = || {
            let key = "c6d98ff3441c3fe1b2182094f69caa2ed4b716b65488960a7a984979fb23e1c8";
            let iv = "e0459b3474bdd0e44a41c144";
            let hp = "25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4";
            let key: [u8; 32] = hex::decode(key).unwrap().try_into().unwrap();
            let iv: [u8; 12] = hex::decode(iv).unwrap().try_into().unwrap();
            let hp: [u8; 32] = hex::decode(hp).unwrap().try_into().unwrap();
            DirectionalKeys {
                packet: CHACHA20_POLY1305.packet_key(AeadKey::from(key), Iv::new(iv)),
                header: CHACHA20_POLY1305.header_protection_key(AeadKey::from(hp)),
            }
        };
        check_packet(
            &keys(),
            &keys(),
            654360564,
            "4200bff4",
            "01",
            "4cfe4189655e5cd55c41f69080575d7999c25a5bfb",
        );
    }

    #[test]
    fn rejects_malformed_input() {
        for suite in [
            cipher_suite::TLS13_AES_128_GCM_SHA256,
            cipher_suite::TLS13_AES_256_GCM_SHA384,
            cipher_suite::TLS13_CHACHA20_POLY1305_SHA256,
        ] {
            let keys = initial_keys(suite, Side::Client).local;

            // A bad sample or an overlong packet number changes nothing.
            let (mut first, mut packet_number) = (0xc3, [0u8; 4]);
            let header = &keys.header;
            assert!(
                header
                    .encrypt_in_place(&[0; 15], &mut first, &mut packet_number)
                    .is_err()
            );
            assert!(
                header
                    .decrypt_in_place(&[0; 17], &mut first, &mut packet_number)
                    .is_err()
            );
            assert!(
                header
                    .encrypt_in_place(&[0; 16], &mut first, &mut [0; 5])
                    .is_err()
            );
            assert_eq!((first, packet_number), (0xc3, [0; 4]));

            let mut sealed = b"payload".to_vec();
            let tag = keys
                .packet
                .encrypt_in_place(7, b"header", &mut sealed)
                .unwrap();
            sealed.extend_from_slice(tag.as_ref());
            let open = |packet_number, header: &[u8], sealed: &[u8]| {
                let mut sealed = sealed.to_vec();
                let plain = keys
                    .packet
                    .decrypt_in_place(packet_number, header, &mut sealed);
                plain.map(<[u8]>::to_vec)
            };
            assert_eq!(open(7, b"header", &sealed).unwrap(), b"payload");
            assert!(open(8, b"header", &sealed).is_err());
            assert!(open(7, b"headex", &sealed).is_err());
            assert!(open(7, b"header", &sealed[..TAG_LEN - 1]).is_err());
        }
    }
}
