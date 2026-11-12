//! Known-answer tests from RFC 3711 (AES-CM and its key derivation) and
//! RFC 7714 (AEAD-AES-GCM for SRTP and SRTCP), plus the inputs str0m's
//! callers can hand a cipher that must be refused rather than panic.

use str0m::crypto::{AeadAes128Gcm, SrtpProvider};

fn srtp() -> &'static dyn SrtpProvider {
    rind_str0m::default_provider().srtp_provider
}

fn hex(s: &str) -> Vec<u8> {
    let s: String = s.split_whitespace().collect();
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn array<const N: usize>(s: &str) -> [u8; N] {
    hex(s).try_into().unwrap()
}

/// RFC 3711 appendix B.2: the keystream over a full 16-bit block counter.
#[test]
fn rfc3711_aes_cm_keystream() {
    let key = array("2B7E151628AED2A6ABF7158809CF4F3C");
    let iv = array("F0F1F2F3F4F5F6F7F8F9FAFBFCFD0000");
    let blocks = 0xff02;

    let mut cipher = srtp().aes_128_cm_sha1_80().create_cipher(key, true);
    let input = vec![0u8; blocks * 16];
    let mut keystream = vec![0u8; blocks * 16];
    cipher.encrypt(&iv, &input, &mut keystream).unwrap();

    let block = |i: usize| &keystream[i * 16..][..16];
    assert_eq!(block(0x0000), hex("E03EAD0935C95E80E166B16DD92B4EB4"));
    assert_eq!(block(0x0001), hex("D23513162B02D0F72A43A2FE4A5F97AB"));
    assert_eq!(block(0x0002), hex("41E95B3BB0A2E8DD477901E4FCA894C0"));
    assert_eq!(block(0xfeff), hex("EC8CDF7398607CB0F2D21675EA9EA1E4"));
    assert_eq!(block(0xff00), hex("362B7C3C6773516318A077D7FC5073AE"));
    assert_eq!(block(0xff01), hex("6A2CC3787889374FBEB4C81B17BA6C44"));

    let mut decrypted = vec![0u8; keystream.len()];
    cipher.decrypt(&iv, &keystream, &mut decrypted).unwrap();
    assert_eq!(decrypted, input);
}

/// RFC 3711 appendix B.3: each AES input block of the key derivation and its output.
#[test]
fn rfc3711_key_derivation() {
    let master = hex("E1F97A0D3E018BE0D64FA32C06DE4139");
    let rounds = [
        // Cipher key.
        (
            "0EC675AD498AFEEBB6960B3AABE60000",
            "C61E7A93744F39EE10734AFE3FF7A087",
        ),
        // Cipher salt.
        (
            "0EC675AD498AFEE9B6960B3AABE60000",
            "30CBBC08863D8C85D49DB34A9AE17AC6",
        ),
        // Auth key.
        (
            "0EC675AD498AFEEAB6960B3AABE60000",
            "CEBE321F6FF7716B6FD4AB49AF256A15",
        ),
        (
            "0EC675AD498AFEEAB6960B3AABE60001",
            "6D38BAA48F0A0ACF3C34E2359E6CDBCE",
        ),
        (
            "0EC675AD498AFEEAB6960B3AABE60002",
            "E049646C43D9327AD175578EF7227098",
        ),
        (
            "0EC675AD498AFEEAB6960B3AABE60003",
            "6371C10C9A369AC2F94A8C5FBCDDDC25",
        ),
        (
            "0EC675AD498AFEEAB6960B3AABE60004",
            "6D6E919A48B610EF17C2041E47403576",
        ),
    ];
    for (input, output) in rounds {
        // str0m passes a 32-byte buffer and reads the first block.
        let mut buf = [0u8; 32];
        srtp().srtp_aes_128_ecb_round(&master, &hex(input), &mut buf);
        assert_eq!(buf[..16], hex(output), "input {input}");
    }
}

const RTP_HEADER: &str = "8040f17b 8041f8d3 5501a0b2";
const RTP_PAYLOAD: &str =
    "47616c6c 69612065 7374206f 6d6e6973 20646976 69736120 696e2070 61727465 73207472 6573";
const SALT: [u8; 12] = *b"Quid pro quo";

/// RFC 7714 sections 16.1 and 16.2: one RTP packet under both key sizes.
#[test]
fn rfc7714_rtp() {
    let iv = AeadAes128Gcm::rtp_iv(SALT, 0x5501a0b2, 0, 0xf17b);
    assert_eq!(iv.to_vec(), hex("51753c6580c2726f20718414"));

    let aad = hex(RTP_HEADER);
    let payload = hex(RTP_PAYLOAD);
    let key128: [u8; 16] = std::array::from_fn(|i| i as u8);
    let key256: [u8; 32] = std::array::from_fn(|i| i as u8);
    let sealed128 = hex(
        "f24de3a3 fb34de6c acba861c 9d7e4bca be633bd5 0d294e6f 42a5f47a 51c7d19b 36de3adf
         8833899d 7f27beb1 6a9152cf 765ee439 0cce",
    );
    let sealed256 = hex(
        "32b1de78 a822fe12 ef9f78fa 332e33aa b1801238 9a58e2f3 b50b2a02 76ffae0f 1ba63799
         b87b7aa3 db36dfff d6b0f9bb 7878d7a7 6c13",
    );

    let mut out = vec![0u8; sealed128.len()];
    let gcm = srtp().aead_aes_128_gcm();
    gcm.create_cipher(key128, true)
        .encrypt(&iv, &aad, &payload, &mut out)
        .unwrap();
    assert_eq!(out, sealed128);
    let n = gcm
        .create_cipher(key128, false)
        .decrypt(&iv, &[&aad], &sealed128, &mut out)
        .unwrap();
    assert_eq!(out[..n], payload);

    let gcm = srtp().aead_aes_256_gcm();
    gcm.create_cipher(key256, true)
        .encrypt(&iv, &aad, &payload, &mut out)
        .unwrap();
    assert_eq!(out, sealed256);
    let n = gcm
        .create_cipher(key256, false)
        .decrypt(&iv, &[&aad], &sealed256, &mut out)
        .unwrap();
    assert_eq!(out[..n], payload);
}

const RTCP_HEAD: &str = "81c8000d 4d617273";
const RTCP_BODY: &str = "4e545031 4e545032 52545020 0000042a 0000e930 4c756e61 deadbeef deadbeef deadbeef deadbeef deadbeef";

/// RFC 7714 section 17.1: an encrypted SRTCP packet.
#[test]
fn rfc7714_rtcp_encrypted() {
    let iv = AeadAes128Gcm::rtcp_iv(SALT, 0x4d617273, 0x5d4);
    assert_eq!(iv.to_vec(), hex("517524055203726f207170bb"));

    let key: [u8; 16] = std::array::from_fn(|i| i as u8);
    let aad = [hex(RTCP_HEAD), hex("800005d4")].concat();
    let body = hex(RTCP_BODY);
    let sealed = hex(
        "63e94885 dcdab67c a727d766 2f6b7e99 7ff5c0f7 6c06f32d c676a5f1 730d6fda 4ce09b46
         86303ded 0bb9275b c84aa458 96cf4d2f c5abf872 45d9eade",
    );

    let gcm = srtp().aead_aes_128_gcm();
    let mut out = vec![0u8; sealed.len()];
    gcm.create_cipher(key, true)
        .encrypt(&iv, &aad, &body, &mut out)
        .unwrap();
    assert_eq!(out, sealed);
    let n = gcm
        .create_cipher(key, false)
        .decrypt(&iv, &[&aad], &sealed, &mut out)
        .unwrap();
    assert_eq!(out[..n], body);
}

/// RFC 7714 section 17.3: an SRTCP packet tagged but not encrypted, whose
/// AAD str0m hands over in two slices around the tag.
#[test]
fn rfc7714_rtcp_tagged_only() {
    let iv = AeadAes128Gcm::rtcp_iv(SALT, 0x4d617273, 0x5d4);
    let key: [u8; 16] = std::array::from_fn(|i| i as u8);
    let packet = [hex(RTCP_HEAD), hex(RTCP_BODY)].concat();
    let index = hex("000005d4");
    let tag = hex("841dd968 3dd78ec9 2ae58790 125f62b3");

    let gcm = srtp().aead_aes_128_gcm();
    let mut out = [0u8; 16];
    let aad = [packet.as_slice(), &index].concat();
    gcm.create_cipher(key, true)
        .encrypt(&iv, &aad, &[], &mut out)
        .unwrap();
    assert_eq!(out.to_vec(), tag);

    let n = gcm
        .create_cipher(key, false)
        .decrypt(&iv, &[&packet, &index], &tag, &mut [])
        .unwrap();
    assert_eq!(n, 0);
}

#[test]
fn gcm_refuses_forgeries() {
    let iv = AeadAes128Gcm::rtp_iv(SALT, 0x5501a0b2, 0, 0xf17b);
    let key: [u8; 16] = std::array::from_fn(|i| i as u8);
    let aad = hex(RTP_HEADER);
    let sealed = hex(
        "f24de3a3 fb34de6c acba861c 9d7e4bca be633bd5 0d294e6f 42a5f47a 51c7d19b 36de3adf
         8833899d 7f27beb1 6a9152cf 765ee439 0cce",
    );
    let mut cipher = srtp().aead_aes_128_gcm().create_cipher(key, false);
    let mut out = vec![0u8; sealed.len()];

    for i in [0, sealed.len() - 1] {
        let mut forged = sealed.clone();
        forged[i] ^= 1;
        assert!(cipher.decrypt(&iv, &[&aad], &forged, &mut out).is_err());
        // Unauthenticated plaintext never reaches the caller.
        assert!(out.iter().all(|&b| b == 0));
    }

    let mut forged_aad = aad.clone();
    forged_aad[0] ^= 1;
    assert!(
        cipher
            .decrypt(&iv, &[&forged_aad], &sealed, &mut out)
            .is_err()
    );
    assert!(
        cipher
            .decrypt(&iv, &[&aad[..4], &aad[5..]], &sealed, &mut out)
            .is_err()
    );
}

#[test]
fn short_buffers_are_errors() {
    let iv = [0u8; 12];
    let mut gcm = srtp().aead_aes_256_gcm().create_cipher([0; 32], false);
    // Shorter than the tag.
    assert!(gcm.decrypt(&iv, &[&[]], &[0; 15], &mut [0; 16]).is_err());
    // No room for the plaintext.
    assert!(gcm.decrypt(&iv, &[&[]], &[0; 32], &mut [0; 15]).is_err());
    // No room for the tag.
    let mut gcm = srtp().aead_aes_128_gcm().create_cipher([0; 16], true);
    assert!(gcm.encrypt(&iv, &[], &[0; 16], &mut [0; 31]).is_err());

    let mut cm = srtp().aes_128_cm_sha1_80().create_cipher([0; 16], true);
    assert!(cm.encrypt(&[0; 16], &[0; 17], &mut [0; 16]).is_err());
}
