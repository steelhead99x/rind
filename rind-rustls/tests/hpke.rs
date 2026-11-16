use std::sync::Arc;

use rustls::client::{EchConfig, EchMode};
#[cfg(not(target_family = "wasm"))]
use rustls::crypto::aws_lc_rs;
use rustls::crypto::hpke::{EncapsulatedSecret, Hpke, HpkePrivateKey, HpkePublicKey};
use rustls::pki_types::{EchConfigListBytes, ServerName};
use rustls::{ClientConfig, ClientConnection, RootCertStore};

/// Each of our suites beside rustls's aws-lc-rs provider's same suite.
#[cfg(not(target_family = "wasm"))]
fn pairs() -> impl Iterator<Item = (&'static dyn Hpke, &'static dyn Hpke)> {
    rind_rustls::hpke::ALL_SUPPORTED_SUITES
        .iter()
        .zip(aws_lc_rs::hpke::ALL_SUPPORTED_SUITES)
        .map(|(ours, theirs)| {
            assert_eq!(ours.suite(), theirs.suite());
            (*ours, *theirs)
        })
}

/// aws-lc-rs does not build for wasm, so there each suite meets itself.
#[cfg(target_family = "wasm")]
fn pairs() -> impl Iterator<Item = (&'static dyn Hpke, &'static dyn Hpke)> {
    rind_rustls::hpke::ALL_SUPPORTED_SUITES
        .iter()
        .map(|ours| (*ours, *ours))
}

fn copy(key: &HpkePrivateKey) -> HpkePrivateKey {
    HpkePrivateKey::from(key.secret_bytes().to_vec())
}

#[test]
fn matches_aws_lc_rs() {
    for (ours, theirs) in pairs() {
        // Each side's keys, in the bytes the other loads.
        for (generator, other) in [(ours, theirs), (theirs, ours)] {
            let (public_key, private_key) = generator.generate_key_pair().unwrap();
            for (sender, recipient) in [(ours, theirs), (theirs, ours), (ours, ours)] {
                let (enc, ct) = sender
                    .seal(b"info", b"aad", b"plaintext", &public_key)
                    .unwrap();
                let pt = recipient
                    .open(&enc, b"info", b"aad", &ct, &copy(&private_key))
                    .unwrap();
                assert_eq!(pt, b"plaintext", "{:?}", ours.suite());
                assert!(
                    recipient
                        .open(&enc, b"other", b"aad", &ct, &copy(&private_key))
                        .is_err()
                );

                let (enc, mut sealer) = sender.setup_sealer(b"", &public_key).unwrap();
                let mut opener = recipient
                    .setup_opener(&enc, b"", &copy(&private_key))
                    .unwrap();
                let sealed = (0..3)
                    .map(|i| sealer.seal(&[i], &[i; 40]).unwrap())
                    .collect::<Vec<_>>();
                // A failed open leaves the sequence where it was.
                assert!(opener.open(&[1], &sealed[1]).is_err());
                for (i, ct) in sealed.iter().enumerate() {
                    let i = i as u8;
                    assert_eq!(opener.open(&[i], ct).unwrap(), [i; 40]);
                }
            }

            // A public key the other side's generator never makes: both
            // refuse it, short of a length either side takes.
            let mut bad = public_key.0.clone();
            let last = bad.len() - 1;
            bad[last] ^= 1;
            for bad in [&bad[..], &public_key.0[..last], &[]] {
                let bad = HpkePublicKey(bad.to_vec());
                assert_eq!(
                    ours.seal(b"", b"", b"", &bad).is_ok(),
                    other.seal(b"", b"", b"", &bad).is_ok(),
                    "{:?} {bad:?}",
                    ours.suite()
                );
            }
        }
    }
}

/// `point`, an uncompressed NIST point, compressed.
#[cfg(not(target_family = "wasm"))]
fn compressed(point: &[u8]) -> Vec<u8> {
    let mut compressed = vec![2 | (point[point.len() - 1] & 1)];
    compressed.extend(&point[1..1 + point.len() / 2]);
    compressed
}

// RFC 9180 serializes NIST points uncompressed (section 7.1.1), and the KEM
// context hashes them as sent. aws-lc-rs seals to a compressed public key,
// but its recipient hashes its own key uncompressed, so not even aws-lc-rs
// opens the message; rind refuses the key instead. Both take a compressed
// `enc`, which a sender that sends one hashes as sent.
// It needs aws-lc-rs, which seals to a compressed key.
#[cfg(not(target_family = "wasm"))]
#[test]
fn compressed_points() {
    for (ours, theirs) in pairs() {
        let (public_key, private_key) = theirs.generate_key_pair().unwrap();
        if public_key.0.len() == 32 {
            continue; // X25519 has no compressed form.
        }
        let compressed_key = HpkePublicKey(compressed(&public_key.0));
        let (enc, ct) = theirs.seal(b"", b"", b"pt", &compressed_key).unwrap();
        assert!(
            theirs
                .open(&enc, b"", b"", &ct, &copy(&private_key))
                .is_err()
        );
        assert!(ours.seal(b"", b"", b"pt", &compressed_key).is_err());

        let (enc, _) = theirs.seal(b"", b"", b"pt", &public_key).unwrap();
        let enc = EncapsulatedSecret(compressed(&enc.0));
        for side in [ours, theirs] {
            assert!(side.setup_opener(&enc, b"", &copy(&private_key)).is_ok());
        }
    }
}

/// An `ECHConfigList` (draft-ietf-tls-esni section 4) holding one config for
/// `suite`'s KEM and symmetric suite, and that config's bytes, which HPKE's
/// `info` names.
fn ech_config_list(suite: &dyn Hpke, public_key: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let suite = suite.suite();
    let mut contents = vec![7]; // config_id
    contents.extend(u16::from(suite.kem).to_be_bytes());
    contents.extend((public_key.len() as u16).to_be_bytes());
    contents.extend(public_key);
    contents.extend(4u16.to_be_bytes());
    contents.extend(u16::from(suite.sym.kdf_id).to_be_bytes());
    contents.extend(u16::from(suite.sym.aead_id).to_be_bytes());
    contents.push(0); // maximum_name_length
    let public_name = b"public.example";
    contents.push(public_name.len() as u8);
    contents.extend(public_name);
    contents.extend(0u16.to_be_bytes()); // extensions

    let mut config = 0xfe0du16.to_be_bytes().to_vec();
    config.extend((contents.len() as u16).to_be_bytes());
    config.extend(contents);
    let mut list = (config.len() as u16).to_be_bytes().to_vec();
    list.extend(&config);
    (list, config)
}

/// The outer ClientHello's ECH extension, as parts HPKE opens: the
/// encapsulated key, the payload, and the ClientHello with the payload
/// zeroed, which is the AAD (draft-ietf-tls-esni section 5.2).
fn ech_extension(record: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let u16_at = |bytes: &[u8], at: usize| u16::from_be_bytes([bytes[at], bytes[at + 1]]) as usize;
    assert_eq!(record[0], 22, "a handshake record");
    let handshake = &record[5..5 + u16_at(record, 3)];
    assert_eq!(handshake[0], 1, "a ClientHello");
    let mut hello = handshake[4..].to_vec();

    let mut at = 2 + 32; // legacy_version, random
    at += 1 + hello[at] as usize; // legacy_session_id
    at += 2 + u16_at(&hello, at); // cipher_suites
    at += 1 + hello[at] as usize; // legacy_compression_methods
    let end = at + 2 + u16_at(&hello, at);
    at += 2;
    while at < end {
        let (kind, len) = (u16_at(&hello, at), u16_at(&hello, at + 2));
        at += 4;
        if kind == 0xfe0d {
            assert_eq!(hello[at], 0, "an outer ClientHello's extension");
            let enc_at = at + 1 + 4 + 1; // type, cipher_suite, config_id
            let enc_len = u16_at(&hello, enc_at);
            let enc = hello[enc_at + 2..enc_at + 2 + enc_len].to_vec();
            let payload_at = enc_at + 2 + enc_len;
            let payload_len = u16_at(&hello, payload_at);
            let payload = &mut hello[payload_at + 2..payload_at + 2 + payload_len];
            let ct = payload.to_vec();
            payload.fill(0);
            return (enc, ct, hello);
        }
        at += len;
    }
    panic!("no ECH extension");
}

// rustls 0.23's ECH is client-side, so the test is the server: it opens the
// outer ClientHello's ECH payload with the config's private key, through our
// suite and aws-lc-rs's, and finds the inner ClientHello's server name.
#[test]
fn encrypted_client_hello() {
    let provider = Arc::new(rind_rustls::default_provider());
    for (ours, theirs) in pairs() {
        let (public_key, private_key) = ours.generate_key_pair().unwrap();
        let (list, config) = ech_config_list(ours, &public_key.0);
        let ech = EchConfig::new(
            EchConfigListBytes::from(list),
            rind_rustls::hpke::ALL_SUPPORTED_SUITES,
        )
        .unwrap();
        let client_config = ClientConfig::builder_with_provider(provider.clone())
            .with_ech(EchMode::Enable(ech))
            .unwrap()
            .with_root_certificates(RootCertStore::empty())
            .with_no_client_auth();
        let mut client = ClientConnection::new(
            Arc::new(client_config),
            ServerName::try_from("inner.example").unwrap(),
        )
        .unwrap();
        let mut record = Vec::new();
        client.write_tls(&mut record).unwrap();

        let (enc, ct, aad) = ech_extension(&record);
        let enc = EncapsulatedSecret(enc);
        let info = [&b"tls ech\0"[..], &config].concat();
        let inner = ours
            .open(&enc, &info, &aad, &ct, &copy(&private_key))
            .unwrap();
        assert_eq!(
            theirs
                .open(&enc, &info, &aad, &ct, &copy(&private_key))
                .unwrap(),
            inner,
        );
        assert!(
            inner.windows(13).any(|name| name == b"inner.example"),
            "{:?}",
            ours.suite()
        );
    }
}
