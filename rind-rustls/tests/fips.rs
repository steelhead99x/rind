//! The `fips` feature: which provider parts run in rind-fips's module and
//! say so, that the default provider offers only those, and that a TLS 1.3
//! connection over them carries data both ways.
//!
//! Without the feature, nothing claims to be FIPS.

use std::io::{Read, Write};
use std::sync::Arc;

use rind_rustls::{cipher_suite, kx_group};
use rustls::crypto::CryptoProvider;
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use rustls::{
    ClientConfig, ClientConnection, NamedGroup, ProtocolVersion, RootCertStore, ServerConfig,
    ServerConnection, SupportedCipherSuite,
};

const FIPS: bool = cfg!(feature = "fips");

/// Where `fips()` is true: TLS 1.3 AES-GCM, and the key exchange groups whose
/// ECDH and ML-KEM run in the module. TLS 1.2 stays false: the module seals
/// only TLS 1.3 records. X25519 alone stays false, and its hybrid with
/// ML-KEM-768 is true, as in rustls's aws-lc-rs provider.
#[test]
fn components_say_what_runs_in_the_module() {
    #[allow(unused_mut)]
    let mut suites = vec![
        (cipher_suite::TLS13_AES_128_GCM_SHA256, FIPS),
        (cipher_suite::TLS13_AES_256_GCM_SHA384, FIPS),
        (cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, false),
    ];
    // The TLS 1.2 suites exist only with `tls12`.
    #[cfg(feature = "tls12")]
    suites.extend([
        (cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, false),
        (cipher_suite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384, false),
        (
            cipher_suite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
            false,
        ),
    ]);
    for (suite, module) in suites {
        assert_eq!(suite.fips(), module, "{:?}", suite.suite());
    }
    for (group, module) in [
        (kx_group::X25519, false),
        (kx_group::SECP256R1, FIPS),
        (kx_group::SECP384R1, FIPS),
        (kx_group::X25519MLKEM768, FIPS),
        (kx_group::SECP256R1MLKEM768, FIPS),
        (kx_group::MLKEM768, FIPS),
        (kx_group::MLKEM1024, FIPS),
    ] {
        assert_eq!(group.fips(), module, "{:?}", group.name());
    }
    let provider = rind_rustls::default_provider();
    assert_eq!(provider.secure_random.fips(), FIPS);
    // Signing keys and signature verification do not run in the module yet.
    assert!(!provider.key_provider.fips());
    assert!(!provider.signature_verification_algorithms.fips());
    assert!(!provider.fips());
}

#[test]
fn the_default_provider_offers_only_the_module_under_fips() {
    let provider = rind_rustls::default_provider();
    let suites: Vec<_> = provider.cipher_suites.iter().map(|cs| cs.suite()).collect();
    let groups: Vec<_> = provider.kx_groups.iter().map(|kx| kx.name()).collect();
    if FIPS {
        assert!(
            provider
                .cipher_suites
                .iter()
                .all(SupportedCipherSuite::fips)
        );
        assert!(provider.kx_groups.iter().all(|kx| kx.fips()));
        assert!(!suites.iter().any(|s| format!("{s:?}").contains("CHACHA20")));
        assert!(!groups.contains(&NamedGroup::X25519));
        assert!(groups.contains(&NamedGroup::X25519MLKEM768));
        assert!(groups.contains(&NamedGroup::secp256r1));
        assert!(groups.contains(&NamedGroup::secp384r1));
    } else {
        assert!(groups.contains(&NamedGroup::X25519));
        assert!(suites.iter().any(|s| format!("{s:?}").contains("CHACHA20")));
    }
}

/// A TLS 1.3 connection over each default group and AES-GCM suite, whose
/// records the module seals and opens under `fips`.
#[test]
fn tls13_carries_data_both_ways() {
    let provider = rind_rustls::default_provider();
    let groups = provider.kx_groups.clone();
    for suite in [
        cipher_suite::TLS13_AES_128_GCM_SHA256,
        cipher_suite::TLS13_AES_256_GCM_SHA384,
    ] {
        for group in &groups {
            let provider: Arc<_> = CryptoProvider {
                cipher_suites: vec![suite],
                kx_groups: vec![*group],
                ..rind_rustls::default_provider()
            }
            .into();
            let (client, server) = connect(provider);
            assert_eq!(client.0, ProtocolVersion::TLSv1_3);
            assert_eq!(client.1, suite.suite());
            assert_eq!(server.1, suite.suite());
            assert_eq!(client.2, b"hello, server");
            assert_eq!(server.2, b"hello, client");
        }
    }
}

type Outcome = (ProtocolVersion, rustls::CipherSuite, Vec<u8>);

/// Runs a handshake and one message each way over an ECDSA P-256 chain.
fn connect(provider: Arc<CryptoProvider>) -> (Outcome, Outcome) {
    let dir = format!("{}/tests/keys/ecdsa-p256", env!("CARGO_MANIFEST_DIR"));
    let chain = CertificateDer::pem_file_iter(format!("{dir}/end.fullchain"))
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let key = PrivateKeyDer::from_pem_file(format!("{dir}/end.key")).unwrap();
    let mut roots = RootCertStore::empty();
    roots
        .add(CertificateDer::from_pem_file(format!("{dir}/ca.cert")).unwrap())
        .unwrap();

    let server_config: Arc<ServerConfig> = ServerConfig::builder_with_provider(provider.clone())
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(chain, key)
        .unwrap()
        .into();
    let client_config: Arc<ClientConfig> = ClientConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth()
        .into();
    let mut client = ClientConnection::new(client_config, "localhost".try_into().unwrap()).unwrap();
    let mut server = ServerConnection::new(server_config).unwrap();

    let mut buf = [0u8; 16384];
    while client.is_handshaking() || server.is_handshaking() {
        let n = client.write_tls(&mut &mut buf[..]).unwrap();
        if n > 0 {
            server.read_tls(&mut &buf[..n]).unwrap();
            server.process_new_packets().unwrap();
        }
        let n = server.write_tls(&mut &mut buf[..]).unwrap();
        if n > 0 {
            client.read_tls(&mut &buf[..n]).unwrap();
            client.process_new_packets().unwrap();
        }
    }
    client.writer().write_all(b"hello, server").unwrap();
    server.writer().write_all(b"hello, client").unwrap();
    let n = client.write_tls(&mut &mut buf[..]).unwrap();
    server.read_tls(&mut &buf[..n]).unwrap();
    server.process_new_packets().unwrap();
    let n = server.write_tls(&mut &mut buf[..]).unwrap();
    client.read_tls(&mut &buf[..n]).unwrap();
    client.process_new_packets().unwrap();

    let mut at_server = vec![0u8; 13];
    server.reader().read_exact(&mut at_server).unwrap();
    let mut at_client = vec![0u8; 13];
    client.reader().read_exact(&mut at_client).unwrap();
    (
        (
            client.protocol_version().unwrap(),
            client.negotiated_cipher_suite().unwrap().suite(),
            at_server,
        ),
        (
            server.protocol_version().unwrap(),
            server.negotiated_cipher_suite().unwrap().suite(),
            at_client,
        ),
    )
}

/// TLS 1.3 records sealed here open under rustls's aws-lc-rs provider, and
/// the reverse, so the module's sealing and opening agree with an
/// independent AES-GCM over the same key, IV, and sequence numbers.
#[cfg(not(target_family = "wasm"))]
#[test]
fn records_agree_with_aws_lc_rs_both_ways() {
    use rustls::ContentType;
    use rustls::crypto::aws_lc_rs::cipher_suite as aws;
    use rustls::crypto::cipher::{
        AeadKey, InboundOpaqueMessage, Iv, OutboundChunks, OutboundPlainMessage,
    };

    // rustls builds a 16-byte key only by deriving it, which the handshake
    // tests do, so this takes the 32-byte AES-256 key directly.
    for (ours, theirs) in [(
        cipher_suite::TLS13_AES_256_GCM_SHA384,
        aws::TLS13_AES_256_GCM_SHA384,
    )] {
        let (ours, theirs) = (ours.tls13().unwrap(), theirs.tls13().unwrap());
        assert_eq!(ours.aead_alg.key_len(), 32);
        let key = |fill: u8| AeadKey::from([fill; 32]);
        let iv = [0x24u8; 12];
        let message = |data: &'static [u8]| OutboundPlainMessage {
            typ: ContentType::ApplicationData,
            version: ProtocolVersion::TLSv1_3,
            payload: OutboundChunks::Single(data),
        };

        for (sealer, opener) in [(ours, theirs), (theirs, ours)] {
            let mut seal = sealer.aead_alg.encrypter(key(0x11), Iv::new(iv));
            let mut open = opener.aead_alg.decrypter(key(0x11), Iv::new(iv));
            for (seq, data) in [
                (0u64, &b""[..]),
                (1, b"a"),
                (2, &[0x5a; 1000][..]),
                (7, &[0xa5; 16384][..]),
            ] {
                let sealed = seal.encrypt(message(data), seq).unwrap();
                let mut bytes = sealed.payload.as_ref().to_vec();
                let record = InboundOpaqueMessage::new(sealed.typ, sealed.version, &mut bytes);
                let plain = open.decrypt(record, seq).unwrap();
                assert_eq!(plain.payload, data, "{:?} seq {seq}", ours.common.suite);
            }
            // A record under another sequence number does not open.
            let sealed = seal.encrypt(message(b"x"), 9).unwrap();
            let mut bytes = sealed.payload.as_ref().to_vec();
            let record = InboundOpaqueMessage::new(sealed.typ, sealed.version, &mut bytes);
            assert!(open.decrypt(record, 10).is_err());
        }
    }
}

/// QUIC packets sealed here open under rustls's aws-lc-rs provider and the
/// reverse, whatever packet number a key starts at: a key update (RFC 9001
/// section 6.2) hands a new key the connection's next packet number, which is
/// not 0, and `confidentiality_limit` is what makes it come early.
#[cfg(not(target_family = "wasm"))]
#[test]
fn quic_packets_agree_with_aws_lc_rs_from_any_packet_number() {
    use rustls::crypto::aws_lc_rs::cipher_suite as aws;
    use rustls::crypto::cipher::{AeadKey, Iv};

    // rustls builds a 16-byte key only by deriving it, so this takes the
    // 32-byte AES-256 key directly, as the record test does.
    {
        let ours = cipher_suite::TLS13_AES_256_GCM_SHA384
            .tls13()
            .unwrap()
            .quic_suite()
            .unwrap();
        let theirs = aws::TLS13_AES_256_GCM_SHA384
            .tls13()
            .unwrap()
            .quic_suite()
            .unwrap();
        for start in [0u64, 1, 3, 8_388_609, 1 << 40, (1 << 62) - 3] {
            let key = |alg: &dyn rustls::quic::Algorithm| {
                alg.packet_key(AeadKey::from([0x42u8; 32]), Iv::new([0x5a; 12]))
            };
            let (here, there) = (key(ours.quic), key(theirs.quic));
            let header = b"header";
            // Consecutive and skipping packet numbers.
            for pn in [start, start + 1, start + 2, start + 10, start + 11] {
                let mut mine = b"quic payload".to_vec();
                let tag = here.encrypt_in_place(pn, header, &mut mine).unwrap();
                let mut theirs_out = b"quic payload".to_vec();
                let their_tag = there.encrypt_in_place(pn, header, &mut theirs_out).unwrap();
                assert_eq!(mine, theirs_out, "start {start} pn {pn}");
                assert_eq!(tag.as_ref(), their_tag.as_ref());
                // Open what the other sealed.
                mine.extend_from_slice(tag.as_ref());
                let plain = there.decrypt_in_place(pn, header, &mut mine).unwrap();
                assert_eq!(plain, b"quic payload");
            }
            // The module refuses a packet number already sealed under the
            // key; rind's own AES-GCM does not track them.
            let mut again = b"quic payload".to_vec();
            let refused = here.encrypt_in_place(start + 11, header, &mut again);
            assert_eq!(refused.is_err(), FIPS);
        }
    }
}

/// Packets sealed out of order under one key, as concurrent `&self` sealing
/// does, seal as rustls's aws-lc-rs provider does: pn + 1 before pn, and a
/// few reversed, each equal byte for byte, while under `fips` a packet number
/// sealed twice is refused (rind's own AES-GCM does not track them).
#[cfg(not(target_family = "wasm"))]
#[test]
fn quic_packets_seal_out_of_order_as_aws_lc_rs_does() {
    use rustls::crypto::aws_lc_rs::cipher_suite as aws;
    use rustls::crypto::cipher::{AeadKey, Iv};

    // rustls builds a 16-byte key only by deriving it, so this takes the
    // 32-byte AES-256 key directly, as the test above does.
    {
        let (ours, theirs) = (
            cipher_suite::TLS13_AES_256_GCM_SHA384,
            aws::TLS13_AES_256_GCM_SHA384,
        );
        let ours = ours.tls13().unwrap().quic_suite().unwrap();
        let theirs = theirs.tls13().unwrap().quic_suite().unwrap();
        for start in [0u64, 1, 3, 8_388_609, 1 << 40, (1 << 62) - 20] {
            let key = |alg: &dyn rustls::quic::Algorithm| {
                alg.packet_key(AeadKey::from([0x42u8; 32]), Iv::new([0x5a; 12]))
            };
            let (here, there) = (key(ours.quic), key(theirs.quic));
            let header = b"header";
            for pn in [
                start + 1,
                start,
                start + 5,
                start + 3,
                start + 4,
                start + 2,
                start + 12,
                start + 9,
            ] {
                let mut mine = b"quic payload".to_vec();
                let tag = here.encrypt_in_place(pn, header, &mut mine).unwrap();
                let mut theirs_out = b"quic payload".to_vec();
                let their_tag = there.encrypt_in_place(pn, header, &mut theirs_out).unwrap();
                assert_eq!(mine, theirs_out, "start {start} pn {pn}");
                assert_eq!(tag.as_ref(), their_tag.as_ref());
                mine.extend_from_slice(tag.as_ref());
                let plain = there.decrypt_in_place(pn, header, &mut mine).unwrap();
                assert_eq!(plain, b"quic payload");
            }
            // Each of them again.
            for pn in [start, start + 1, start + 9, start + 12] {
                let mut again = b"quic payload".to_vec();
                let refused = here.encrypt_in_place(pn, header, &mut again);
                assert_eq!(refused.is_err(), FIPS, "pn {pn}");
            }
        }
    }
}

/// HKDF-Expand through rind-rustls's TLS 1.3 suites matches rustls's aws-lc-rs
/// provider for every `info` it takes, an empty one included: aws-lc-rs
/// derives `expand_slice(&[], ..)`, and under `fips` the module refuses it, so
/// the expander derives it in its rind copy. The same `info` split into parts
/// gives the same bytes, and a length over 255 hash outputs fails in both.
#[cfg(not(target_family = "wasm"))]
#[test]
fn hkdf_expand_agrees_with_aws_lc_rs_for_any_info() {
    use rustls::crypto::aws_lc_rs::cipher_suite as aws;
    use rustls::crypto::tls13::{Hkdf, HkdfExpander};

    let pairs = [
        (
            cipher_suite::TLS13_AES_128_GCM_SHA256,
            aws::TLS13_AES_128_GCM_SHA256,
        ),
        (
            cipher_suite::TLS13_AES_256_GCM_SHA384,
            aws::TLS13_AES_256_GCM_SHA384,
        ),
    ];
    let infos: [&[&[u8]]; 9] = [
        &[],
        &[b""],
        &[b"", b"", b""],
        &[b"label"],
        &[b"la", b"bel"],
        &[b"", b"la", b"", b"bel", b""],
        &[b"l", b"a", b"b", b"e", b"l"],
        &[&[0u8; 300]],
        &[&[0xffu8; 1], &[0u8; 0], &[7u8; 130]],
    ];
    let secret = [0x5au8; 32];
    for (ours, theirs) in pairs {
        let ours: &dyn Hkdf = ours.tls13().unwrap().hkdf_provider;
        let theirs: &dyn Hkdf = theirs.tls13().unwrap().hkdf_provider;
        let salts: [Option<&[u8]>; 3] = [None, Some(&[]), Some(b"a salt")];
        for salt in salts {
            let a = ours.extract_from_secret(salt, &secret);
            let b = theirs.extract_from_secret(salt, &secret);
            let z_a = ours.extract_from_zero_ikm(salt);
            let z_b = theirs.extract_from_zero_ikm(salt);
            let okm = a.expand_block(&[b"okm"]);
            let c = ours.expander_for_okm(&okm);
            let d = theirs.expander_for_okm(&okm);
            let hash_len = a.hash_len();
            assert_eq!(hash_len, b.hash_len());
            for (x, y) in [(&a, &b), (&z_a, &z_b), (&c, &d)] {
                check_expanders(x.as_ref(), y.as_ref(), &infos, hash_len);
            }
        }
    }

    fn check_expanders(
        ours: &dyn HkdfExpander,
        theirs: &dyn HkdfExpander,
        infos: &[&[&[u8]]],
        hash_len: usize,
    ) {
        for info in infos {
            for len in [0, 1, hash_len, 3 * hash_len + 7, 255 * hash_len] {
                let mut x = vec![1u8; len];
                let mut y = vec![2u8; len];
                let rx = ours.expand_slice(info, &mut x);
                let ry = theirs.expand_slice(info, &mut y);
                assert_eq!(rx.is_ok(), ry.is_ok(), "{info:?} {len}");
                assert_eq!(x, y, "{info:?} {len}");
            }
            let mut x = vec![0u8; 255 * hash_len + 1];
            let mut y = x.clone();
            assert!(ours.expand_slice(info, &mut x).is_err());
            assert!(theirs.expand_slice(info, &mut y).is_err());
            assert_eq!(
                ours.expand_block(info).as_ref(),
                theirs.expand_block(info).as_ref(),
                "{info:?}"
            );
        }
        // Every split of one `info` derives the same bytes.
        let mut whole = vec![0u8; hash_len];
        ours.expand_slice(&[b"label"], &mut whole).unwrap();
        let mut split = vec![0u8; hash_len];
        ours.expand_slice(&[b"la", b"", b"bel"], &mut split)
            .unwrap();
        assert_eq!(whole, split);
        // An empty `info` is not the same as a non-empty one.
        let mut empty = vec![0u8; hash_len];
        ours.expand_slice(&[], &mut empty).unwrap();
        assert_ne!(whole, empty);
    }
}
