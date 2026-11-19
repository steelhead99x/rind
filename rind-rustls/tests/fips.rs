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
    for (suite, module) in [
        (cipher_suite::TLS13_AES_128_GCM_SHA256, FIPS),
        (cipher_suite::TLS13_AES_256_GCM_SHA384, FIPS),
        (cipher_suite::TLS13_CHACHA20_POLY1305_SHA256, false),
        (cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256, false),
        (cipher_suite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384, false),
        (
            cipher_suite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
            false,
        ),
    ] {
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
