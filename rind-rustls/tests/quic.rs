//! QUIC handshakes between rind and other providers, checking that each side's
//! packet and header protection keys open what the other side seals.

use std::sync::Arc;

use rustls::crypto::CryptoProvider;
#[cfg(not(target_family = "wasm"))]
use rustls::crypto::{aws_lc_rs, ring};
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use rustls::quic::{self, Connection, DirectionalKeys, KeyChange, PacketKey, Version};
use rustls::{CipherSuite, ClientConfig, RootCertStore, ServerConfig, Side, SupportedCipherSuite};

/// The providers rind runs against.
#[cfg(not(target_family = "wasm"))]
fn others() -> [CryptoProvider; 2] {
    [aws_lc_rs::default_provider(), ring::default_provider()]
}

/// rustls's own providers build for neither wasm target, so there rind runs
/// against itself.
#[cfg(target_family = "wasm")]
fn others() -> [CryptoProvider; 1] {
    [rind_rustls::default_provider()]
}

#[test]
fn initial_keys() {
    // Initial keys always use AES-128-GCM, derived from the client's first destination CID.
    let dcid = b"initial dcid";
    let rind = rind_rustls::default_provider();
    for other in others() {
        check_keys(
            &initial(&rind, dcid, Side::Client),
            &initial(&other, dcid, Side::Server),
        );
        check_keys(
            &initial(&other, dcid, Side::Client),
            &initial(&rind, dcid, Side::Server),
        );
    }
}

#[test]
fn all_suites() {
    for suite in [
        rind_rustls::cipher_suite::TLS13_AES_128_GCM_SHA256,
        rind_rustls::cipher_suite::TLS13_AES_256_GCM_SHA384,
        rind_rustls::cipher_suite::TLS13_CHACHA20_POLY1305_SHA256,
    ] {
        let rind: Arc<_> = CryptoProvider {
            cipher_suites: vec![suite],
            ..rind_rustls::default_provider()
        }
        .into();
        for other in others() {
            let other = Arc::new(other);
            handshake(suite, rind.clone(), other.clone());
            handshake(suite, other, rind.clone());
        }
    }
}

fn handshake(
    suite: SupportedCipherSuite,
    client_provider: Arc<CryptoProvider>,
    server_provider: Arc<CryptoProvider>,
) {
    println!("{:?}: client {client_provider:?}", suite.suite());

    let mut client = Connection::Client(
        quic::ClientConnection::new(
            client_config(client_provider),
            Version::V1,
            "localhost".try_into().unwrap(),
            b"client params".to_vec(),
        )
        .unwrap(),
    );
    let mut server = Connection::Server(
        quic::ServerConnection::new(
            server_config(server_provider),
            Version::V1,
            b"server params".to_vec(),
        )
        .unwrap(),
    );

    assert!(step(&mut client, &mut server).is_none());
    let server_hs = step(&mut server, &mut client).unwrap();
    let client_hs = step(&mut client, &mut server).unwrap();
    let (KeyChange::Handshake { keys: server_hs }, KeyChange::Handshake { keys: client_hs }) =
        (server_hs, client_hs)
    else {
        panic!("expected handshake keys");
    };
    check_keys(&client_hs, &server_hs);

    let server_1rtt = step(&mut server, &mut client).unwrap();
    let client_1rtt = step(&mut client, &mut server).unwrap();
    assert!(!client.is_handshaking() && !server.is_handshaking());
    assert_eq!(client.negotiated_cipher_suite(), Some(suite));
    assert_eq!(server.negotiated_cipher_suite(), Some(suite));
    assert_eq!(
        server.quic_transport_parameters(),
        Some(&b"client params"[..])
    );
    assert_eq!(
        client.quic_transport_parameters(),
        Some(&b"server params"[..])
    );

    let (
        KeyChange::OneRtt {
            keys: server_1rtt,
            next: mut server_next,
        },
        KeyChange::OneRtt {
            keys: client_1rtt,
            next: mut client_next,
        },
    ) = (server_1rtt, client_1rtt)
    else {
        panic!("expected 1-RTT keys");
    };
    check_keys(&client_1rtt, &server_1rtt);

    // Key updates derive new packet keys but keep the header protection keys.
    for _ in 0..2 {
        let client_next = client_next.next_packet_keys();
        let server_next = server_next.next_packet_keys();
        seal_open(&*client_next.local, &*server_next.remote);
        seal_open(&*server_next.local, &*client_next.remote);
    }
}

/// Drives `send` until it changes keys or runs dry, and feeds its output to `recv`.
fn step(send: &mut Connection, recv: &mut Connection) -> Option<KeyChange> {
    let mut buf = Vec::new();
    let change = loop {
        let prev = buf.len();
        if let Some(change) = send.write_hs(&mut buf) {
            break Some(change);
        }
        if prev == buf.len() {
            break None;
        }
    };
    recv.read_hs(&buf).unwrap();
    assert_eq!(recv.alert(), None);
    change
}

fn initial(provider: &CryptoProvider, dcid: &[u8], side: Side) -> quic::Keys {
    let suite = provider
        .cipher_suites
        .iter()
        .find(|suite| suite.suite() == CipherSuite::TLS13_AES_128_GCM_SHA256)
        .and_then(SupportedCipherSuite::tls13)
        .unwrap();
    suite.quic_suite().unwrap().keys(dcid, side, Version::V1)
}

fn check_keys(client: &quic::Keys, server: &quic::Keys) {
    protect_unprotect(&client.local, &server.remote);
    protect_unprotect(&server.local, &client.remote);
}

/// Seals and header-protects a short-header packet, then removes both on the other side.
fn protect_unprotect(send: &DirectionalKeys, recv: &DirectionalKeys) {
    const PN: u64 = 0x1234_5678;
    // Short header, 4-byte packet number, then the packet number itself.
    let header = [0x43, 0xde, 0xad, 0xbe, 0xef, 0x12, 0x34, 0x56, 0x78];
    let pn_offset = header.len() - 4;
    let payload = b"a payload long enough to sample";

    let mut packet = [&header[..], &payload[..]].concat();
    let (head, body) = packet.split_at_mut(header.len());
    let tag = send.packet.encrypt_in_place(PN, head, body).unwrap();
    packet.extend_from_slice(tag.as_ref());

    let (head, rest) = packet.split_at_mut(pn_offset + 4);
    let sample = &rest[..send.header.sample_len()];
    let (first, pn) = head.split_first_mut().unwrap();
    send.header
        .encrypt_in_place(sample, first, &mut pn[pn_offset - 1..])
        .unwrap();
    assert_ne!(&packet[..header.len()], &header[..]);

    let (head, rest) = packet.split_at_mut(pn_offset + 4);
    let sample = &rest[..recv.header.sample_len()];
    let (first, pn) = head.split_first_mut().unwrap();
    recv.header
        .decrypt_in_place(sample, first, &mut pn[pn_offset - 1..])
        .unwrap();
    let (head, body) = packet.split_at_mut(header.len());
    assert_eq!(head, &header[..]);
    assert_eq!(
        recv.packet.decrypt_in_place(PN, head, body).unwrap(),
        payload
    );
}

fn seal_open(send: &dyn PacketKey, recv: &dyn PacketKey) {
    let mut packet = b"after a key update".to_vec();
    let tag = send.encrypt_in_place(9, b"header", &mut packet).unwrap();
    packet.extend_from_slice(tag.as_ref());
    let plain = recv.decrypt_in_place(9, b"header", &mut packet).unwrap();
    assert_eq!(plain, b"after a key update");
}

fn server_config(provider: Arc<CryptoProvider>) -> Arc<ServerConfig> {
    let cert_chain = CertificateDer::pem_file_iter(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/keys/ecdsa-p256/end.fullchain"
    ))
    .unwrap()
    .collect::<Result<Vec<_>, _>>()
    .unwrap();
    let key = PrivateKeyDer::from_pem_file(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/keys/ecdsa-p256/end.key"
    ))
    .unwrap();
    ServerConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(cert_chain, key)
        .unwrap()
        .into()
}

fn client_config(provider: Arc<CryptoProvider>) -> Arc<ClientConfig> {
    let mut roots = RootCertStore::empty();
    roots
        .add(
            CertificateDer::from_pem_file(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/tests/keys/ecdsa-p256/ca.cert"
            ))
            .unwrap(),
        )
        .unwrap();
    ClientConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth()
        .into()
}
