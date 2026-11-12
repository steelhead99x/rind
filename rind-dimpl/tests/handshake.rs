//! Completes DTLS handshakes between rind's provider and dimpl's aws-lc-rs
//! provider, for every suite and group, then exchanges records both ways.

use std::sync::Arc;
use std::time::{Duration, Instant};

use ::aws_lc_rs::encoding::AsDer;
use ::aws_lc_rs::signature;
use dimpl::crypto::{CryptoProvider, Dtls12CipherSuite, Dtls13CipherSuite, NamedGroup, aws_lc_rs};
use dimpl::{Config, Dtls, DtlsCertificate, Output, ProtocolVersion};

const DTLS12: [Dtls12CipherSuite; 3] = [
    Dtls12CipherSuite::ECDHE_ECDSA_AES128_GCM_SHA256,
    Dtls12CipherSuite::ECDHE_ECDSA_AES256_GCM_SHA384,
    Dtls12CipherSuite::ECDHE_ECDSA_CHACHA20_POLY1305_SHA256,
];

const DTLS13: [Dtls13CipherSuite; 3] = [
    Dtls13CipherSuite::AES_128_GCM_SHA256,
    Dtls13CipherSuite::AES_256_GCM_SHA384,
    Dtls13CipherSuite::CHACHA20_POLY1305_SHA256,
];

const GROUPS: [NamedGroup; 3] = [
    NamedGroup::X25519,
    NamedGroup::Secp256r1,
    NamedGroup::Secp384r1,
];

#[derive(Clone, Copy, Debug)]
enum Suite {
    Dtls12(Dtls12CipherSuite),
    Dtls13(Dtls13CipherSuite),
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum Curve {
    P256,
    P384,
}

#[derive(Clone, Copy, Debug)]
enum KeyFormat {
    Pkcs8,
    Sec1,
}

/// One endpoint: which provider it runs and how its certificate key is made.
#[derive(Clone, Copy, Debug)]
struct Side {
    rind: bool,
    curve: Curve,
    format: KeyFormat,
}

impl Side {
    fn provider(self) -> CryptoProvider {
        match self.rind {
            true => rind_dimpl::default_provider(),
            false => aws_lc_rs::default_provider(),
        }
    }

    fn certificate(self) -> DtlsCertificate {
        let algorithm = match self.curve {
            Curve::P256 => &rcgen::PKCS_ECDSA_P256_SHA256,
            Curve::P384 => &rcgen::PKCS_ECDSA_P384_SHA384,
        };
        let key = rcgen::KeyPair::generate_for(algorithm).unwrap();
        let certificate = rcgen::CertificateParams::new(Vec::<String>::new())
            .unwrap()
            .self_signed(&key)
            .unwrap()
            .der()
            .to_vec();

        let pkcs8 = key.serialize_der();
        let private_key = match self.format {
            KeyFormat::Pkcs8 => pkcs8,
            KeyFormat::Sec1 => sec1(self.curve, &pkcs8),
        };
        DtlsCertificate {
            certificate,
            private_key,
        }
    }
}

/// Re-encodes a PKCS#8 key as SEC1, which rind does not write.
fn sec1(curve: Curve, pkcs8: &[u8]) -> Vec<u8> {
    let algorithm = match curve {
        Curve::P256 => &signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        Curve::P384 => &signature::ECDSA_P384_SHA384_ASN1_SIGNING,
    };
    let key = signature::EcdsaKeyPair::from_pkcs8(algorithm, pkcs8).unwrap();
    key.private_key().as_der().unwrap().as_ref().to_vec()
}

fn endpoint(side: Side, suite: Suite, group: NamedGroup, now: Instant) -> (Dtls, Vec<u8>) {
    let builder = Config::builder()
        .with_crypto_provider(side.provider())
        .kx_groups(&[group]);
    let builder = match suite {
        Suite::Dtls12(suite) => builder.dtls12_cipher_suites(&[suite]),
        Suite::Dtls13(suite) => builder.dtls13_cipher_suites(&[suite]),
    };
    let config = Arc::new(builder.build().unwrap());

    let certificate = side.certificate();
    let der = certificate.certificate.clone();
    let dtls = match suite {
        Suite::Dtls12(_) => Dtls::new_12(config, certificate, now),
        Suite::Dtls13(_) => Dtls::new_13(config, certificate, now),
    };
    (dtls, der)
}

/// What one endpoint emitted while being polled.
#[derive(Default)]
struct Events {
    packets: Vec<Vec<u8>>,
    connected: bool,
    peer_cert: Option<Vec<u8>>,
    keying_material: Option<Vec<u8>>,
    data: Vec<Vec<u8>>,
}

fn poll(dtls: &mut Dtls, events: &mut Events) {
    let mut buf = vec![0u8; 2048];
    loop {
        match dtls.poll_output(&mut buf) {
            Output::Packet(p) => events.packets.push(p.to_vec()),
            Output::Connected => events.connected = true,
            Output::PeerCert(c) => events.peer_cert = Some(c.to_vec()),
            Output::KeyingMaterial(k, _) => events.keying_material = Some(k.to_vec()),
            Output::ApplicationData(d) => events.data.push(d.to_vec()),
            Output::Timeout(_) => return,
            other => panic!("unexpected {other:?}"),
        }
    }
}

/// Moves packets between the endpoints until both have seen `done`.
fn run(endpoints: &mut [(Dtls, Events); 2], mut now: Instant, done: fn(&Events) -> bool) {
    for _ in 0..20 {
        for (dtls, events) in endpoints.iter_mut() {
            dtls.handle_timeout(now).unwrap();
            poll(dtls, events);
        }
        let [(a, a_events), (b, b_events)] = endpoints;
        for packet in a_events.packets.drain(..) {
            b.handle_packet(&packet).unwrap();
        }
        for packet in b_events.packets.drain(..) {
            a.handle_packet(&packet).unwrap();
        }
        if endpoints.iter().all(|(_, events)| done(events)) {
            return;
        }
        now += Duration::from_millis(10);
    }
    panic!("endpoints never finished");
}

fn handshake(client: Side, server: Side, suite: Suite, group: NamedGroup) {
    let label = format!("{suite:?} {group:?} client={client:?} server={server:?}");
    let now = Instant::now();
    let (mut client_dtls, client_cert) = endpoint(client, suite, group, now);
    let (mut server_dtls, server_cert) = endpoint(server, suite, group, now);
    client_dtls.set_active(true);
    server_dtls.set_active(false);

    let mut endpoints = [
        (client_dtls, Events::default()),
        (server_dtls, Events::default()),
    ];
    run(&mut endpoints, now, |events| events.connected);

    let [(client_dtls, client_events), (server_dtls, server_events)] = &mut endpoints;
    let version = match suite {
        Suite::Dtls12(_) => ProtocolVersion::DTLS1_2,
        Suite::Dtls13(_) => ProtocolVersion::DTLS1_3,
    };
    assert_eq!(client_dtls.protocol_version(), Some(version), "{label}");
    assert_eq!(server_dtls.protocol_version(), Some(version), "{label}");
    assert_eq!(
        client_events.peer_cert.as_ref(),
        Some(&server_cert),
        "{label}"
    );
    assert_eq!(
        server_events.peer_cert.as_ref(),
        Some(&client_cert),
        "{label}"
    );
    assert!(client_events.keying_material.is_some(), "{label}");
    assert_eq!(
        client_events.keying_material, server_events.keying_material,
        "{label}"
    );

    client_dtls.send_application_data(b"from client").unwrap();
    server_dtls.send_application_data(b"from server").unwrap();
    run(&mut endpoints, now, |events| !events.data.is_empty());
    let [(_, client_events), (_, server_events)] = &endpoints;
    assert_eq!(server_events.data, [b"from client"], "{label}");
    assert_eq!(client_events.data, [b"from server"], "{label}");
}

fn every_suite_and_group(curve: Curve) {
    let suites = DTLS12
        .map(Suite::Dtls12)
        .into_iter()
        .chain(DTLS13.map(Suite::Dtls13));
    for suite in suites {
        for group in GROUPS {
            let rind = Side {
                rind: true,
                curve,
                format: KeyFormat::Pkcs8,
            };
            let aws_lc = Side {
                rind: false,
                ..rind
            };
            handshake(rind, aws_lc, suite, group);
            handshake(aws_lc, rind, suite, group);
        }
    }
}

#[test]
fn every_suite_and_group_with_p256_certificates() {
    every_suite_and_group(Curve::P256);
}

#[test]
fn every_suite_and_group_with_p384_certificates() {
    every_suite_and_group(Curve::P384);
}

// rind loads a SEC1 key and signs with a curve other than its peer's.
#[test]
fn sec1_keys_and_mixed_curves() {
    for (rind_curve, peer_curve) in [(Curve::P256, Curve::P384), (Curve::P384, Curve::P256)] {
        let rind = Side {
            rind: true,
            curve: rind_curve,
            format: KeyFormat::Sec1,
        };
        let aws_lc = Side {
            rind: false,
            curve: peer_curve,
            format: KeyFormat::Pkcs8,
        };
        for suite in [Suite::Dtls12(DTLS12[0]), Suite::Dtls13(DTLS13[0])] {
            handshake(rind, aws_lc, suite, NamedGroup::X25519);
            handshake(aws_lc, rind, suite, NamedGroup::X25519);
        }
    }
}
