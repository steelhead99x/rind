//! rustls over each provider, with the client and server in one process, so
//! each row is what both peers pay together.

mod criterion;
use std::io::{Read, Write};
use std::sync::Arc;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use rustls::client::Resumption;
use rustls::crypto::CryptoProvider;
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use rustls::{
    CipherSuite, ClientConfig, ClientConnection, Connection, HandshakeKind, NamedGroup,
    RootCertStore, ServerConfig, ServerConnection,
};

/// The providers this build and CPU have. The setup below runs every
/// provider, whatever criterion's filter, so it can't leave Graviola to it.
fn providers() -> impl Iterator<Item = &'static str> {
    ["ring"]
        .into_iter()
        .chain(cfg!(not(any(target_arch = "xtensa", target_os = "none"))).then_some("aws-lc-rs"))
        .chain(["rind"])
        .chain(graviola_runs().then_some("graviola"))
        .chain(cfg!(all(feature = "__bench_openssl", target_family = "unix")).then_some("openssl"))
}

/// Whether Graviola runs here: it panics on a CPU without the features it
/// asserts in its `verify_cpu_features`.
#[cfg(target_arch = "x86_64")]
fn graviola_runs() -> bool {
    use std::arch::is_x86_feature_detected as has;
    has!("aes") && has!("pclmulqdq") && has!("bmi1") && has!("adx") && has!("avx") && has!("avx2")
}

#[cfg(target_arch = "aarch64")]
fn graviola_runs() -> bool {
    use std::arch::is_aarch64_feature_detected as has;
    has!("neon") && has!("aes") && has!("pmull") && has!("sha2")
}

#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
fn graviola_runs() -> bool {
    false
}

fn provider(name: &str) -> CryptoProvider {
    match name {
        "ring" => rustls::crypto::ring::default_provider(),
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        "aws-lc-rs" => rustls::crypto::aws_lc_rs::default_provider(),
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        "graviola" => rustls_graviola::default_provider(),
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        "openssl" => rustls_openssl::default_provider(),
        _ => rind_rustls::default_provider(),
    }
}

/// `name`'s provider, offering only `group`, or `None` where it lacks it.
fn with_group(name: &str, group: NamedGroup) -> Option<CryptoProvider> {
    let all = match name {
        "ring" => rustls::crypto::ring::ALL_KX_GROUPS.to_vec(),
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        "aws-lc-rs" => rustls::crypto::aws_lc_rs::ALL_KX_GROUPS.to_vec(),
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        "graviola" => rustls_graviola::kx::ALL_KX_GROUPS.to_vec(),
        // What the linked OpenSSL offers: ML-KEM needs 3.5.
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        "openssl" => rustls_openssl::kx_group::available_groups(),
        _ => rind_rustls::ALL_KX_GROUPS.to_vec(),
    };
    let group = *all.iter().find(|g| g.name() == group)?;
    Some(CryptoProvider {
        kx_groups: vec![group],
        ..provider(name)
    })
}

/// `name`'s provider, offering only the TLS 1.3 `suite`.
fn with_suite(name: &str, suite: CipherSuite) -> CryptoProvider {
    let provider = provider(name);
    let suite = *provider
        .cipher_suites
        .iter()
        .find(|s| s.suite() == suite)
        .unwrap();
    CryptoProvider {
        cipher_suites: vec![suite],
        ..provider
    }
}

/// A key in `rind-rustls/tests/keys`, and the client and server configs for
/// it, or `None` where the provider cannot sign with it.
fn configs(
    provider: CryptoProvider,
    key: &str,
    resumption: bool,
) -> Option<(Arc<ClientConfig>, Arc<ServerConfig>)> {
    let dir = format!(
        "{}/../rind-rustls/tests/keys/{key}",
        env!("CARGO_MANIFEST_DIR")
    );
    let chain = CertificateDer::pem_file_iter(format!("{dir}/end.fullchain"))
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let private_key = PrivateKeyDer::from_pem_file(format!("{dir}/end.key")).unwrap();
    let mut roots = RootCertStore::empty();
    roots
        .add(CertificateDer::from_pem_file(format!("{dir}/ca.cert")).unwrap())
        .unwrap();

    let provider = Arc::new(provider);
    let server = ServerConfig::builder_with_provider(provider.clone())
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(chain, private_key)
        .ok()?;
    let mut client = ClientConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    if !resumption {
        client.resumption = Resumption::disabled();
    }
    Some((client.into(), server.into()))
}

/// Moves every record `from` has queued into `to`.
fn transfer(from: &mut Connection, to: &mut Connection, buf: &mut Vec<u8>) {
    while from.wants_write() {
        buf.clear();
        from.write_tls(buf).unwrap();
        let mut records = &buf[..];
        while !records.is_empty() {
            to.read_tls(&mut records).unwrap();
            to.process_new_packets().unwrap();
        }
    }
}

/// Runs a handshake to completion, including the server's session tickets.
fn handshake(client: &Arc<ClientConfig>, server: &Arc<ServerConfig>) -> (Connection, Connection) {
    let mut client = Connection::Client(
        ClientConnection::new(client.clone(), "localhost".try_into().unwrap()).unwrap(),
    );
    let mut server = Connection::Server(ServerConnection::new(server.clone()).unwrap());
    let mut buf = Vec::new();
    while client.is_handshaking() || server.is_handshaking() || server.wants_write() {
        transfer(&mut client, &mut server, &mut buf);
        transfer(&mut server, &mut client, &mut buf);
    }
    (client, server)
}

fn handshake_kind(server: &Connection) -> HandshakeKind {
    match server {
        Connection::Server(server) => server.handshake_kind().unwrap(),
        Connection::Client(_) => unreachable!(),
    }
}

const GROUPS: [(&str, NamedGroup); 5] = [
    ("x25519mlkem768", NamedGroup::X25519MLKEM768),
    ("x25519", NamedGroup::X25519),
    ("secp256r1", NamedGroup::secp256r1),
    ("secp384r1", NamedGroup::secp384r1),
    ("secp521r1", NamedGroup::secp521r1),
];

const KEYS: [&str; 7] = [
    "ecdsa-p256",
    "ecdsa-p384",
    "ecdsa-p521",
    "ed25519",
    "rsa-2048",
    "rsa-3072",
    "rsa-4096",
];

/// A full TLS 1.3 handshake per key exchange group, with an ECDSA P-256
/// certificate.
fn full_handshake_by_group(c: &mut Criterion) {
    let mut group = c.benchmark_group("rustls-full-handshake-group");
    group.throughput(Throughput::Elements(1));
    for (group_name, named) in GROUPS {
        for name in providers() {
            let Some(provider) = with_group(name, named) else {
                continue;
            };
            let (client, server) = configs(provider, "ecdsa-p256", false).unwrap();
            assert_eq!(
                handshake_kind(&handshake(&client, &server).1),
                HandshakeKind::Full
            );
            group.bench_function(format!("{group_name}/{name}"), |b| {
                b.iter(|| handshake(&client, &server))
            });
        }
    }
}

/// A full TLS 1.3 handshake per certificate key, over X25519.
fn full_handshake_by_key(c: &mut Criterion) {
    let mut group = c.benchmark_group("rustls-full-handshake-key");
    group.throughput(Throughput::Elements(1));
    for key in KEYS {
        for name in providers() {
            let provider = with_group(name, NamedGroup::X25519).unwrap();
            let Some((client, server)) = configs(provider, key, false) else {
                continue;
            };
            group.bench_function(format!("{key}/{name}"), |b| {
                b.iter(|| handshake(&client, &server))
            });
        }
    }
}

/// A TLS 1.3 handshake resumed from a ticket, per key exchange group: each
/// resumption takes one ticket and the server sends more.
fn resumed_handshake(c: &mut Criterion) {
    let mut group = c.benchmark_group("rustls-resumed-handshake");
    group.throughput(Throughput::Elements(1));
    for (group_name, named) in GROUPS {
        for name in providers() {
            let Some(provider) = with_group(name, named) else {
                continue;
            };
            let (client, server) = configs(provider, "ecdsa-p256", true).unwrap();
            handshake(&client, &server);
            assert_eq!(
                handshake_kind(&handshake(&client, &server).1),
                HandshakeKind::Resumed
            );
            group.bench_function(format!("{group_name}/{name}"), |b| {
                b.iter(|| handshake(&client, &server))
            });
        }
    }
}

/// 1 MB from server to client in full records, per TLS 1.3 cipher suite:
/// each byte is sealed once and opened once.
fn bulk(c: &mut Criterion) {
    const LEN: usize = 1 << 20;
    const RECORD: usize = 16384;
    let mut group = c.benchmark_group("rustls-bulk");
    group.throughput(Throughput::Bytes(LEN as u64));
    let data = vec![0x5a; RECORD];
    let mut out = vec![0; RECORD];
    for (suite_name, suite) in [
        ("aes128-gcm", CipherSuite::TLS13_AES_128_GCM_SHA256),
        ("aes256-gcm", CipherSuite::TLS13_AES_256_GCM_SHA384),
        (
            "chacha20poly1305",
            CipherSuite::TLS13_CHACHA20_POLY1305_SHA256,
        ),
    ] {
        for name in providers() {
            let (client, server) = configs(with_suite(name, suite), "ecdsa-p256", false).unwrap();
            let (mut client, mut server) = handshake(&client, &server);
            let mut buf = Vec::new();
            group.bench_function(format!("{suite_name}/{name}"), |b| {
                b.iter(|| {
                    for _ in 0..LEN / RECORD {
                        server.writer().write_all(&data).unwrap();
                        transfer(&mut server, &mut client, &mut buf);
                        client.reader().read_exact(&mut out).unwrap();
                    }
                })
            });
        }
    }
}

criterion_group!(
    benches,
    full_handshake_by_group,
    full_handshake_by_key,
    resumed_handshake,
    bulk
);
criterion_main!(benches);
