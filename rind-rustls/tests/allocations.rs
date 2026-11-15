//! How many heap allocations one full TLS 1.3 handshake makes, both peers
//! together, per certificate key type. Pinned on x86_64 alone, where it was
//! measured, on the assembly and portable backends alike. RSA's private-key
//! routines allocate differently by backend and with ADX or AVX-512 IFMA, so
//! RSA certificates are not pinned.
#![cfg(target_arch = "x86_64")]

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::Arc;

use rustls::client::Resumption;
use rustls::pki_types::pem::PemObject;
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
use rustls::{
    ClientConfig, ClientConnection, Connection, RootCertStore, ServerConfig, ServerConnection,
};

/// Counts allocations per thread, so that tests running beside this one
/// don't add to its count.
struct Counting;

thread_local! {
    static ALLOCATIONS: Cell<u64> = const { Cell::new(0) };
}

fn counted() {
    ALLOCATIONS.with(|n| n.set(n.get() + 1));
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        counted();
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        counted();
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        counted();
        unsafe { System.realloc(ptr, layout, new_size) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// The client and server configs for a key in `tests/keys`.
fn configs(key: &str) -> (Arc<ClientConfig>, Arc<ServerConfig>) {
    let dir = format!("{}/tests/keys/{key}", env!("CARGO_MANIFEST_DIR"));
    let chain = CertificateDer::pem_file_iter(format!("{dir}/end.fullchain"))
        .unwrap()
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let private_key = PrivateKeyDer::from_pem_file(format!("{dir}/end.key")).unwrap();
    let mut roots = RootCertStore::empty();
    roots
        .add(CertificateDer::from_pem_file(format!("{dir}/ca.cert")).unwrap())
        .unwrap();
    let provider = Arc::new(match std::env::var("ALLOCATIONS_PROVIDER").as_deref() {
        // For comparison by hand; the test's counts are rind's. This counts
        // only aws-lc-rs's Rust allocations, not AWS-LC's own `malloc` calls.
        Ok("aws-lc-rs") => rustls::crypto::aws_lc_rs::default_provider(),
        _ => rind_rustls::default_provider(),
    });
    let server = ServerConfig::builder_with_provider(provider.clone())
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_no_client_auth()
        .with_single_cert(chain, private_key)
        .unwrap();
    let mut client = ClientConfig::builder_with_provider(provider)
        .with_protocol_versions(&[&rustls::version::TLS13])
        .unwrap()
        .with_root_certificates(roots)
        .with_no_client_auth();
    client.resumption = Resumption::disabled();
    (client.into(), server.into())
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

/// The allocations one full handshake makes, both peers' and the server's
/// session tickets included.
fn count(client: &Arc<ClientConfig>, server: &Arc<ServerConfig>) -> u64 {
    // Allocated before counting, and sized for any flight so that it never
    // grows: the harness's buffer is not the handshake's.
    let mut buf = Vec::with_capacity(1 << 16);
    let before = ALLOCATIONS.with(Cell::get);
    let mut client = Connection::Client(
        ClientConnection::new(client.clone(), "localhost".try_into().unwrap()).unwrap(),
    );
    let mut server = Connection::Server(ServerConnection::new(server.clone()).unwrap());
    while client.is_handshaking() || server.is_handshaking() || server.wants_write() {
        transfer(&mut client, &mut server, &mut buf);
        transfer(&mut server, &mut client, &mut buf);
    }
    ALLOCATIONS.with(Cell::get) - before
}

/// Each key type's allocations per handshake over rind-rustls's default
/// provider, which leads with X25519MLKEM768.
const EXPECTED: [(&str, u64); 4] = [
    ("ecdsa-p256", 245),
    ("ecdsa-p384", 249),
    ("ecdsa-p521", 253),
    ("ed25519", 245),
];

#[test]
fn handshake_allocations() {
    let mut wrong = Vec::new();
    for (key, expected) in EXPECTED {
        let (client, server) = configs(key);
        // The first handshake fills one-time state, such as the CPU features.
        count(&client, &server);
        // rustls shuffles the ClientHello's extensions, which moves where its
        // buffers grow, so a handshake makes a few more than the fewest about
        // half the time; the fewest of 32 is the fewest every time in practice.
        let got = (0..32).map(|_| count(&client, &server)).min().unwrap();
        if got != expected {
            wrong.push(format!("{key}: {got}, expected {expected}"));
        }
    }
    assert!(
        wrong.is_empty(),
        "a handshake's allocation count changed; if the change was meant, update EXPECTED:\n{}",
        wrong.join("\n")
    );
}
