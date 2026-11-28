//! rustls over each provider, with the client and server in one process, so
//! each row is what both peers pay together. Each function is a group of
//! rows, and its argument names the row in it, such as `x25519/rind` or
//! `aes128-gcm/rind/64B`: its IDs put the provider before a records row's
//! size, and which rows a provider has depends on what it offers.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::fmt;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;
#[cfg(not(target_arch = "xtensa"))]
use std::io::{Read, Write};
#[cfg(not(target_arch = "xtensa"))]
use std::panic::{self, AssertUnwindSafe};
#[cfg(not(target_arch = "xtensa"))]
use std::sync::{Arc, mpsc};
#[cfg(not(target_arch = "xtensa"))]
use std::thread;
#[cfg(not(target_arch = "xtensa"))]
use std::time::{Duration, Instant};

#[cfg(not(target_arch = "xtensa"))]
use common::Size;
#[cfg(not(target_arch = "xtensa"))]
use rustls::client::Resumption;
#[cfg(not(target_arch = "xtensa"))]
use rustls::crypto::CryptoProvider;
#[cfg(not(target_arch = "xtensa"))]
use rustls::pki_types::pem::PemObject;
#[cfg(not(target_arch = "xtensa"))]
use rustls::pki_types::{CertificateDer, PrivateKeyDer};
#[cfg(not(target_arch = "xtensa"))]
use rustls::{
    CipherSuite, ClientConfig, ClientConnection, Connection, HandshakeKind, NamedGroup,
    RootCertStore, ServerConfig, ServerConnection,
};
#[cfg(not(target_arch = "xtensa"))]
use swole::{Iterations, bench};

/// A rustls crypto provider, shown as its rows name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg(not(target_arch = "xtensa"))]
enum Provider {
    Ring,
    AwsLcRs,
    Rind,
    #[cfg(graviola)]
    Graviola,
    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    Openssl,
}

#[cfg(not(target_arch = "xtensa"))]
impl fmt::Display for Provider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Ring => "ring",
            Self::AwsLcRs => "aws-lc-rs",
            Self::Rind => "rind",
            #[cfg(graviola)]
            Self::Graviola => "graviola",
            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            Self::Openssl => "openssl",
        })
    }
}

/// Whether Graviola runs here: it panics on a CPU without the features its
/// `verify_cpu_features` asserts.
#[cfg(all(graviola, target_arch = "x86_64"))]
#[cfg(not(target_arch = "xtensa"))]
fn graviola_runs() -> bool {
    use std::arch::is_x86_feature_detected as has;
    has!("aes") && has!("pclmulqdq") && has!("bmi1") && has!("adx") && has!("avx") && has!("avx2")
}

#[cfg(all(graviola, target_arch = "aarch64"))]
#[cfg(not(target_arch = "xtensa"))]
fn graviola_runs() -> bool {
    use std::arch::is_aarch64_feature_detected as has;
    has!("neon") && has!("aes") && has!("pmull") && has!("sha2")
}

#[cfg(not(target_arch = "xtensa"))]
impl Provider {
    /// The providers this build has that run on this CPU. Graviola asserts
    /// its CPU features when it builds a provider, and swole builds every
    /// row's argument list in each benchmark's process, so a CPU without
    /// them, such as Haswell, has no Graviola row rather than every row
    /// panicking. The weekly count leaves Graviola's rows out by name.
    fn all() -> Vec<Self> {
        let mut all = vec![Self::Ring, Self::AwsLcRs, Self::Rind];
        #[cfg(graviola)]
        if graviola_runs() {
            all.push(Self::Graviola);
        }
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        all.push(Self::Openssl);
        all
    }

    fn provider(self) -> CryptoProvider {
        match self {
            Self::Ring => rustls::crypto::ring::default_provider(),
            Self::AwsLcRs => rustls::crypto::aws_lc_rs::default_provider(),
            Self::Rind => rind_rustls::default_provider(),
            #[cfg(graviola)]
            Self::Graviola => rustls_graviola::default_provider(),
            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            Self::Openssl => rustls_openssl::default_provider(),
        }
    }

    /// The provider, offering only `group`, or `None` where it lacks it.
    fn with_group(self, group: NamedGroup) -> Option<CryptoProvider> {
        let all = match self {
            Self::Ring => rustls::crypto::ring::ALL_KX_GROUPS.to_vec(),
            Self::AwsLcRs => rustls::crypto::aws_lc_rs::ALL_KX_GROUPS.to_vec(),
            Self::Rind => rind_rustls::ALL_KX_GROUPS.to_vec(),
            #[cfg(graviola)]
            Self::Graviola => rustls_graviola::kx::ALL_KX_GROUPS.to_vec(),
            // What the linked OpenSSL offers: ML-KEM needs 3.5.
            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            Self::Openssl => rustls_openssl::kx_group::available_groups(),
        };
        let group = *all.iter().find(|g| g.name() == group)?;
        Some(CryptoProvider {
            kx_groups: vec![group],
            ..self.provider()
        })
    }

    /// The provider, offering only the TLS 1.3 `suite`.
    fn with_suite(self, suite: CipherSuite) -> CryptoProvider {
        let provider = self.provider();
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

    /// The DIT guard rind's rows hold across their calls, on the thread that
    /// makes them.
    fn dit(self) -> Option<rind::cpu::Dit> {
        (self == Self::Rind).then(rind::cpu::Dit::hold)
    }
}

/// A key in `rind-rustls/tests/keys`, and the client and server configs for
/// it, or `None` where the provider cannot sign with it.
#[cfg(not(target_arch = "xtensa"))]
fn configs(
    provider: CryptoProvider,
    key: &str,
    resumption: bool,
) -> Option<(Arc<ClientConfig>, Arc<ServerConfig>)> {
    // `RIND_BENCH_KEYS_DIR`, read at run time, names a copy of
    // `rind-rustls/tests/keys`, for a binary run on a device where the
    // build-time checkout path does not exist.
    let keys = std::env::var("RIND_BENCH_KEYS_DIR")
        .unwrap_or_else(|_| format!("{}/../rind-rustls/tests/keys", env!("CARGO_MANIFEST_DIR")));
    let dir = format!("{keys}/{key}");
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
#[cfg(not(target_arch = "xtensa"))]
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
#[cfg(not(target_arch = "xtensa"))]
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

#[cfg(not(target_arch = "xtensa"))]
fn handshake_kind(server: &Connection) -> HandshakeKind {
    match server {
        Connection::Server(server) => server.handshake_kind().unwrap(),
        Connection::Client(_) => unreachable!(),
    }
}

/// A client and server config, with the DIT guard rind's rows hold.
#[cfg(not(target_arch = "xtensa"))]
struct Configs {
    client: Arc<ClientConfig>,
    server: Arc<ServerConfig>,
    _dit: Option<rind::cpu::Dit>,
}

/// A handshake row's argument, shown as `{group or key}/{provider}`: a
/// provider offering one key exchange group, with a certificate of one key.
#[derive(Clone, Copy)]
#[cfg(not(target_arch = "xtensa"))]
struct Handshake {
    provider: Provider,
    group: (&'static str, NamedGroup),
    key: &'static str,
    /// Whether the row is one of several keys, so named by the key.
    by_key: bool,
}

#[cfg(not(target_arch = "xtensa"))]
impl fmt::Display for Handshake {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = if self.by_key { self.key } else { self.group.0 };
        write!(f, "{name}/{}", self.provider)
    }
}

#[cfg(not(target_arch = "xtensa"))]
const GROUPS: [(&str, NamedGroup); 5] = [
    ("x25519mlkem768", NamedGroup::X25519MLKEM768),
    ("x25519", NamedGroup::X25519),
    ("secp256r1", NamedGroup::secp256r1),
    ("secp384r1", NamedGroup::secp384r1),
    ("secp521r1", NamedGroup::secp521r1),
];

#[cfg(not(target_arch = "xtensa"))]
const KEYS: [&str; 7] = [
    "ecdsa-p256",
    "ecdsa-p384",
    "ecdsa-p521",
    "ed25519",
    "rsa-2048",
    "rsa-3072",
    "rsa-4096",
];

#[cfg(not(target_arch = "xtensa"))]
impl Handshake {
    /// Each provider over each group, with an ECDSA P-256 certificate, where
    /// the provider offers the group.
    fn by_group() -> Vec<Self> {
        let rows = GROUPS.into_iter().flat_map(|group| {
            Provider::all().into_iter().map(move |provider| Self {
                provider,
                group,
                key: "ecdsa-p256",
                by_key: false,
            })
        });
        rows.filter(|row| row.configs(false).is_some()).collect()
    }

    /// Each provider over X25519 with each certificate key it signs with.
    fn by_key() -> Vec<Self> {
        let rows = KEYS.into_iter().flat_map(|key| {
            Provider::all().into_iter().map(move |provider| Self {
                provider,
                group: GROUPS[1],
                key,
                by_key: true,
            })
        });
        rows.filter(|row| row.configs(false).is_some()).collect()
    }

    fn configs(self, resumption: bool) -> Option<Configs> {
        let provider = self.provider.with_group(self.group.1)?;
        let (client, server) = configs(provider, self.key, resumption)?;
        Some(Configs {
            client,
            server,
            _dit: None,
        })
    }

    /// A full handshake's configs, checked to run one.
    fn full(self) -> Configs {
        let configs = self.configs(false).unwrap();
        assert_eq!(
            handshake_kind(&handshake(&configs.client, &configs.server).1),
            HandshakeKind::Full
        );
        Configs {
            _dit: self.provider.dit(),
            ..configs
        }
    }

    /// A resumed handshake's configs, the client holding tickets from a first
    /// handshake, checked to resume.
    fn resumed(self) -> Configs {
        let configs = self.configs(true).unwrap();
        handshake(&configs.client, &configs.server);
        assert_eq!(
            handshake_kind(&handshake(&configs.client, &configs.server).1),
            HandshakeKind::Resumed
        );
        Configs {
            _dit: self.provider.dit(),
            ..configs
        }
    }
}

/// A full TLS 1.3 handshake per key exchange group, with an ECDSA P-256
/// certificate.
#[bench(args = Handshake::by_group(), setup = Handshake::full)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_full_handshake_group(configs: &Configs) {
    black_box(handshake(&configs.client, &configs.server));
}

/// A full TLS 1.3 handshake per certificate key, over X25519.
#[bench(args = Handshake::by_key(), setup = Handshake::full)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_full_handshake_key(configs: &Configs) {
    black_box(handshake(&configs.client, &configs.server));
}

/// A TLS 1.3 handshake resumed from a ticket, per key exchange group: each
/// resumption takes one ticket and the server sends more.
#[bench(args = Handshake::by_group(), setup = Handshake::resumed)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_resumed_handshake(configs: &Configs) {
    black_box(handshake(&configs.client, &configs.server));
}

/// A threaded row's argument, shown as `x25519/{provider}`: a provider
/// running handshakes of one kind over X25519.
#[derive(Clone, Copy)]
#[cfg(not(target_arch = "xtensa"))]
struct Threaded {
    provider: Provider,
    kind: HandshakeKind,
}

#[cfg(not(target_arch = "xtensa"))]
impl fmt::Display for Threaded {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x25519/{}", self.provider)
    }
}

#[cfg(not(target_arch = "xtensa"))]
impl Threaded {
    fn each(kind: HandshakeKind) -> Vec<Self> {
        let each = |provider| Self { provider, kind };
        Provider::all().into_iter().map(each).collect()
    }
}

/// Threads, one per logical CPU, each with its own client and server, running
/// handshakes of one kind on request.
///
/// Each thread keeps its own pair, as the single-thread rows do: a shared
/// server's session cache gains a ticket per resumption and evicts the
/// oldest, so a thread that falls behind finds its ticket gone and runs a full
/// handshake. The threads live as long as the pool, so per-thread state a
/// provider sets up on first use, such as aws-lc's, is not timed.
#[cfg(not(target_arch = "xtensa"))]
struct Pool {
    /// Each thread's queue of handshake counts to run.
    work: Vec<mpsc::Sender<u64>>,
    /// Whether each request ran, every handshake of the pool's kind.
    done: mpsc::Receiver<bool>,
    threads: Vec<thread::JoinHandle<()>>,
    /// What a failure names.
    what: String,
}

#[cfg(not(target_arch = "xtensa"))]
impl Pool {
    /// The pool, past each thread's first handshake, which seeds a resuming
    /// client's tickets.
    fn new(Threaded { provider, kind }: Threaded) -> Self {
        let count = thread::available_parallelism().unwrap().get();
        // bench-report reports these rows as running on every logical CPU, so a
        // run held to fewer, by affinity or a cgroup quota, must not pass for one.
        if let Ok(cpus) = std::env::var("RIND_BENCH_CPUS") {
            let cpus: usize = cpus.parse().expect("RIND_BENCH_CPUS is a count");
            assert_eq!(
                count, cpus,
                "this process may use {count} of the host's {cpus} logical CPUs"
            );
        }
        let resumption = kind == HandshakeKind::Resumed;
        let (done_tx, done) = mpsc::channel();
        let (work, threads) = (0..count)
            .map(|_| {
                let (work, jobs) = mpsc::channel::<u64>();
                let done_tx = done_tx.clone();
                let thread = thread::spawn(move || {
                    // Held for the thread's life, so the timed handshakes run under it.
                    let _dit = provider.dit();
                    // Each step reports whether it ran and every handshake was
                    // of `kind`, rather than panic and leave the main thread
                    // waiting on this one.
                    let report = |f: &mut dyn FnMut() -> bool| {
                        let ok = panic::catch_unwind(AssertUnwindSafe(f));
                        done_tx.send(matches!(ok, Ok(true))).unwrap();
                    };
                    let mut pair = None;
                    report(&mut || {
                        let with = provider.with_group(NamedGroup::X25519).unwrap();
                        let (client, server) = configs(with, "ecdsa-p256", resumption).unwrap();
                        handshake(&client, &server);
                        let ok = handshake_kind(&handshake(&client, &server).1) == kind;
                        pair = Some((client, server));
                        ok
                    });
                    let Some((client, server)) = pair else {
                        return;
                    };
                    for n in jobs {
                        report(&mut || {
                            (0..n).all(|_| handshake_kind(&handshake(&client, &server).1) == kind)
                        });
                    }
                });
                (work, thread)
            })
            .unzip();
        let pool = Self {
            work,
            done,
            threads,
            what: format!("a {kind:?} handshake over {provider}"),
        };
        pool.wait();
        pool
    }

    /// Waits for every thread's last request.
    fn wait(&self) {
        let ok = (0..self.work.len()).all(|_| self.done.recv().unwrap());
        assert!(ok, "{} failed or was not of its kind", self.what);
    }

    /// Runs `iterations` handshakes, spread over the threads, returning the
    /// wall time they took.
    fn run(&self, iterations: Iterations) -> Duration {
        let (total, threads) = (iterations.get(), self.work.len() as u64);
        let start = Instant::now();
        for (work, i) in self.work.iter().zip(0..) {
            work.send(total / threads + u64::from(i < total % threads))
                .unwrap();
        }
        self.wait();
        start.elapsed()
    }
}

#[cfg(not(target_arch = "xtensa"))]
impl Drop for Pool {
    fn drop(&mut self) {
        // Closing each queue ends its thread.
        self.work.clear();
        for thread in self.threads.drain(..) {
            thread.join().unwrap();
        }
    }
}

/// Full TLS 1.3 handshakes over X25519 with an ECDSA P-256 certificate, on
/// every logical CPU at once. A row's time is the machine's: wall time over
/// the handshakes all threads completed, so its ratio to the single-thread
/// row is how throughput scales. The weekly instruction count leaves these
/// rows out: what each thread runs while the others wait is the scheduler's.
#[bench(args = Threaded::each(HandshakeKind::Full), setup = Pool::new)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_full_handshake_threads(pool: &mut Pool, iterations: Iterations) -> Duration {
    pool.run(iterations)
}

/// Resumed TLS 1.3 handshakes, as `rustls_full_handshake_threads` runs full
/// ones.
#[bench(args = Threaded::each(HandshakeKind::Resumed), setup = Pool::new)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_resumed_handshake_threads(pool: &mut Pool, iterations: Iterations) -> Duration {
    pool.run(iterations)
}

/// A connected pair, past its handshake, with a buffer for the records
/// between them, and the data to send and room to read it.
#[cfg(not(target_arch = "xtensa"))]
struct Pair {
    client: Connection,
    server: Connection,
    buf: Vec<u8>,
    data: Vec<u8>,
    out: Vec<u8>,
    _dit: Option<rind::cpu::Dit>,
}

#[cfg(not(target_arch = "xtensa"))]
impl Pair {
    /// Sends the data from the server to the client in one record, which the
    /// client reads back.
    fn record(&mut self) {
        self.server.writer().write_all(&self.data).unwrap();
        transfer(&mut self.server, &mut self.client, &mut self.buf);
        self.client.reader().read_exact(&mut self.out).unwrap();
    }
}

#[cfg(not(target_arch = "xtensa"))]
const SUITES: [(&str, CipherSuite); 3] = [
    ("aes128-gcm", CipherSuite::TLS13_AES_128_GCM_SHA256),
    ("aes256-gcm", CipherSuite::TLS13_AES_256_GCM_SHA384),
    (
        "chacha20poly1305",
        CipherSuite::TLS13_CHACHA20_POLY1305_SHA256,
    ),
];

/// A records row's argument, shown as `{suite}/{provider}`, then `/{size}`
/// where the row has several: a provider offering only one TLS 1.3 suite,
/// sending records of one size.
#[derive(Clone, Copy)]
#[cfg(not(target_arch = "xtensa"))]
struct Records {
    provider: Provider,
    suite: (&'static str, CipherSuite),
    size: Size,
    /// Whether the row is one of several sizes, so named by it.
    sized: bool,
}

#[cfg(not(target_arch = "xtensa"))]
impl fmt::Display for Records {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.suite.0, self.provider)?;
        if self.sized {
            write!(f, "/{}", self.size)?;
        }
        Ok(())
    }
}

#[cfg(not(target_arch = "xtensa"))]
impl Records {
    /// A pair past its handshake.
    fn pair(self) -> Pair {
        let provider = self.provider.with_suite(self.suite.1);
        let (client, server) = configs(provider, "ecdsa-p256", false).unwrap();
        let (client, server) = handshake(&client, &server);
        Pair {
            client,
            server,
            buf: Vec::new(),
            data: vec![0x5a; self.size.len],
            out: vec![0; self.size.len],
            _dit: self.provider.dit(),
        }
    }
}

/// A full record.
#[cfg(not(target_arch = "xtensa"))]
const RECORD: usize = 16384;

/// The bulk rows: each provider over each suite, in full records.
#[cfg(not(target_arch = "xtensa"))]
fn bulk_rows() -> Vec<Records> {
    let rows = SUITES.into_iter().flat_map(|suite| {
        Provider::all().into_iter().map(move |provider| Records {
            provider,
            suite,
            size: Size::new(RECORD, "16KB"),
            sized: false,
        })
    });
    rows.collect()
}

/// 1 MB from server to client in full records, per TLS 1.3 cipher suite:
/// each byte is sealed once and opened once.
#[bench(args = bulk_rows(), setup = Records::pair)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_bulk(pair: &mut Pair) {
    for _ in 0..(1 << 20) / RECORD {
        pair.record();
    }
}

/// The small records' sizes.
#[cfg(not(target_arch = "xtensa"))]
const RECORD_SIZES: [Size; 3] = [
    Size::new(64, "64B"),
    Size::new(256, "256B"),
    Size::new(1024, "1KB"),
];

/// The records rows: each provider over AES-128-GCM and ChaCha20-Poly1305,
/// in records of each size.
#[cfg(not(target_arch = "xtensa"))]
fn records_rows() -> Vec<Records> {
    let suites = [SUITES[0], SUITES[2]];
    let rows = suites.into_iter().flat_map(|suite| {
        Provider::all().into_iter().flat_map(move |provider| {
            RECORD_SIZES.into_iter().map(move |size| Records {
                provider,
                suite,
                size,
                sized: true,
            })
        })
    });
    rows.collect()
}

/// One small record from server to client, per TLS 1.3 cipher suite and
/// size, as chat messages, game state, and MoQ's control messages send them:
/// what rustls and each provider add per record, which bulk's full records
/// spread over 16 KB.
#[bench(args = records_rows(), setup = Records::pair)]
#[cfg(not(target_arch = "xtensa"))]
fn rustls_records(pair: &mut Pair) {
    pair.record()
}

/// rind's smallest record again without its DIT guard, where the toggle is
/// the largest share of a record. See `common::Dit`.
#[cfg(target_arch = "aarch64")]
#[cfg(not(target_arch = "xtensa"))]
mod dit_per_call {
    use swole::bench;

    use super::*;

    fn pair(records: Records) -> Pair {
        Pair {
            _dit: None,
            ..records.pair()
        }
    }

    const ROW: Records = Records {
        provider: Provider::Rind,
        suite: SUITES[0],
        size: RECORD_SIZES[0],
        sized: true,
    };

    #[bench(args = [ROW], setup = pair)]
    fn rustls_records(pair: &mut Pair) {
        pair.record()
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
