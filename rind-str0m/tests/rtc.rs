//! A str0m session between a peer on rind and a peer on aws-lc-rs: STUN
//! MESSAGE-INTEGRITY, the DTLS handshake and fingerprint check, then SRTP and
//! SRTCP in both directions.

use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Arc;
use std::time::{Duration, Instant};

use str0m::crypto::CryptoProvider;
use str0m::crypto::dtls::DtlsVersion;
use str0m::format::Codec;
use str0m::media::{MediaKind, Mid};
use str0m::net::{Protocol, Receive};
use str0m::rtp::{RawPacket, RtpWrite, Ssrc};
use str0m::{Candidate, Event, Input, Output, Rtc};

struct Peer {
    rtc: Rtc,
    addr: SocketAddr,
    timeout: Instant,
    connected: bool,
    rtp: Vec<Vec<u8>>,
    rtcp: usize,
}

impl Peer {
    fn new(provider: CryptoProvider, version: DtlsVersion, port: u16, now: Instant) -> Self {
        let rtc = Rtc::builder()
            .set_crypto_provider(Arc::new(provider))
            .set_dtls_version(version)
            .set_rtp_mode(true)
            .enable_raw_packets(true)
            .build(now);
        Self {
            rtc,
            addr: (Ipv4Addr::LOCALHOST, port).into(),
            timeout: now,
            connected: false,
            rtp: Vec::new(),
            rtcp: 0,
        }
    }

    /// Runs until the next timeout, queueing the datagrams it sends.
    fn poll(&mut self, sent: &mut Vec<Datagram>) {
        loop {
            match self.rtc.poll_output().unwrap() {
                Output::Timeout(at) => {
                    self.timeout = at;
                    return;
                }
                Output::Transmit(t) => sent.push((t.source, t.destination, t.contents.to_vec())),
                Output::Event(Event::Connected) => self.connected = true,
                Output::Event(Event::RtpPacket(p)) => self.rtp.push(p.payload.to_vec()),
                Output::Event(Event::RawPacket(p)) => {
                    if let RawPacket::RtcpRx(_) = *p {
                        self.rtcp += 1;
                    }
                }
                Output::Event(_) => {}
            }
        }
    }
}

type Datagram = (SocketAddr, SocketAddr, Vec<u8>);

/// Delivers `datagrams` to `to`, queueing its replies.
fn deliver(to: &mut Peer, datagrams: Vec<Datagram>, now: Instant, replies: &mut Vec<Datagram>) {
    for (source, destination, contents) in datagrams {
        let receive = Receive {
            proto: Protocol::Udp,
            source,
            destination,
            contents: contents.as_slice().try_into().unwrap(),
        };
        to.rtc.handle_input(Input::Receive(now, receive)).unwrap();
        to.poll(replies);
    }
}

/// Fires both peers' timers at `now` and exchanges datagrams until both go quiet,
/// then advances `now` to the next timer.
fn step(a: &mut Peer, b: &mut Peer, now: &mut Instant) {
    let (mut from_a, mut from_b) = (Vec::new(), Vec::new());
    a.rtc.handle_input(Input::Timeout(*now)).unwrap();
    a.poll(&mut from_a);
    b.rtc.handle_input(Input::Timeout(*now)).unwrap();
    b.poll(&mut from_b);
    while !from_a.is_empty() || !from_b.is_empty() {
        deliver(b, std::mem::take(&mut from_a), *now, &mut from_b);
        deliver(a, std::mem::take(&mut from_b), *now, &mut from_a);
    }
    *now = (*now + Duration::from_millis(1)).max(a.timeout.min(b.timeout));
}

/// Steps simulated time until `done`, failing after a simulated minute.
fn run(a: &mut Peer, b: &mut Peer, now: &mut Instant, done: impl Fn(&Peer, &Peer) -> bool) {
    let deadline = *now + Duration::from_secs(60);
    while !done(a, b) {
        assert!(*now < deadline, "timed out");
        step(a, b, now);
    }
}

fn connect(rind_active: bool, version: DtlsVersion) {
    let mut now = Instant::now();
    let mut a = Peer::new(rind_str0m::default_provider(), version, 1000, now);
    let mut b = Peer::new(str0m_aws_lc_rs::default_provider(), version, 2000, now);

    let ca = Candidate::host(a.addr, "udp").unwrap();
    let cb = Candidate::host(b.addr, "udp").unwrap();
    let (fa, fb) = (
        a.rtc.direct_api().local_dtls_fingerprint().clone(),
        b.rtc.direct_api().local_dtls_fingerprint().clone(),
    );
    let (ia, ib) = (
        a.rtc.direct_api().local_ice_credentials(),
        b.rtc.direct_api().local_ice_credentials(),
    );
    for (peer, local, remote, finger, creds, controlling) in [
        (&mut a, ca.clone(), cb.clone(), fb, ib, true),
        (&mut b, cb, ca, fa, ia, false),
    ] {
        peer.rtc.add_local_candidate(local);
        peer.rtc.add_remote_candidate(remote);
        let mut api = peer.rtc.direct_api();
        api.set_remote_fingerprint(finger);
        api.set_remote_ice_credentials(creds);
        api.set_ice_controlling(controlling);
        api.start_dtls(controlling == rind_active).unwrap();
    }

    run(&mut a, &mut b, &mut now, |a, b| a.connected && b.connected);

    // Each peer sends a stream the other expects.
    let mid: Mid = "a".into();
    for (peer, tx, rx) in [(&mut a, 1, 2), (&mut b, 2, 1)] {
        let mut api = peer.rtc.direct_api();
        api.declare_media(mid, MediaKind::Audio);
        api.declare_stream_tx(Ssrc::from(tx), None, mid, None);
        api.expect_stream_rx(Ssrc::from(rx), None, mid, None);
    }

    let payloads: Vec<Vec<u8>> = (0..20u8).map(|i| vec![i; 10 + 37 * i as usize]).collect();
    for (i, payload) in payloads.iter().enumerate() {
        for (peer, ssrc) in [(&mut a, 1), (&mut b, 2)] {
            let pt = peer
                .rtc
                .codec_config()
                .find(|p| p.spec().codec == Codec::Opus)
                .unwrap()
                .pt();
            let write = RtpWrite::new(pt, (i as u64).into(), 960 * i as u32, now, payload.clone());
            peer.rtc
                .direct_api()
                .stream_tx(&Ssrc::from(ssrc))
                .unwrap()
                .write_rtp(write);
        }
        step(&mut a, &mut b, &mut now);
    }

    run(&mut a, &mut b, &mut now, |a, b| {
        a.rtp.len() == payloads.len() && b.rtp.len() == payloads.len() && a.rtcp > 0 && b.rtcp > 0
    });
    assert_eq!(a.rtp, payloads);
    assert_eq!(b.rtp, payloads);
}

#[test]
fn dtls12_rind_client() {
    connect(true, DtlsVersion::Dtls12);
}

#[test]
fn dtls12_rind_server() {
    connect(false, DtlsVersion::Dtls12);
}

#[test]
fn dtls13_rind_client() {
    connect(true, DtlsVersion::Dtls13);
}

#[test]
fn dtls13_rind_server() {
    connect(false, DtlsVersion::Dtls13);
}

/// The generated certificate's fingerprint is its SHA-256, as browsers check.
#[test]
fn generated_certificate() {
    let provider = rind_str0m::default_provider();
    let cert = provider.dtls_provider.generate_certificate().unwrap();
    let again = provider.dtls_provider.generate_certificate().unwrap();
    assert_ne!(cert.certificate, again.certificate);

    let mut rtc = Rtc::builder()
        .set_crypto_provider(Arc::new(provider))
        .set_dtls_cert(cert.clone())
        .build(Instant::now());
    let fingerprint = rtc.direct_api().local_dtls_fingerprint().clone();
    assert_eq!(fingerprint.hash_func, "sha-256");
    assert_eq!(
        fingerprint.bytes,
        str0m_aws_lc_rs::default_provider()
            .sha256_provider
            .sha256(&cert.certificate)
    );
}

/// A caller's certificate or key that dimpl cannot use is an error, not a panic.
#[test]
fn unusable_certificate_is_an_error() {
    let provider = rind_str0m::default_provider();
    let dtls = provider.dtls_provider;
    let cert = dtls.generate_certificate().unwrap();

    let mut empty = cert.clone();
    empty.certificate.clear();
    let mut truncated = cert.clone();
    truncated.private_key.truncate(cert.private_key.len() / 2);
    let mut no_key = cert.clone();
    no_key.private_key.clear();

    for bad in [empty, truncated, no_key] {
        for version in [DtlsVersion::Dtls12, DtlsVersion::Dtls13, DtlsVersion::Auto] {
            assert!(dtls.new_dtls(&bad, Instant::now(), version, None).is_err());
        }
    }
    assert!(
        dtls.new_dtls(&cert, Instant::now(), DtlsVersion::Auto, None)
            .is_ok()
    );
}

/// A fresh connection reports dimpl's state through str0m's trait. This stays
/// out of the crate's unit tests: `admin/ctgrind` runs those under valgrind,
/// and building a dimpl config runs dimpl's own key-exchange self-test, which
/// compares the two throwaway shared secrets with `!=`.
#[test]
fn fresh_connection_reports_dimpl_state() {
    let dtls = rind_str0m::default_provider().dtls_provider;
    let cert = dtls.generate_certificate().unwrap();
    let mut dtls12 = dtls
        .new_dtls(&cert, Instant::now(), DtlsVersion::Dtls12, None)
        .unwrap();
    let rendered = format!("{dtls12:?}");
    assert!(rendered.contains("Dtls"), "{rendered}");
    assert!(!dtls12.is_active());
    assert_eq!(format!("{:?}", dtls12.protocol_version()), "Some(DTLS1_2)");
    let dtls13 = dtls
        .new_dtls(&cert, Instant::now(), DtlsVersion::Dtls13, None)
        .unwrap();
    assert_eq!(format!("{:?}", dtls13.protocol_version()), "Some(DTLS1_3)");
    assert!(!dtls12.is_closing());
    assert!(!dtls12.is_closed());
    dtls12.set_active(true);
    assert!(dtls12.is_active());
    assert_eq!(dtls12.send_application_data(&[0x11; 8]).unwrap(), 8);
    dtls12.close().unwrap();
    assert!(dtls12.is_closing() || dtls12.is_closed());
}
