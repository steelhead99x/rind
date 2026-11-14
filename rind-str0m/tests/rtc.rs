//! A str0m session between a peer on rind and a peer on aws-lc-rs: STUN
//! MESSAGE-INTEGRITY, the DTLS handshake and fingerprint check, then SRTP and
//! SRTCP in both directions.

use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Arc;
use std::time::{Duration, Instant};

use str0m::crypto::CryptoProvider;
use str0m::crypto::dtls::{DtlsInstance, DtlsOutput, DtlsVersion};
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
    assert!(!dtls12.is_closing());
    assert!(dtls12.is_closed());
}

#[derive(Default)]
struct DtlsEvents {
    connected: bool,
    close_notify: bool,
    packets: usize,
    timeout: Option<Instant>,
}

fn transfer_dtls(from: &mut dyn DtlsInstance, to: &mut dyn DtlsInstance) -> DtlsEvents {
    let mut events = DtlsEvents::default();
    let mut buffer = [0u8; 2048];
    loop {
        match from.poll_output(&mut buffer) {
            DtlsOutput::Packet(packet) => {
                to.handle_packet(packet).unwrap();
                events.packets += 1;
            }
            DtlsOutput::Connected => events.connected = true,
            DtlsOutput::CloseNotify => events.close_notify = true,
            DtlsOutput::PeerCert(_) | DtlsOutput::KeyingMaterial(_, _) => {}
            DtlsOutput::Timeout(at) => {
                events.timeout = Some(at);
                return events;
            }
            other => panic!("unexpected DTLS output: {other:?}"),
        }
    }
}

/// Graceful close must be visible while close_notify still needs polling,
/// through the same provider trait str0m uses for an established connection.
#[test]
fn established_connection_reports_graceful_close() {
    for version in [DtlsVersion::Dtls12, DtlsVersion::Dtls13] {
        for rind_active in [false, true] {
            let mut now = Instant::now();
            let rind = rind_str0m::default_provider().dtls_provider;
            let aws = str0m_aws_lc_rs::default_provider().dtls_provider;
            let mut a = rind
                .new_dtls(&rind.generate_certificate().unwrap(), now, version, None)
                .unwrap();
            let mut b = aws
                .new_dtls(&aws.generate_certificate().unwrap(), now, version, None)
                .unwrap();
            a.set_active(rind_active);
            b.set_active(!rind_active);
            let mut connected = [false; 2];
            // dimpl's first flight retransmit is one second. Follow the Timeout
            // it returns, and fail once simulated time passes a minute.
            let deadline = now + Duration::from_secs(60);
            loop {
                assert!(
                    now < deadline,
                    "{version:?} handshake timed out, rind active={rind_active}"
                );
                a.handle_timeout(now).unwrap();
                b.handle_timeout(now).unwrap();
                let from_a = transfer_dtls(&mut *a, &mut *b);
                let from_b = transfer_dtls(&mut *b, &mut *a);
                connected[0] |= from_a.connected;
                connected[1] |= from_b.connected;
                if connected == [true; 2] {
                    break;
                }
                let next = from_a
                    .timeout
                    .into_iter()
                    .chain(from_b.timeout)
                    .min()
                    .unwrap_or_else(|| panic!("{version:?} handshake stalled without a timeout"));
                // A timeout that is not strictly later still advances, as `step` does,
                // so a stuck instant cannot spin.
                now = (now + Duration::from_millis(1)).max(next);
            }
            assert_eq!(
                connected, [true; 2],
                "{version:?}, rind active={rind_active}"
            );
            assert!(!a.is_closing());
            assert!(!a.is_closed());
            a.close().unwrap();
            assert!(a.is_closing(), "{version:?}, rind active={rind_active}");
            assert!(!a.is_closed());
            assert!(transfer_dtls(&mut *a, &mut *b).packets > 0);
            assert!(transfer_dtls(&mut *b, &mut *a).close_notify);
            b.close().unwrap();
            transfer_dtls(&mut *b, &mut *a);
            transfer_dtls(&mut *a, &mut *b);
            assert!(a.is_closed());
            assert!(!a.is_closing());
            assert!(b.is_closed());
        }
    }
}

/// The generated serial stays a positive INTEGER, and the certificate is valid
/// for exactly 365 days. `clear_serial_high_bit_forces_a_positive_integer`
/// checks the mask with a forced high bit. Branching on a serial from
/// `rind::rand` stays here, out of the crate's unit tests, because
/// `admin/ctgrind adapters` runs those under valgrind.
#[test]
fn certificate_serial_stays_positive_and_the_span_is_a_year() {
    let dtls = rind_str0m::default_provider().dtls_provider;
    let cert = dtls.generate_certificate().unwrap();
    let serial = serial_integer(&cert.certificate);
    assert!(serial.len() <= 20 && serial[0] & 0x80 == 0, "{serial:?}");
    let (before, after) = validity(&cert.certificate);
    assert_eq!(
        certificate_time(&after) - certificate_time(&before),
        time::Duration::days(365),
        "{before} .. {after}"
    );
}

fn serial_integer(cert: &[u8]) -> Vec<u8> {
    let body = sequence(cert);
    let tbs = sequence(body);
    let after_version = if tbs.first() == Some(&0xa0) {
        let (_, rest) = tlv(tbs);
        rest
    } else {
        tbs
    };
    let (serial, _) = tlv(after_version);
    assert_eq!(after_version[0], 0x02);
    serial.to_vec()
}

fn certificate_time(value: &str) -> time::OffsetDateTime {
    assert!(value.ends_with('Z'), "{value}");
    let digits = &value[..value.len() - 1];
    let (year, rest) = match digits.len() {
        12 => {
            let yy: i32 = digits[..2].parse().unwrap();
            (if yy >= 50 { 1900 + yy } else { 2000 + yy }, &digits[2..])
        }
        14 => (digits[..4].parse().unwrap(), &digits[4..]),
        _ => panic!("certificate time {value}"),
    };
    let part = |at: usize| -> u8 { rest[at..at + 2].parse().unwrap() };
    let date = time::Date::from_calendar_date(year, part(0).try_into().unwrap(), part(2)).unwrap();
    let clock = time::Time::from_hms(part(4), part(6), part(8)).unwrap();
    date.with_time(clock).assume_utc()
}

fn validity(cert: &[u8]) -> (String, String) {
    let body = sequence(cert);
    let tbs = sequence(body);
    let mut rest = tbs;
    // version, serial, signature, issuer, then validity.
    for _ in 0..4 {
        let (_, next) = tlv(rest);
        rest = next;
    }
    let (span, _) = tlv(rest);
    assert_eq!(rest[0], 0x30);
    let (before, after_bytes) = tlv(span);
    let (after, _) = tlv(after_bytes);
    (
        String::from_utf8(before.to_vec()).unwrap(),
        String::from_utf8(after.to_vec()).unwrap(),
    )
}

fn sequence(input: &[u8]) -> &[u8] {
    let (body, _) = tlv(input);
    assert_eq!(input[0], 0x30);
    body
}

fn tlv(input: &[u8]) -> (&[u8], &[u8]) {
    assert!(input.len() >= 2, "{input:?}");
    let (len, header) = match input[1] {
        len @ 0..=0x7f => (len as usize, 2),
        0x81 => (input[2] as usize, 3),
        0x82 => (u16::from_be_bytes([input[2], input[3]]) as usize, 4),
        other => panic!("DER length {other:#x}"),
    };
    let rest = &input[header..];
    (&rest[..len], &rest[len..])
}
