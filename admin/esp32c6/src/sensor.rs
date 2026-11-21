// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Signing and sealing sensor readings with Ed25519 and ChaCha20-Poly1305.
//!
//! The sensor sits behind [`Sensor`], so the board's real sensor, which is not
//! identified yet, is one `impl` away. A [`Sealer`] turns each [`Reading`]
//! into a packet only the holder of the shared key reads, and only the holder
//! of the Ed25519 secret could have produced:
//!
//! ```text
//! version(1) | seq(8, big-endian) | ChaCha20-Poly1305(reading, aad = version | seq) | Ed25519 over all before it
//! ```
//!
//! The nonce is the sequence number XORed into a derived IV, so a sequence
//! number must never repeat under one key: a device keeps its next number in
//! non-volatile memory and starts above it after a reset, which this module
//! cannot do for it. [`Opener`] refuses a packet whose number is not above the
//! last it accepted, so a replay fails.

use alloc::vec::Vec;
use rind::aead::{CHACHA20_POLY1305, Key, Nonce};
use rind::ed25519::KeyPair;
use rind::hkdf::{HKDF_SHA256, Salt};

/// What a [`Sensor`] reads, in the unit's thousandths (milli-degrees, milli-percent).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reading {
    /// Which of the sensor's channels was read.
    pub channel: u8,
    /// An application-defined unit code, such as 1 for degrees Celsius.
    pub unit: u8,
    /// The value in thousandths of the unit.
    pub milli: i32,
    /// The device's uptime in milliseconds when it was read.
    pub uptime_ms: u64,
}

impl Reading {
    /// The encoded length.
    pub const LEN: usize = 14;

    fn encode(&self) -> [u8; Self::LEN] {
        let mut b = [0u8; Self::LEN];
        b[0] = self.channel;
        b[1] = self.unit;
        b[2..6].copy_from_slice(&self.milli.to_be_bytes());
        b[6..].copy_from_slice(&self.uptime_ms.to_be_bytes());
        b
    }

    fn decode(b: &[u8]) -> Option<Self> {
        let b: &[u8; Self::LEN] = b.try_into().ok()?;
        Some(Self {
            channel: b[0],
            unit: b[1],
            milli: i32::from_be_bytes(b[2..6].try_into().ok()?),
            uptime_ms: u64::from_be_bytes(b[6..].try_into().ok()?),
        })
    }
}

/// A source of readings. Implement it for the real sensor's driver.
pub trait Sensor {
    /// Why a read failed.
    type Error;
    /// Takes one reading.
    fn read(&mut self) -> Result<Reading, Self::Error>;
}

/// A fixed ramp standing in for a sensor, so a build without one still runs.
/// Its values are synthetic and say nothing about any hardware.
pub struct SyntheticSensor {
    next: i32,
    uptime_ms: u64,
}

impl SyntheticSensor {
    /// A ramp that starts at 20.000 and rises 0.125 a reading.
    pub fn new() -> Self {
        Self {
            next: 20_000,
            uptime_ms: 0,
        }
    }
}

impl Default for SyntheticSensor {
    fn default() -> Self {
        Self::new()
    }
}

impl Sensor for SyntheticSensor {
    type Error = core::convert::Infallible;
    fn read(&mut self) -> Result<Reading, Self::Error> {
        let r = Reading {
            channel: 0,
            unit: 1,
            milli: self.next,
            uptime_ms: self.uptime_ms,
        };
        self.next += 125;
        self.uptime_ms += 1000;
        Ok(r)
    }
}

/// Why sealing or opening failed.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    /// The packet is too short or has an unknown version.
    Malformed,
    /// The Ed25519 signature does not verify.
    BadSignature,
    /// The sequence number is not above the last accepted: a replay.
    Replay,
    /// The tag does not verify.
    BadTag,
    /// rind refused the operation.
    Crypto,
}

const VERSION: u8 = 1;
const HEADER: usize = 9;
const TAG: usize = 16;
const SIG: usize = 64;

/// The keys both ends derive from one 32-byte secret: HKDF-SHA256 with
/// distinct `info` for the AEAD key, the IV, and the Ed25519 seed.
pub struct DeviceKeys {
    aead: Key,
    iv: [u8; 12],
    signing: KeyPair,
}

impl DeviceKeys {
    /// Derives the keys from `secret`, which must be 32 secret random bytes.
    pub fn derive(secret: &[u8; 32]) -> Result<Self, Error> {
        let prk = Salt::new(&HKDF_SHA256, b"rind-esp32c6 sensor v1")
            .extract(secret)
            .map_err(|_| Error::Crypto)?;
        let mut aead = [0u8; 32];
        let mut iv = [0u8; 12];
        let mut seed = [0u8; 32];
        prk.fill(&[b"aead"], &mut aead).map_err(|_| Error::Crypto)?;
        prk.fill(&[b"iv"], &mut iv).map_err(|_| Error::Crypto)?;
        prk.fill(&[b"ed25519"], &mut seed)
            .map_err(|_| Error::Crypto)?;
        Ok(Self {
            aead: Key::new(&CHACHA20_POLY1305, &aead).map_err(|_| Error::Crypto)?,
            iv,
            signing: KeyPair::from_seed(&seed).map_err(|_| Error::Crypto)?,
        })
    }

    /// The Ed25519 public key a reader verifies with.
    pub fn public_key(&self) -> &[u8] {
        self.signing.public_key().as_ref()
    }
}

/// Seals readings in order, numbering them from `next_seq`.
pub struct Sealer {
    keys: DeviceKeys,
    next_seq: u64,
}

impl Sealer {
    /// A sealer whose first packet is `next_seq`, which must be above every
    /// number this key has used, including before the last reset.
    pub fn new(keys: DeviceKeys, next_seq: u64) -> Self {
        Self { keys, next_seq }
    }

    /// The number the next packet gets, to store before sending.
    pub fn next_seq(&self) -> u64 {
        self.next_seq
    }

    /// Signs and seals one reading.
    pub fn seal(&mut self, reading: &Reading) -> Result<Vec<u8>, Error> {
        let seq = self.next_seq;
        let next = seq.checked_add(1).ok_or(Error::Crypto)?;
        let mut out = Vec::with_capacity(HEADER + Reading::LEN + TAG + SIG);
        out.push(VERSION);
        out.extend_from_slice(&seq.to_be_bytes());
        let mut body = reading.encode();
        let tag = self
            .keys
            .aead
            .seal_in_place_separate_tag(
                Nonce::from_sequence(&self.keys.iv, seq),
                &out[..HEADER],
                &mut body,
            )
            .map_err(|_| Error::Crypto)?;
        self.next_seq = next;
        out.extend_from_slice(&body);
        out.extend_from_slice(tag.as_ref());
        let sig = self.keys.signing.sign(&out);
        out.extend_from_slice(sig.as_ref());
        Ok(out)
    }
}

/// Verifies and opens packets, refusing replays.
///
/// It holds the same [`DeviceKeys`] as the sealer, signing secret included: a
/// reader that must not be able to forge packets needs a design with the
/// public key only, which this example does not build.
pub struct Opener {
    keys: DeviceKeys,
    last: Option<u64>,
}

impl Opener {
    /// An opener for the packets `keys` seals.
    pub fn new(keys: DeviceKeys) -> Self {
        Self { keys, last: None }
    }

    /// Verifies the signature, then the sequence, then opens the reading.
    pub fn open(&mut self, packet: &[u8]) -> Result<Reading, Error> {
        if packet.len() != HEADER + Reading::LEN + TAG + SIG || packet[0] != VERSION {
            return Err(Error::Malformed);
        }
        let (signed, sig) = packet.split_at(packet.len() - SIG);
        self.keys
            .signing
            .public_key()
            .verify(signed, sig)
            .map_err(|_| Error::BadSignature)?;
        let seq = u64::from_be_bytes(packet[1..HEADER].try_into().map_err(|_| Error::Malformed)?);
        if self.last.is_some_and(|l| seq <= l) {
            return Err(Error::Replay);
        }
        let mut sealed = signed[HEADER..].to_vec();
        let plain = self
            .keys
            .aead
            .open_in_place(
                Nonce::from_sequence(&self.keys.iv, seq),
                &packet[..HEADER],
                &mut sealed,
            )
            .map_err(|_| Error::BadTag)?;
        let reading = Reading::decode(plain).ok_or(Error::Malformed)?;
        self.last = Some(seq);
        Ok(reading)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keys() -> DeviceKeys {
        DeviceKeys::derive(&[7; 32]).unwrap()
    }

    fn packet() -> (Vec<u8>, Reading) {
        let r = SyntheticSensor::new().read().unwrap();
        (Sealer::new(keys(), 1).seal(&r).unwrap(), r)
    }

    #[test]
    fn a_sealed_reading_opens_to_itself() {
        let (p, r) = packet();
        assert_eq!(p.len(), HEADER + Reading::LEN + TAG + SIG);
        assert_eq!(Opener::new(keys()).open(&p), Ok(r));
    }

    #[test]
    fn the_reading_is_not_in_the_clear() {
        let (p, r) = packet();
        assert!(!p.windows(Reading::LEN).any(|w| w == r.encode()));
    }

    #[test]
    fn any_changed_byte_fails() {
        let (p, _) = packet();
        for i in 0..p.len() {
            let mut q = p.clone();
            q[i] ^= 1;
            assert!(Opener::new(keys()).open(&q).is_err(), "byte {i}");
        }
    }

    #[test]
    fn a_replay_and_an_old_number_fail() {
        let mut s = Sealer::new(keys(), 5);
        let mut sensor = SyntheticSensor::new();
        let a = s.seal(&sensor.read().unwrap()).unwrap();
        let b = s.seal(&sensor.read().unwrap()).unwrap();
        let mut o = Opener::new(keys());
        assert!(o.open(&b).is_ok());
        assert_eq!(o.open(&b), Err(Error::Replay));
        assert_eq!(o.open(&a), Err(Error::Replay));
    }

    #[test]
    fn another_device_key_fails() {
        let (p, _) = packet();
        let other = DeviceKeys::derive(&[8; 32]).unwrap();
        assert_eq!(Opener::new(other).open(&p), Err(Error::BadSignature));
    }

    #[test]
    fn short_and_unknown_version_packets_are_malformed() {
        let (mut p, _) = packet();
        assert_eq!(Opener::new(keys()).open(&p[1..]), Err(Error::Malformed));
        p[0] = 2;
        assert_eq!(Opener::new(keys()).open(&p), Err(Error::Malformed));
    }

    #[test]
    fn the_counter_advances_and_never_repeats_a_nonce() {
        let mut s = Sealer::new(keys(), 0);
        let r = SyntheticSensor::new().read().unwrap();
        let a = s.seal(&r).unwrap();
        let b = s.seal(&r).unwrap();
        assert_eq!(s.next_seq(), 2);
        assert_ne!(
            a[HEADER..HEADER + Reading::LEN],
            b[HEADER..HEADER + Reading::LEN]
        );
    }

    #[test]
    fn the_last_number_is_refused_rather_than_wrapped() {
        let mut s = Sealer::new(keys(), u64::MAX);
        let r = SyntheticSensor::new().read().unwrap();
        assert_eq!(s.seal(&r), Err(Error::Crypto));
    }

    /// A sensor that fails, to show the trait carries the error.
    struct Broken;
    impl Sensor for Broken {
        type Error = &'static str;
        fn read(&mut self) -> Result<Reading, &'static str> {
            Err("no device")
        }
    }

    #[test]
    fn a_failing_sensor_surfaces_its_error() {
        assert_eq!(Broken.read(), Err("no device"));
    }

    #[test]
    fn a_reading_round_trips_its_encoding() {
        let r = Reading {
            channel: 3,
            unit: 2,
            milli: -40_500,
            uptime_ms: u64::MAX - 1,
        };
        assert_eq!(Reading::decode(&r.encode()), Some(r));
    }
}
