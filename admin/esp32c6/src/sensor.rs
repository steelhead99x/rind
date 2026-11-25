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
use core::mem::{ManuallyDrop, size_of};
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
///
/// AGENTS.md: "A key type wipes its whole value on drop, public parts
/// included". So on drop this type first drops `aead` and `signing`, which wipe
/// their own values through rind's `Drop`, then overwrites every byte of itself
/// (the derived IV, a public security parameter, and any padding) with zeroes.
/// The two keys sit in `ManuallyDrop` so that `Drop::drop` runs them first,
/// once, and the zeroing comes after, with nothing left to run over it.
pub struct DeviceKeys {
    aead: ManuallyDrop<Key>,
    iv: [u8; 12],
    signing: ManuallyDrop<KeyPair>,
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
        let keys = Key::new(&CHACHA20_POLY1305, &aead)
            .and_then(|k| KeyPair::from_seed(&seed).map(|s| (k, s)))
            .map_err(|_| Error::Crypto);
        // The derived secrets were copied into the key types; wipe the stack
        // copies on every path, including the error one.
        wipe(&mut aead);
        wipe(&mut seed);
        let (aead, signing) = keys?;
        Ok(Self {
            aead: ManuallyDrop::new(aead),
            iv,
            signing: ManuallyDrop::new(signing),
        })
    }

    /// The Ed25519 public key a reader verifies with.
    pub fn public_key(&self) -> &[u8] {
        self.signing.public_key().as_ref()
    }
}

impl Drop for DeviceKeys {
    fn drop(&mut self) {
        // SAFETY: each field is dropped exactly once, here, and never used
        // again: the zeroing below is the last access to the whole value.
        unsafe {
            ManuallyDrop::drop(&mut self.aead);
            ManuallyDrop::drop(&mut self.signing);
        }
        // SAFETY: `self` is valid for writes of `size_of::<Self>()` bytes, and
        // all-zero bytes are written only as bytes: nothing reads the fields
        // as their types again, since the value is being dropped.
        let whole = unsafe {
            core::slice::from_raw_parts_mut((self as *mut Self).cast::<u8>(), size_of::<Self>())
        };
        wipe(whole);
    }
}

/// Overwrites `bytes` with zeroes in a way the compiler may not remove.
fn wipe(bytes: &mut [u8]) {
    for b in bytes.iter_mut() {
        // SAFETY: `b` is a valid, aligned, exclusive reference to one byte.
        unsafe { core::ptr::write_volatile(b, 0) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
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
    fn dropping_device_keys_wipes_the_whole_value() {
        let mut k = core::mem::ManuallyDrop::new(keys());
        let at = (&*k as *const DeviceKeys).cast::<u8>();
        let len = size_of::<DeviceKeys>();
        // Only initialised fields are read before the drop: the value's padding
        // and the AEAD key's unused storage are not, and reading them as bytes
        // would be undefined behaviour.
        assert_ne!(k.iv, [0; 12]);
        assert_ne!(k.public_key(), &[0; 32][..]);
        // SAFETY: dropped once; `k` is not used as a `DeviceKeys` afterward.
        unsafe { core::mem::ManuallyDrop::drop(&mut k) };
        // SAFETY: `ManuallyDrop` keeps the storage, and `Drop::drop` wrote
        // every byte of it, padding included, so all `len` bytes are
        // initialised now.
        let after = unsafe { core::slice::from_raw_parts(at, len) };
        assert!(after.iter().all(|&b| b == 0), "{after:02x?}");
    }

    fn unhex(s: &str) -> Vec<u8> {
        (0..s.len())
            .step_by(2)
            .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
            .collect()
    }

    // Produced outside rind and outside its backend: the HKDF-SHA256 keys,
    // the nonce, ChaCha20-Poly1305 and Ed25519 come from Python's
    // `cryptography` (OpenSSL 3.5). Secret [7; 32], sequence 1, the first
    // synthetic reading (channel 0, unit 1, 20.000, uptime 0).
    const VECTOR_PACKET: &str = "0100000000000000014e09ce87eaf8a6f915f7f5ca8120dad3c019e33fa97ef6cedf5410534550fceda8d148158679f86143b90e38c2e112aa6c59da07db3b3eaf4211efe6ce0fdaf2b7cfc990aa7052dadad56a4a4fa318609ee5f935cba002acb6bd8241cf06";
    const VECTOR_PUBLIC_KEY: &str =
        "233216634a8ecb8d4708c8e355e4a2c59df50e12b8c62c79e4f3dcb6f1bbd309";

    #[test]
    fn the_packet_and_public_key_match_an_independent_implementation() {
        let (p, r) = packet();
        assert_eq!(p, unhex(VECTOR_PACKET));
        assert_eq!(keys().public_key(), unhex(VECTOR_PUBLIC_KEY));
        assert_eq!(Opener::new(keys()).open(&unhex(VECTOR_PACKET)), Ok(r));
    }

    #[test]
    fn a_signed_packet_with_a_bad_tag_is_refused_as_a_bad_tag() {
        let (p, _) = packet();
        // Change a ciphertext byte, then sign the result properly, so the
        // signature check passes and only the AEAD tag can refuse it.
        let mut signed = p[..p.len() - SIG].to_vec();
        signed[HEADER] ^= 1;
        let sig = keys().signing.sign(&signed);
        signed.extend_from_slice(sig.as_ref());
        assert_eq!(Opener::new(keys()).open(&signed), Err(Error::BadTag));
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
