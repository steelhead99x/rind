// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Constant-time check of the sensor example's secret path, run under valgrind
//! by `admin/ctgrind esp32c6`, as AGENTS.md requires of a new secret-handling
//! path.
//!
//! The 32-byte device secret and the reading are marked undefined (the reading
//! is confidential: the packet encrypts it), so memcheck flags any branch or
//! memory index that depends on either while the keys derive, a reading seals
//! and a packet opens. The packet is public by design (ciphertext, tag and
//! signature), as is the public key, so they are marked defined before the test
//! compares them. rind marks the keys it generates or parses itself.
//!
//! This host build checks the portable code the ESP32-C6 runs, as `admin/ctgrind`
//! forces `rind_portable` and 32-bit limbs for this suite, on the host's
//! instruction set, not riscv32imac itself, which valgrind does not support.
#![cfg(feature = "sensor")]

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use rind_esp32c6::sensor::{DeviceKeys, Error, Opener, Reading, Sealer};

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

fn reading() -> Reading {
    Reading {
        channel: 1,
        unit: 1,
        milli: 21_500,
        uptime_ms: 12_345,
    }
}

/// Derives the keys from a secret memcheck tracks, seals a reading, and opens
/// it with a second copy of the keys.
#[test]
fn the_secret_path_is_constant_time() {
    let seed = [0x5a; 32];
    // The expected packet, derived with the secret marked defined.
    let expected = Sealer::new(DeviceKeys::derive(&seed).unwrap(), 9)
        .seal(&reading())
        .unwrap();

    let secret_bytes = seed;
    secret(&secret_bytes);
    let sealing = DeviceKeys::derive(&secret_bytes).unwrap();
    public(sealing.public_key());
    let public_key = sealing.public_key().to_vec();
    let mut sealer = Sealer::new(sealing, 9);
    let confidential = reading();
    secret(&confidential);
    let packet = sealer.seal(&confidential).unwrap();
    public(&packet[..]);
    assert_eq!(packet, expected);
    assert_eq!(public_key, DeviceKeys::derive(&seed).unwrap().public_key());

    let mut opener = Opener::new(DeviceKeys::derive(&secret_bytes).unwrap());
    let opened = opener.open(&packet).unwrap();
    public(&opened);
    assert_eq!(opened, reading());

    // A replay and a changed byte take the refusal paths; which one they take
    // depends on public data and on the check's outcome, not on the keys.
    assert_eq!(opener.open(&packet), Err(Error::Replay));
    let mut bad = packet.clone();
    let last = bad.len() - 1;
    bad[last] ^= 1;
    assert!(
        Opener::new(DeviceKeys::derive(&secret_bytes).unwrap())
            .open(&bad)
            .is_err()
    );
    let mut bad = packet;
    bad[10] ^= 1;
    assert!(
        Opener::new(DeviceKeys::derive(&secret_bytes).unwrap())
            .open(&bad)
            .is_err()
    );
}
