// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! TLS 1.3's record sequence, which the FIPS module owns (IG C.H scenario 5).
//!
//! Not a supported API. A nonce's last 8 bytes are the static IV XOR the
//! sequence number. The first nonce fixes that mask and is sequence 0. A
//! later one is refused unless its sequence is strictly above the last and
//! is not `u64::MAX`, so the counter never wraps. A gap is allowed, as
//! aws-lc-rs's TLS record key allows one: only a repeat, a step backward,
//! or the last value is refused.

use crate::low::{Zeroable, zeroise_value};

/// The sequence counter a TLS 1.3 sealing key stores beside its AES key.
///
/// The mask is the static IV's last 8 bytes. That IV comes from the traffic
/// secret, so this whole value is wiped on drop under the `wipe` feature.
#[doc(hidden)]
pub struct Counter {
    mask: u64,
    min_next: u64,
    started: u8,
}

impl Counter {
    /// A counter that has not sealed, so the next nonce is sequence 0.
    pub fn new() -> Self {
        Self {
            mask: 0,
            min_next: 0,
            started: 0,
        }
    }

    /// Accepts `nonce` when its sequence is one this counter still allows,
    /// and records that sequence as used.
    ///
    /// The sequence number is the record counter. Refusal is the call's
    /// result, so the comparison is one unsigned compare; the mask stays in
    /// this value.
    pub fn accept(&mut self, nonce: &[u8; 12]) -> bool {
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(&nonce[4..]);
        let raw = u64::from_be_bytes(bytes);
        let seq = if self.started == 0 {
            0
        } else {
            raw ^ self.mask
        };
        if seq == u64::MAX || seq < self.min_next {
            return false;
        }
        if self.started == 0 {
            self.mask = raw;
            self.started = 1;
        }
        self.min_next = seq + 1;
        true
    }
}

impl Drop for Counter {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for Counter {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn nonce(mask: u64, seq: u64) -> [u8; 12] {
        let mut nonce = [0x11, 0x22, 0x33, 0x44, 0, 0, 0, 0, 0, 0, 0, 0];
        nonce[4..].copy_from_slice(&(mask ^ seq).to_be_bytes());
        nonce
    }

    #[test]
    fn sequence_moves_forward_and_refuses_a_repeat() {
        let mask = 0x0123_4567_89ab_cdef;
        let mut counter = Counter::new();
        assert!(counter.accept(&nonce(mask, 0)));
        assert!(counter.accept(&nonce(mask, 1)));
        assert!(!counter.accept(&nonce(mask, 1)));
        assert!(counter.accept(&nonce(mask, 3)));
        assert!(!counter.accept(&nonce(mask, 2)));
    }

    #[test]
    fn the_last_sequence_is_refused_and_does_not_wrap() {
        let mask = 0x0fed_cba9_8765_4321;
        let mut counter = Counter::new();
        counter.min_next = u64::MAX - 1;
        counter.mask = mask;
        counter.started = 1;
        assert!(counter.accept(&nonce(mask, u64::MAX - 1)));
        assert!(!counter.accept(&nonce(mask, u64::MAX)));
        assert!(!counter.accept(&nonce(mask, 0)));
        assert_eq!(counter.min_next, u64::MAX);
    }
}
