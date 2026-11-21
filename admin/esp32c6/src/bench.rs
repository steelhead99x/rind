// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Times rind's algorithms on whatever clock the caller has, and prints rows
//! in the form `admin/esp32c6-bench-ingest` reads:
//!
//! ```text
//! RIND-BENCH v1 <operation> median_ns=<n> min_ns=<n> max_ns=<n> rounds=<n> iters=<n>
//! ```
//!
//! `<operation>` is a bench-report operation ID with `{lib}` left in place
//! (`sha256/{lib}/1350B`), so a row names what it times. The clock is a trait
//! so the statistics are tested on the host with a fake one; on a board it is
//! the chip's timer.

use alloc::{format, string::String, vec, vec::Vec};

/// A monotonic clock.
pub trait Clock {
    /// Nanoseconds since any fixed point. Its tick may be coarser than 1 ns.
    fn now_ns(&mut self) -> u64;
}

/// One operation's result.
#[derive(Debug, PartialEq, Eq)]
pub struct Row {
    /// The bench-report operation ID.
    pub operation: &'static str,
    /// Median over rounds of the per-call time.
    pub median_ns: u64,
    /// Fastest round's per-call time.
    pub min_ns: u64,
    /// Slowest round's per-call time.
    pub max_ns: u64,
    /// How many rounds ran.
    pub rounds: u32,
    /// Calls per round.
    pub iters: u32,
}

impl Row {
    /// The row as the line `esp32c6-bench-ingest` parses.
    pub fn line(&self) -> String {
        format!(
            "RIND-BENCH v1 {} median_ns={} min_ns={} max_ns={} rounds={} iters={}",
            self.operation, self.median_ns, self.min_ns, self.max_ns, self.rounds, self.iters
        )
    }
}

/// Times `rounds` rounds of `iters` calls of `f`, after one untimed call.
/// `f` returns a value that is folded into a sink, so the call is not optimized away.
pub fn time<C: Clock>(
    clock: &mut C,
    operation: &'static str,
    rounds: u32,
    iters: u32,
    mut f: impl FnMut() -> u8,
) -> Row {
    assert!(rounds > 0 && iters > 0);
    let mut sink = f();
    let mut per_call: Vec<u64> = vec![];
    for _ in 0..rounds {
        let start = clock.now_ns();
        for _ in 0..iters {
            sink = sink.wrapping_add(f());
        }
        let end = clock.now_ns();
        per_call.push(end.saturating_sub(start) / u64::from(iters));
    }
    core::hint::black_box(sink);
    per_call.sort_unstable();
    Row {
        operation,
        median_ns: per_call[per_call.len() / 2],
        min_ns: per_call[0],
        max_ns: per_call[per_call.len() - 1],
        rounds,
        iters,
    }
}

/// The operations the enabled features include, timed. `scale` divides every
/// operation's iteration count (1 for the full count) so a slow board can
/// shorten a run without changing what it times.
#[allow(unused_variables, unused_mut)]
pub fn run_all<C: Clock>(clock: &mut C, rounds: u32, scale: u32, mut emit: impl FnMut(&Row)) {
    let scale = scale.max(1);
    let it = |n: u32| (n / scale).max(1);
    let buf = [0x5au8; 1350];
    let mut push = |r: Row| emit(&r);
    #[cfg(feature = "sha256")]
    push(time(clock, "sha256/{lib}/1350B", rounds, it(8), || {
        rind::digest::digest(&rind::digest::SHA256, &buf).as_ref()[0]
    }));
    #[cfg(feature = "sha512")]
    push(time(clock, "sha512/{lib}/1350B", rounds, it(8), || {
        rind::digest::digest(&rind::digest::SHA512, &buf).as_ref()[0]
    }));
    #[cfg(feature = "sha3-256")]
    push(time(clock, "sha3-256/{lib}/1350B", rounds, it(8), || {
        rind::digest::digest(&rind::digest::SHA3_256, &buf).as_ref()[0]
    }));
    #[cfg(feature = "hmac-sha256")]
    {
        let key = rind::hmac::Key::new(&rind::hmac::HMAC_SHA256, &[1; 32]);
        push(time(
            clock,
            "hmac-sha256/{lib}/1350B",
            rounds,
            it(8),
            || rind::hmac::sign(&key, &buf).as_ref()[0],
        ));
    }
    #[cfg(feature = "hkdf-sha256")]
    push(time(
        clock,
        "hkdf-sha256/extract-expand/{lib}",
        rounds,
        it(16),
        || {
            let mut out = [0u8; 32];
            let _ = rind::hkdf::Salt::new(&rind::hkdf::HKDF_SHA256, &[2; 16])
                .extract(&[3; 32])
                .and_then(|p| p.fill(&[b"info"], &mut out));
            out[0]
        },
    ));
    #[cfg(feature = "chacha20poly1305")]
    {
        let key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &[4; 32]).unwrap();
        push(time(
            clock,
            "chacha20poly1305/{lib}/1350B",
            rounds,
            it(8),
            || {
                let mut b = buf;
                let n = rind::aead::Nonce::assume_unique_for_key([0; 12]);
                key.seal_in_place_separate_tag(n, &[], &mut b)
                    .map_or(0, |t| t.as_ref()[0])
            },
        ));
    }
    #[cfg(feature = "aes128-gcm")]
    {
        let key = rind::aead::Key::new(&rind::aead::AES_128_GCM, &[5; 16]).unwrap();
        push(time(clock, "aes128-gcm/{lib}/1350B", rounds, it(8), || {
            let mut b = buf;
            let n = rind::aead::Nonce::assume_unique_for_key([0; 12]);
            key.seal_in_place_separate_tag(n, &[], &mut b)
                .map_or(0, |t| t.as_ref()[0])
        }));
    }
    #[cfg(feature = "x25519")]
    {
        use rind::agreement::{PrivateKey, X25519};
        let a = PrivateKey::from_scalar(&X25519, &[9; 32]).unwrap();
        let b = PrivateKey::from_scalar(&X25519, &[10; 32]).unwrap();
        let bp = b.public_key().as_ref().to_vec();
        push(time(clock, "x25519/{lib}", rounds, it(2), || {
            a.agree(&bp).map_or(0, |s| s.as_ref()[0])
        }));
    }
    #[cfg(feature = "ed25519")]
    {
        let kp = rind::ed25519::KeyPair::from_seed(&[11; 32]).unwrap();
        let sig = kp.sign(&buf[..64]);
        push(time(clock, "ed25519-sign/{lib}", rounds, it(2), || {
            kp.sign(&buf[..64]).as_ref()[0]
        }));
        push(time(clock, "ed25519-verify/{lib}", rounds, it(2), || {
            u8::from(kp.public_key().verify(&buf[..64], sig.as_ref()).is_ok())
        }));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A clock that advances a fixed step per call, so `time` is exact.
    struct Step(u64, u64);
    impl Clock for Step {
        fn now_ns(&mut self) -> u64 {
            self.0 += self.1;
            self.0
        }
    }

    #[test]
    fn the_median_is_the_middle_round_and_the_line_is_stable() {
        // Each round reads the clock twice, a step apart: 100 ns per round over 4 calls.
        let mut c = Step(0, 100);
        let row = time(&mut c, "sha256/{lib}/1350B", 5, 4, || 1);
        assert_eq!(row.median_ns, 25);
        assert_eq!(
            (row.min_ns, row.max_ns, row.rounds, row.iters),
            (25, 25, 5, 4)
        );
        assert_eq!(
            row.line(),
            "RIND-BENCH v1 sha256/{lib}/1350B median_ns=25 min_ns=25 max_ns=25 rounds=5 iters=4"
        );
    }

    #[test]
    fn a_clock_that_runs_backwards_gives_zero_not_a_wrap() {
        struct Back(u64);
        impl Clock for Back {
            fn now_ns(&mut self) -> u64 {
                self.0 = self.0.saturating_sub(10);
                self.0
            }
        }
        assert_eq!(time(&mut Back(1000), "x", 3, 2, || 0).max_ns, 0);
    }

    #[test]
    fn the_median_ignores_one_slow_round() {
        // Rounds of 10, 10, 1000 ns over one call each.
        struct Seq(Vec<u64>, usize);
        impl Clock for Seq {
            fn now_ns(&mut self) -> u64 {
                self.1 += 1;
                self.0[self.1 - 1]
            }
        }
        let mut c = Seq(vec![0, 10, 20, 1020, 2000, 2010], 0);
        // Rounds read (0,10), (20,1020), (2000,2010): 10, 1000, 10.
        let r = time(&mut c, "x", 3, 1, || 0);
        assert_eq!((r.median_ns, r.min_ns, r.max_ns), (10, 10, 1000));
    }

    #[cfg(feature = "all")]
    #[test]
    fn every_enabled_operation_emits_one_row() {
        let mut rows = vec![];
        run_all(&mut Step(0, 1000), 3, 4, |r| rows.push(r.operation));
        assert_eq!(rows.len(), 10);
        assert!(rows.iter().all(|o| o.contains("{lib}")));
    }
}
