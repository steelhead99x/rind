// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Times rind's algorithms on whatever clock the caller has, and prints rows
//! in the form `admin/esp32c6-bench-ingest` reads:
//!
//! ```text
//! RIND-BENCH v1 <operation> lib=<library> median_ns=<n> min_ns=<n> max_ns=<n> rounds=<n> iters=<n>
//! ```
//!
//! `<operation>` is a bench-report operation ID with `{lib}` left in place
//! (`sha256/{lib}/1350B`), so a row names what it times. The clock is a trait
//! so the statistics are tested on the host with a fake one; on a board it is
//! the chip's timer.

use alloc::{format, string::String, vec, vec::Vec};
use core::hint::black_box;
use core::num::NonZeroU32;

/// A monotonic clock.
pub trait Clock {
    /// Nanoseconds since any fixed point. Its tick may be coarser than 1 ns.
    fn now_ns(&mut self) -> u64;

    /// Heap bytes and stack bytes the board has free right now. The default,
    /// for a host or an emulator with no such limit, is unlimited.
    fn free(&mut self) -> (usize, usize) {
        (usize::MAX, usize::MAX)
    }
}

/// What the operations that need the most memory ask for, in bytes of heap and
/// stack: the peaks `admin/esp32c6-riscv32 size` measured, plus a quarter and
/// 4 KiB. Operations not listed are small and always run.
const NEEDS: &[(&str, usize, usize)] = &[
    ("mlkem768", 15_360 + 4096, 41_204 + 10_301 + 4096),
    ("mldsa65", 84_992 + 21_248 + 4096, 40_276 + 10_069 + 4096),
    ("p256", 4096, 17_228 + 4_307 + 4096),
];

/// Emits a size-failure row for each of `operations` and returns false when
/// the board has less heap or stack than `need` names, so the caller skips the
/// work instead of panicking on a failed allocation or overrunning the stack
/// (`admin/esp32c6-bench-ingest` refuses a panic and records this row).
fn fits<C: Clock>(
    clock: &mut C,
    need: &str,
    operations: &[&'static str],
    library: &'static str,
    emit: &mut impl FnMut(&Row),
) -> bool {
    let Some(&(_, heap, stack)) = NEEDS.iter().find(|n| n.0 == need) else {
        return true;
    };
    let (have_heap, have_stack) = clock.free();
    let (which, need, have) = if have_heap < heap {
        ("heap", heap, have_heap)
    } else if have_stack < stack {
        ("stack", stack, have_stack)
    } else {
        return true;
    };
    for &operation in operations {
        emit(&Row {
            operation,
            library,
            result: Result::SizeFailure { which, need, have },
        });
    }
    false
}

/// One operation's result.
#[derive(Debug, PartialEq, Eq)]
pub struct Row {
    /// The bench-report operation ID, with `{lib}` in the library's place.
    pub operation: &'static str,
    /// The library that ran it: `rind`, or the vendor.
    pub library: &'static str,
    /// The timing, or why there is none.
    pub result: Result,
}

/// A row's outcome.
#[derive(Debug, PartialEq, Eq)]
pub enum Result {
    /// The operation ran.
    Timed {
        /// Median over rounds of the per-call time.
        median_ns: u64,
        /// Fastest round's per-call time.
        min_ns: u64,
        /// Slowest round's per-call time.
        max_ns: u64,
        /// How many rounds ran.
        rounds: u32,
        /// Calls per round.
        iters: u32,
    },
    /// The board had less `which` (`heap` or `stack`) than the operation needs,
    /// so it did not run.
    SizeFailure {
        /// `heap` or `stack`.
        which: &'static str,
        /// Bytes the operation is expected to need.
        need: usize,
        /// Bytes the board had free.
        have: usize,
    },
}

impl Row {
    /// The row as the line `esp32c6-bench-ingest` parses.
    pub fn line(&self) -> String {
        match &self.result {
            Result::Timed { median_ns, min_ns, max_ns, rounds, iters } => format!(
                "RIND-BENCH v1 {} lib={} median_ns={median_ns} min_ns={min_ns} max_ns={max_ns} rounds={rounds} iters={iters}",
                self.operation, self.library
            ),
            Result::SizeFailure { which, need, have } => format!(
                "RIND-BENCH v1 {} lib={} size_failure={which} need={need} have={have}",
                self.operation, self.library
            ),
        }
    }
}

/// Times `rounds` rounds of `iters` calls of `f`, after two untimed calls:
/// rind builds a key's reusable state, such as a verifying key's expanded
/// matrix, on its second use, which would otherwise land in the first round.
/// Zero counts are unrepresentable: the parameters are non-zero.
///
/// `f` returns a value, and each call's value goes through `black_box` before
/// it is folded into the sink, so the compiler cannot hoist the call out of the
/// loop or collapse repeated calls. `f` must also pass its inputs through
/// `black_box` (the rows in `run_all` do), so the inputs are not known to be
/// the same on every call.
pub fn time<C: Clock>(
    clock: &mut C,
    operation: &'static str,
    library: &'static str,
    rounds: NonZeroU32,
    iters: NonZeroU32,
    mut f: impl FnMut() -> u8,
) -> Row {
    let (rounds, iters) = (rounds.get(), iters.get());
    let mut sink = black_box(f()).wrapping_add(black_box(f()));
    let mut per_call: Vec<u64> = vec![];
    for _ in 0..rounds {
        let start = clock.now_ns();
        for _ in 0..iters {
            sink = sink.wrapping_add(black_box(f()));
        }
        let end = clock.now_ns();
        per_call.push(end.saturating_sub(start) / u64::from(iters));
    }
    black_box(sink);
    per_call.sort_unstable();
    Row {
        operation,
        library,
        result: Result::Timed {
            median_ns: per_call[per_call.len() / 2],
            min_ns: per_call[0],
            max_ns: per_call[per_call.len() - 1],
            rounds,
            iters,
        },
    }
}

/// The operations the enabled features include, timed. `scale` divides every
/// operation's iteration count (1 for the full count) so a slow board can
/// shorten a run without changing what it times.
#[allow(unused_variables, unused_mut)]
pub fn run_all<C: Clock>(
    clock: &mut C,
    rounds: NonZeroU32,
    scale: u32,
    mut emit: impl FnMut(&Row),
) {
    let scale = scale.max(1);
    let it = |n: u32| NonZeroU32::new(n / scale).unwrap_or(NonZeroU32::MIN);
    let buf = [0x5au8; 1350];
    // The 32 B associated data rind-bench's AEAD rows use for the 1350 B size
    // (`criterion::aead_rows`): all zeroes.
    #[allow(dead_code)]
    const AAD: [u8; 32] = [0; 32];
    macro_rules! push {
        ($r:expr) => {{
            let r = $r;
            emit(&r)
        }};
    }
    #[cfg(feature = "sha256")]
    push!(time(
        clock,
        "sha256/{lib}/1350B",
        "rind",
        rounds,
        it(8),
        || rind::digest::digest(&rind::digest::SHA256, black_box(&buf)).as_ref()[0],
    ));
    #[cfg(feature = "sha512")]
    push!(time(
        clock,
        "sha512/{lib}/1350B",
        "rind",
        rounds,
        it(8),
        || rind::digest::digest(&rind::digest::SHA512, black_box(&buf)).as_ref()[0],
    ));
    #[cfg(feature = "sha3-256")]
    push!(time(
        clock,
        "sha3-256/{lib}/1350B",
        "rind",
        rounds,
        it(8),
        || rind::digest::digest(&rind::digest::SHA3_256, black_box(&buf)).as_ref()[0],
    ));
    // The canonical row keys HMAC per message, as rind-bench/benches/hmac.rs
    // does (its `reused-key` rows are separate), so the key is built inside.
    #[cfg(feature = "hmac-sha256")]
    push!(time(
        clock,
        "hmac-sha256/{lib}/1350B",
        "rind",
        rounds,
        it(8),
        || {
            let key = rind::hmac::Key::new(&rind::hmac::HMAC_SHA256, black_box(&[1; 32]));
            rind::hmac::sign(&key, black_box(&buf)).as_ref()[0]
        },
    ));
    #[cfg(feature = "hkdf-sha256")]
    push!(time(
        clock,
        "hkdf-sha256/extract-expand/{lib}",
        "rind",
        rounds,
        it(16),
        || {
            let mut out = [0u8; 32];
            let _ = rind::hkdf::Salt::new(&rind::hkdf::HKDF_SHA256, black_box(&[2; 16]))
                .extract(black_box(&[3; 32]))
                .and_then(|p| p.fill(&[b"info"], &mut out));
            black_box(out)[0]
        },
    ));
    #[cfg(feature = "chacha20poly1305")]
    {
        let key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &[4; 32]).unwrap();
        push!(time(
            clock,
            "chacha20poly1305/{lib}/1350B",
            "rind",
            rounds,
            it(8),
            || {
                let mut b = *black_box(&buf);
                let n = rind::aead::Nonce::assume_unique_for_key([0; 12]);
                key.seal_in_place_separate_tag(n, black_box(&AAD), black_box(&mut b[..]))
                    .map_or(0, |t| t.as_ref()[0])
            },
        ));
    }
    #[cfg(feature = "aes128-gcm")]
    {
        let key = rind::aead::Key::new(&rind::aead::AES_128_GCM, &[5; 16]).unwrap();
        push!(time(
            clock,
            "aes128-gcm/{lib}/1350B",
            "rind",
            rounds,
            it(8),
            || {
                let mut b = *black_box(&buf);
                let n = rind::aead::Nonce::assume_unique_for_key([0; 12]);
                key.seal_in_place_separate_tag(n, black_box(&AAD), black_box(&mut b[..]))
                    .map_or(0, |t| t.as_ref()[0])
            },
        ));
    }
    #[cfg(feature = "sha1")]
    push!(time(
        clock,
        "sha1/{lib}/1350B",
        "rind",
        rounds,
        it(8),
        || rind::digest::digest(&rind::digest::legacy::SHA1, black_box(&buf)).as_ref()[0],
    ));
    #[cfg(feature = "md5")]
    push!(time(
        clock,
        "md5/{lib}/1350B",
        "rind",
        rounds,
        it(8),
        || rind::digest::digest(&rind::digest::legacy::MD5, black_box(&buf)).as_ref()[0],
    ));
    #[cfg(feature = "aes256-gcm")]
    {
        let key = rind::aead::Key::new(&rind::aead::AES_256_GCM, &[6; 32]).unwrap();
        push!(time(
            clock,
            "aes256-gcm/{lib}/1350B",
            "rind",
            rounds,
            it(8),
            || {
                let mut b = *black_box(&buf);
                let n = rind::aead::Nonce::assume_unique_for_key([0; 12]);
                key.seal_in_place_separate_tag(n, black_box(&AAD), black_box(&mut b[..]))
                    .map_or(0, |t| t.as_ref()[0])
            },
        ));
    }
    #[cfg(feature = "pbkdf2-sha256")]
    {
        let secret = rind::pbkdf2::Secret::new(&rind::pbkdf2::PBKDF2_HMAC_SHA256, b"password");
        let n = core::num::NonZeroU32::new(1000).unwrap();
        push!(time(
            clock,
            "pbkdf2-hmac-sha256-1000/{lib}",
            "rind",
            rounds,
            it(1),
            || {
                let mut out = [0u8; 32];
                let _ = black_box(&secret).derive(n, black_box(b"salt"), &mut out);
                black_box(out)[0]
            },
        ));
    }
    // Keys are generated once outside the timed closure, so this is the stored-key
    // workload of `p256-ecdh-stored`, not the `p256-ecdh` benchmark that times key generation.
    #[cfg(feature = "p256-ecdh")]
    if fits(clock, "p256", &["p256-ecdh-stored/{lib}"], "rind", &mut emit) {
        use rind::agreement::{ECDH_P256, PrivateKey};
        let a = PrivateKey::generate(&ECDH_P256).unwrap();
        let b = PrivateKey::generate(&ECDH_P256).unwrap();
        let bp = b.public_key().as_ref().to_vec();
        push!(time(
            clock,
            "p256-ecdh-stored/{lib}",
            "rind",
            rounds,
            it(1),
            || black_box(&a).agree(black_box(&bp)).map_or(0, |s| s.as_ref()[0]),
        ));
    }
    #[cfg(feature = "p256-ecdsa")]
    if fits(clock, "p256", &["p256-ecdsa-sign/{lib}", "p256-ecdsa-verify-parsed/{lib}"], "rind", &mut emit) {
        use rind::ecdsa::{KeyPair, PublicKey, sign, verify};
        let kp = KeyPair::generate(&sign::P256_SHA256_FIXED).unwrap();
        let sig = kp.sign(&buf[..64]).unwrap();
        let pk = PublicKey::new(&verify::P256_SHA256_FIXED, kp.public_key().as_ref()).unwrap();
        push!(time(
            clock,
            "p256-ecdsa-sign/{lib}",
            "rind",
            rounds,
            it(1),
            || black_box(&kp).sign(black_box(&buf[..64])).map_or(0, |s| s.as_ref()[0]),
        ));
        push!(time(
            clock,
            "p256-ecdsa-verify-parsed/{lib}",
            "rind",
            rounds,
            it(1),
            || u8::from(black_box(&pk).verify(black_box(&buf[..64]), black_box(sig.as_ref())).is_ok()),
        ));
    }
    #[cfg(feature = "mlkem768")]
    if fits(clock, "mlkem768", &["mlkem768-encaps/{lib}", "mlkem768-decaps/{lib}"], "rind", &mut emit) {
        use rind::kem::{DecapsulationKey, EncapsulationKey, MlKem768};
        let dk = DecapsulationKey::<MlKem768>::generate().unwrap();
        let ek = dk.public_key();
        let (ct, _) = ek.encapsulate().unwrap();
        // As rind-bench's `mlkem768-encaps`: the encoded key is parsed inside the timed closure.
        let ek_bytes = ek.as_ref().to_vec();
        push!(time(
            clock,
            "mlkem768-encaps/{lib}",
            "rind",
            rounds,
            it(1),
            || {
                EncapsulationKey::<MlKem768>::new(black_box(&ek_bytes))
                    .ok()
                    .and_then(|k| k.encapsulate().ok())
                    .map_or(0, |(_, s)| s.as_ref()[0])
            },
        ));
        push!(time(
            clock,
            "mlkem768-decaps/{lib}",
            "rind",
            rounds,
            it(1),
            || black_box(&dk).decapsulate(black_box(&ct)).as_ref()[0],
        ));
    }
    #[cfg(feature = "mldsa65")]
    if fits(clock, "mldsa65", &["mldsa65-sign/{lib}", "mldsa65-verify/{lib}"], "rind", &mut emit) {
        use rind::ml_dsa::{KeyPair, MlDsa65, PublicKey};
        let kp = KeyPair::<MlDsa65>::generate().unwrap();
        let sig = kp.sign(&buf[..64]).unwrap();
        let pk = PublicKey::<MlDsa65>::new(kp.public_key().as_ref()).unwrap();
        // Signing draws fresh randomness, so each call runs a random number
        // of rejection-sampling attempts (about 5 on average for ML-DSA-65,
        // one about a fifth of the time): one call a round makes the median
        // a draw from a spread of ten times or more. 16 calls a round time
        // the mean instead.
        push!(time(
            clock,
            "mldsa65-sign/{lib}",
            "rind",
            rounds,
            it(16),
            || black_box(&kp).sign(black_box(&buf[..64])).map_or(0, |s| s.as_ref()[0]),
        ));
        push!(time(
            clock,
            "mldsa65-verify/{lib}",
            "rind",
            rounds,
            it(1),
            || u8::from(black_box(&pk).verify(black_box(&buf[..64]), black_box(sig.as_ref())).is_ok()),
        ));
    }
    #[cfg(feature = "x25519")]
    {
        use rind::agreement::{PrivateKey, X25519};
        let a = PrivateKey::from_scalar(&X25519, &[9; 32]).unwrap();
        let b = PrivateKey::from_scalar(&X25519, &[10; 32]).unwrap();
        let bp = b.public_key().as_ref().to_vec();
        push!(time(clock, "x25519-ecdh-stored/{lib}", "rind", rounds, it(2), || {
            black_box(&a).agree(black_box(&bp)).map_or(0, |s| s.as_ref()[0])
        }));
    }
    #[cfg(feature = "ed25519")]
    {
        let kp = rind::ed25519::KeyPair::from_seed(&[11; 32]).unwrap();
        // The messages rind-bench/benches/ed25519.rs uses, so these rows measure
        // the canonical workload: verification hashes R | A | message, which is
        // one SHA-512 block for four bytes and two for 64.
        let sign_msg = b"123400";
        let verify_msg = b"Test";
        let sig = kp.sign(verify_msg);
        push!(time(
            clock,
            "ed25519-sign/{lib}",
            "rind",
            rounds,
            it(2),
            || black_box(&kp).sign(black_box(sign_msg)).as_ref()[0],
        ));
        push!(time(
            clock,
            "ed25519-verify/{lib}",
            "rind",
            rounds,
            it(2),
            || {
                u8::from(
                    kp.public_key()
                        .verify(black_box(verify_msg), black_box(sig.as_ref()))
                        .is_ok(),
                )
            },
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nz(n: u32) -> NonZeroU32 {
        NonZeroU32::new(n).unwrap()
    }

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
        let row = time(&mut c, "sha256/{lib}/1350B", "rind", nz(5), nz(4), || 1);
        assert_eq!(
            row.result,
            Result::Timed { median_ns: 25, min_ns: 25, max_ns: 25, rounds: 5, iters: 4 }
        );
        assert_eq!(
            row.line(),
            "RIND-BENCH v1 sha256/{lib}/1350B lib=rind median_ns=25 min_ns=25 max_ns=25 rounds=5 iters=4"
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
        let Result::Timed { max_ns, .. } = time(&mut Back(1000), "x", "rind", nz(3), nz(2), || 0).result
        else {
            panic!("not timed")
        };
        assert_eq!(max_ns, 0);
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
        let r = time(&mut c, "x", "rind", nz(3), nz(1), || 0);
        let Result::Timed { median_ns, min_ns, max_ns, .. } = r.result else {
            panic!("not timed")
        };
        assert_eq!((median_ns, min_ns, max_ns), (10, 10, 1000));
    }

    #[cfg(feature = "all")]
    #[test]
    fn every_enabled_operation_emits_one_row() {
        let mut rows = vec![];
        run_all(&mut Step(0, 1000), nz(3), 4, |r| rows.push(r.operation));
        assert_eq!(rows.len(), 21);
        assert!(rows.iter().all(|o| o.contains("{lib}")));
    }

    /// A board with too little heap or stack gets a size-failure row, not a panic.
    #[cfg(feature = "all")]
    #[test]
    fn a_board_too_small_for_an_operation_records_a_size_failure() {
        struct Small(usize, usize);
        impl Clock for Small {
            fn now_ns(&mut self) -> u64 {
                0
            }
            fn free(&mut self) -> (usize, usize) {
                (self.0, self.1)
            }
        }
        let mut lines = vec![];
        run_all(&mut Small(50_000, usize::MAX), nz(1), 64, |r| lines.push(r.line()));
        assert_eq!(lines.len(), 21);
        let failed: Vec<_> = lines.iter().filter(|l| l.contains("size_failure=")).collect();
        assert_eq!(failed.len(), 2, "{failed:?}");
        assert!(failed[0].starts_with("RIND-BENCH v1 mldsa65-sign/{lib} lib=rind size_failure=heap need=110336 have=50000"));
        lines.clear();
        run_all(&mut Small(usize::MAX, 30_000), nz(1), 64, |r| lines.push(r.line()));
        let n = lines.iter().filter(|l| l.contains("size_failure=stack")).count();
        // 30 000 B of stack fits P-256 (about 26 KB) but not ML-KEM or ML-DSA.
        assert_eq!(n, 4);
    }
}
