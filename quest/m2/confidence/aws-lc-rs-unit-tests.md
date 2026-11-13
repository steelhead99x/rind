# [M] rind-aws-lc-rs runs aws-lc-rs's in-crate tests of its public API

## Goal

rind-aws-lc-rs also runs the tests aws-lc-rs 1.19.0 keeps beside its code, in `src/`, wherever they exercise its public API, under `rind-aws-lc-rs/tests/aws-lc-rs/` with the integration tests already there. Each test of something rind-aws-lc-rs does not offer is left out with a pointer to its README's "Not offered" list, and every other test passes or is a recorded divergence.

## Plan

- Why: with aws-lc-rs's `tests/` ported, 127 of rind-aws-lc-rs's 510 functions still never run (Linux/x86_64, 2026-11-12), most in `agreement.rs` (18), `error.rs` (19), `aead.rs` (20), and `aead/tls.rs` (7). aws-lc-rs tests those in `src/`: `agreement/agreement_tests.rs` (8 tests), `agreement/parsed_public_key_tests.rs` (16), `agreement/ephemeral.rs` (7), `signature/parsed_public_key_tests.rs` (27), `key_wrap/tests.rs` (12), `kem.rs` (10), `cipher.rs` (28), `aead/unbound_key.rs` (8), and smaller modules.
- These are unit tests, so they name `crate::` paths and sometimes private items, such as `agreement::AlgorithmID`. Port a test when it reaches only public items once its paths read `aws_lc_rs::`; leave out one that inspects private state, and list it in the vendored README.
- ML-KEM-512 and ML-KEM-1024 cases in `kem.rs` wait on [moq-dev/rind#606](https://github.com/moq-dev/rind/pull/606); leave them out with a pointer to the README's "Not offered" list until it lands.
- Triage failures as the integration tests' port did: a small divergence is fixed in the same PR, a larger one gets a quest and a "Behaves differently" line.

## Related

- [Every published function runs under a test](/quest/m2/confidence/uncovered-functions.md) - closes the rest of the adapters' gap after this
- [Adapter crates' surviving mutants](/quest/m2/confidence/mutants-adapters.md) - starts after this, as these tests kill many of rind-aws-lc-rs's mutants
