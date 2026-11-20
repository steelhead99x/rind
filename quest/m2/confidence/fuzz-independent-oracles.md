# [M] Fuzz targets compare three implementations

## Goal

Each `fuzz/fuzzer/` target for a primitive compares rind, aws-lc-rs, and an implementation that shares no code with the path rind runs, and fails on any disagreement. Where aws-lc-rs lacks the algorithm, as for the ECVRF, OPRF, and blind RSA targets that today compare rind only with itself, the target compares rind with that outside oracle alone, as `AGENTS.md`'s testing rule does.

## Plan

Decided with the maintainer on 2026-11-18 (/quest-plan): ✅ RustCrypto, with libcrux or dalek where RustCrypto shares code with the path (rejected: Botan, which brings a C++ build; leaving fuzzing out).

- This replaces what cryptofuzz gave aws-lc: guidovranken/cryptofuzz is gone, OSS-Fuzz disabled its project on 2026-08-20, and MozillaSecurity's fork has no Rust modules ([the OSS-Fuzz quest](/quest/m4/oss-fuzz.md) records that cryptofuzz is not planned again without a maintained upstream).
- Take the oracle choices from [the differential-test quest](/quest/m2/confidence/independent-oracles.md); a target can share its per-primitive comparison helpers if that is simpler. Work in either order.
- Where an oracle refuses inputs aws-lc-rs accepts, or the reverse, follow `AGENTS.md`: aws-lc-rs decides behavior, and the independent oracle checks only the values both accept.
- `vrf-rfc9381`, `akd_core`, `voprf`, and `blind-rsa-signatures` already serve as the differential tests' references for the three targets that compare rind with itself. On armv7 and the portable backend, `voprf` shares rind's code for every group, fiat-crypto's field arithmetic for the NIST suites and `curve25519-dalek` for ristretto255, so there the OPRF target checks the group operations against `num-bigint` references written from the RFCs: the differential-test quest's for the NIST groups, and one from RFC 9496 for ristretto255. `voprf` still checks the protocol steps above them, finalization and the proofs, whose code it does not share with rind.
- Rerun each target's corpus on every tier, as `sh/fuzz-replay.sh` does, and note in the PR any growth in run time.

## Related

- [Every differential test has an oracle that shares no code with rind](/quest/m2/confidence/independent-oracles.md) - picks the oracles
