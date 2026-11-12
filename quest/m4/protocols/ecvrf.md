# [M] rind offers ECVRF

## Goal

A public `vrf` module implements RFC 9381's ECVRF-EDWARDS25519-SHA512-TAI and ECVRF-P256-SHA256-TAI: the holder of a secret key proves a pseudorandom output for an input, and anyone holding the public key verifies the proof and recovers the same output. These are the two suites key transparency uses: Meta's `akd` runs the Edwards suite, and draft-ietf-keytrans-protocol's ciphersuites name both.

## Plan

- Builds on the constant-time edwards25519 scalar multiplication in `rind/src/mid/edwards25519.rs` (`Point::mul`, on x86_64 and aarch64; armv7 and the portable backend multiply with curve25519-dalek's `EdwardsPoint`, as their Ed25519 does), since the prover multiplies the hashed input by its secret key; P-256 uses rind's existing arithmetic. Try-and-increment's running time depends on the input, never on the key; RFC 9381's security considerations note that this can leak a secret input, so the module's docs say so.
- The ELL2 and SSWU suites are left out: Cardano and Algorand use an incompatible pre-RFC draft, and no RFC 9381 consumer uses them.
- API: one `&'static Algorithm` per suite; a wiped `SecretKey` whose `prove(alpha)` returns the `Proof` and its `Output`, and a `PublicKey` whose `verify(alpha, &proof)` returns the `Output` or an error, so a caller cannot use an output it did not verify. Public keys are validated as RFC 9381 section 5.4.5 requires.
- Test against RFC 9381's Appendix B vectors, differentially against `akd_core`'s ECVRF for the Edwards suite and `vrf-rfc9381` for P-256 as dev-dependencies (aws-lc-rs has no VRF), and ctgrind on proving.
