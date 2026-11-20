# [M] Every differential test has an oracle that shares no code with rind

## Goal

Each primitive's differential test in `rind/tests/crosschecks.rs` compares rind with an implementation that shares no code with the path rind runs on that tier, besides aws-lc-rs. `AGENTS.md`'s testing rule, reworded by this quest as the Plan says, requires it, and TESTING.md and AUDIT.md say which oracle checks each path.

## Plan

Decided with the maintainer on 2026-11-18 (/quest-plan): ✅ RustCrypto, with libcrux or dalek wherever RustCrypto shares code with the path (rejected: also Botan through its crate, which brings a C++ build for little independence beyond that pair; tests only, with no fuzzing, which [the fuzzing quest](/quest/m2/confidence/fuzz-independent-oracles.md) covers).

- Why: aws-lc-rs runs the same s2n-bignum, mlkem-native, and mldsa-native code rind runs on x86_64 and aarch64, for P-256, P-384, P-521, X25519, Ed25519, ML-KEM, ML-DSA, RSA, and SHA-3, as well as its own ChaCha20-Poly1305 and RSAZ, and verified-garbage's and Graviola's code shares upstream with it in places. There the differential test checks only rind's glue around the routine. AUDIT.md names only ChaCha20-Poly1305 and RSAZ.
- Candidate oracles, from the 2026-11-18 survey: `aes-gcm`, `chacha20poly1305`, `sha2`, `sha3`, `rsa` (with `num-bigint` for raw modular exponentiation), `p256`, `p384`, `p521`, `ml-kem`, `ml-dsa`, `x25519-dalek`, `ed25519-dalek`, and the libcrux crates (`libcrux-ml-kem`, `libcrux-ml-dsa`, `libcrux-p256`, `libcrux-curve25519`, `libcrux-ed25519`). Exclusions: not `openssl`, whose perlasm shares BoringSSL's lineage; not RustCrypto's NIST curves or aws-lc-rs's on armv7 and the portable backend, where rind and both of them run fiat-crypto's field arithmetic, so use `libcrux-p256` for P-256 there, and for P-384 and P-521, which no candidate crate covers without fiat-crypto, a schoolbook affine reference over `num-bigint` in the test itself, slow but sharing nothing; not dalek or the libcrux HACL\* crates on the tiers where rind runs that same code.
- Hash-to-curve follows the same rule: on armv7 and the portable backend, RustCrypto's NIST hash-to-curve runs fiat-crypto's field arithmetic too, so `mid::p521::hash_to_curve::crosscheck`, and any P-256 or P-384 one, uses the test's `num-bigint` reference running RFC 9380's simplified SWU map and its `expand_message_xmd`, both written from the RFC over the `sha2` crate's hashes, beside Appendix J's vectors.
- Start from ALGORITHMS.md's tables: for each primitive and tier, list the sources rind runs, and pick the oracle that shares none. Some dev-dependencies are already there for other reasons (`p256`, `p384`, `p521`, `curve25519-dalek`).
- Once each primitive has its oracle, reword `AGENTS.md`'s testing rule as the maintainer approved on 2026-11-18: "...differentially against aws-lc-rs (a dev-dependency only), and against a Rust implementation that shares no code with the path rind runs, such as RustCrypto's or libcrux's. Where aws-lc-rs lacks the algorithm, the latter alone...". Extend `admin/testing` so TESTING.md's primitives table names each one's independent oracle.
- A disagreement that turns out to be the oracle's bug goes in the PR body, and is reported upstream only with the maintainer's approval when it is outside the orgs `AGENTS.md` lists.

## Related

- [Fuzz targets compare three implementations](/quest/m2/confidence/fuzz-independent-oracles.md) - the same oracles, on fuzzed input
