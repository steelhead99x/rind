# [M] ML-KEM's portable arithmetic is proven

## Goal

ML-KEM-768 earns the ✓ on x86_64 CPUs without AVX2: rind's Rust port of mlkem-native's portable C polynomial arithmetic, which runs there and on armv7, is proven against FIPS 203.

## Plan

- Runs: `low/generic/mlkem_poly.rs` and `low/generic/mlkem768.rs` (the NTT, inverse NTT, base multiplication, Barrett and Montgomery reductions, byte encoding, and rejection sampling), under the same construction, over s2n-bignum's proven single-state Keccak-f on x86_64. mlkem-native's CBMC proofs cover only memory safety and coefficient bounds of its C, not this port.
- Route: Aeneas to Lean against the same FIPS 203 spec as the construction, stating each function's contract as s2n-bignum's routines state theirs, so the construction's proof takes either.
- armv7 also needs its Keccak-f, OpenSSL's `keccak1600-armv4` assembly, which [the armv7 epic](/quest/m5/verified-armv7/README.md) covers.

## Required

- [ML-KEM-768's construction is proven](/quest/m4/verified/mlkem-construction.md) - the spec and contracts this meets
- [VG measured](/quest/m2/verified-garbage/bench.md) - whether pyca/verified-garbage's proven code beats what this would prove; if a switch replaces it, this quest is deleted or rewritten (maintainer, 2026-11-12)
