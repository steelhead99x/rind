# [XL] aws-lc's ChaCha20-Poly1305 seal and open are proven on x86_64

## Goal

`OnePass` in `proofs/Rind/X86_64/ChaCha20Poly1305.lean` is discharged, so ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Prove both halves (AVX2 and SSE4.1) of aws-lc's `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` on rind's object code in HOL Light, on s2n-bignum's model as rind's fork in `thirdparty/s2n-bignum` extends it, against the fork's `common/chacha20poly1305.ml`'s `chacha20_encrypt` and `chacha20_poly1305_tag`, which `Rind/S2nChaCha20Poly1305.lean` carries to `Rind/Spec.lean`; the proofs `needs` it, replacing its entry in `admin/prove`'s `hol_light_specs`.
- Restate them in `Rind/X86_64/` as axioms about `one_pass` that give `OnePass`, record them in `Axioms.lean`, and add the `verified.toml` entries.
- Seal and open are 8,138 instructions; s2n-bignum's proofs of its aarch64 AES-GCM routines run 11,000 to 14,000 lines, a guide to the scale.

## Required

- [VG measured](/quest/m2/verified-garbage/bench.md) - whether pyca/verified-garbage's proven code beats what this would prove; if a switch replaces it, this quest is deleted or rewritten (maintainer, 2026-11-12)
