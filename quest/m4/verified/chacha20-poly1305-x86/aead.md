# [XL] aws-lc's ChaCha20-Poly1305 seal and open are proven on x86_64

## Goal

`OnePass` in `proofs/Rind/X86_64/ChaCha20Poly1305.lean` is discharged, so ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Prove both halves (AVX2 and SSE4.1) of aws-lc's `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` on rind's object code in HOL Light, on s2n-bignum's model as `proofs/hol-light/s2n-bignum/x86.patch` extends it, against the [specs](/quest/m4/verified/chacha20-poly1305-x86/specs.md).
- Restate them in `Rind/X86_64/` as axioms about `one_pass` that give `OnePass`, record them in `Axioms.lean`, and add the `verified.toml` entries.
- Seal and open are 8,138 instructions; s2n-bignum's proofs of its aarch64 AES-GCM routines run 11,000 to 14,000 lines, a guide to the scale.

## Required

- [Specs](/quest/m4/verified/chacha20-poly1305-x86/specs.md) - the HOL Light ChaCha20, Poly1305, and AEAD specs the routines are proven against
