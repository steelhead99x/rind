# [XL] aws-lc's ChaCha20-Poly1305 seal and open are proven on x86_64

## Goal

`OnePass` in `proofs/Rind/X86_64/ChaCha20Poly1305.lean` is discharged, so ChaCha20-Poly1305 and XChaCha20-Poly1305 earn the ✓ on x86_64 CPUs with SSE4.1.

## Plan

- Prove both halves (AVX2 and SSE4.1) of aws-lc's `chacha20_poly1305_{seal,open}` and `poly_hash_ad_internal` on rind's object code in Lean, on VG's x86_64 model, directly against `Rind/Spec.lean`'s ChaCha20 and Poly1305, with their leakage contracts, as [kixel-ai/rind#912](https://github.com/kixel-ai/rind/pull/912) proved aarch64 SHA-256 (its body measures that route against HOL Light): model what VG's lacks in `proofs/verified-garbage/RindIsa/`, and list the programs in `RindIsa/Proven.lean`, so `admin/prove lean` checks their bytes and `admin/prove vg` cosimulates every instruction. The first x86_64 proof also extends `rind_isa` and `vg --rind` in `admin/prove`, aarch64-only today, to x86_64.
- Restate them in `Rind/X86_64/` as axioms about `one_pass` that give `OnePass`, record them in `Axioms.lean`, and add the `verified.toml` entries.
- Seal and open are 8,138 instructions; s2n-bignum's proofs of its aarch64 AES-GCM routines run 11,000 to 14,000 lines, a guide to the scale.
- pyca/verified-garbage (VG) measured slower on 2026-11-13 (ChaCha20-Poly1305 on x86_64 up to 1.14x rind's time with AVX-512 and 1.68x without AVX2), so rind keeps this code ([the m2 VG epic](/quest/m2/verified-garbage/README.md)).
