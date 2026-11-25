# [L] The portable SHA-2 block functions are proven in Lean

## Goal

The portable backend's SHA-256 and SHA-512 block functions, `low::generic::sha256::sha256_compress_blocks` and `low::generic::sha512::sha512_compress_blocks` (aws-lc's C `sha256_block_data_order_nohw` and 64-bit `sha512_block_data_order_nohw`, ported to Rust), are translated with the rest of the portable backend and proven against FIPS 180-4 in Lean, so `Sha256Blocks`'s `sha256` field in `proofs/Rind/Portable/ShaBlocks.lean` and `RunsSha512`'s contract in `proofs/Rind/Portable/Sha512Entry.lean` become theorems and the portable SHA-256, SHA-512, HMAC, and HKDF rows earn the ✓ again.

## Plan

[kixel-ai/rind#944](https://github.com/kixel-ai/rind/pull/944) replaced HACL*'s verified SHA-2, whose F* theorems the portable proof imported as axioms, with the port, which measured faster at every size, and took each block function's contract as a hypothesis, as SHA-1's already is.

Decided 2026-11-21 (maintainer, /quest-plan): ✅ keep the port and prove it here (rejected: revert to HACL*'s SHA-2 to keep the ✓; re-measure on stable runners first).

- Have `admin/prove`'s portable pass translate both modules (`--include crate::low::generic::sha256 --include crate::low::generic::sha512`) instead of leaving the two functions opaque, and drop their `opaque` declarations from `proofs/Rind/Portable/FunsExternal.lean`.
- Prove each against `Rind/HashSpec.lean`'s `sha256.compress` and `Rind/Sha2.lean`'s `processBlock`. Each body is sixteen rounds that read the block, then a loop of three (SHA-256) or four (SHA-512) passes of sixteen rounds over a sixteen-word window of the schedule, unrolled by the `sixteen!` macro with the working variables renamed rather than moved. Prove one round as a lemma, and the window's invariant as: after the pass starting at round `i`, slot `j` holds `W[i + j]`. Ch and Maj are the three-operation forms `((f ^ g) & e) ^ g` and `((a ^ b) & (b ^ c)) ^ b`, each a `bv_decide` lemma against FIPS 180-4's.
- Then turn the hypotheses into theorems: `Sha256Blocks` keeps only its entry checks, `RunsSha512` only its entry guard, and `HashAxioms.lean`'s and `Axioms.lean`'s pins stay at Lean's own axioms. Add the rind entry back to `benchmarks/verified.toml` for `sha256/*`, `sha512/*`, `hmac-sha256/*`, and `hkdf-sha256/*` on `portable`, and rerun `admin/bench-report render`.
- If Charon cannot translate a body (HACL*'s 64- and 80-round unrolled bodies hit its fixed `MAX_STACK_DEPTH` of 1024), measure a body without the macro's unrolling before reporting it upstream: the port unrolls only sixteen rounds at a time, so it should translate.

## Related

- [The rolled SHA-256 and SHA-512 loops on microcontrollers are proven in Lean](/quest/m4/verified/rolled-sha2-esp.md) - proves the bodies 32-bit microcontrollers run instead
- [Every hand model of untranslated Rust is retired](/quest/m4/verified/aeneas-fn-pointers.md) - retires the other places `proofs/` stands in for Rust the translation leaves out
