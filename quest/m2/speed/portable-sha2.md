# [M] The portable backend's SHA-256 and SHA-512 run the fastest permissive source

## Goal

The portable backend's SHA-256 and SHA-512 (and with them SHA-224, SHA-384, SHA-512/256, their HMACs, and HKDF) run the fastest permissively licensed portable source, measured on a 64-bit target at every size, closing the 1.11 to 1.22× gap to aws-lc's C that `benchmarks/gaps.toml`'s portable SHA-2 entry records.

## Plan

Decided 2026-11-18 (maintainer, [kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619#issuecomment-6994276361)): ✅ keep this quest (rejected: drop it). It subsumes the earlier SHA-256 measurement and SHA-512/256 per-call follow-ups.

- Today `low/portable/sha.rs` runs HACL*'s verified `Hacl_Hash_SHA2` through libcrux-sha2, which [run 43646114817](https://github.com/kixel-ai/rind/actions/runs/43646114817) measured at 1.11 to 1.17× aws-lc's C for SHA-256 and HMAC-SHA-256 and 1.15 to 1.22× for SHA-512, SHA-512/256, and HMAC-SHA-384 from 1200 B up.
- Candidates: aws-lc's C `sha256_block_data_order_nohw` and `sha512_block_data_order_nohw` ported to Rust, Graviola's portable SHA-2, `low::generic`'s own, and HACL*. Measure each on the portable tier of the weekly bench at every hash size; HACL* stays where it measures as fast at every size, per the source rule.
- Contributor draft [kixel-ai/rind#794](https://github.com/kixel-ai/rind/pull/794) drops libcrux-sha2 and rewrites the same `gaps.toml` entry and [the HACL* SHA-2 proof quest](/quest/m4/verified/hacl-sha2-lean.md): whichever lands second merges the other's changes.
- If HACL* is replaced, rewrite [the HACL* SHA-2 proof quest](/quest/m4/verified/hacl-sha2-lean.md) into the proof of what then runs, so the portable SHA-2 ✓ is planned again.
