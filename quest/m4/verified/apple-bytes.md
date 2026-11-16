# [M] A proof's ✓ covers the macOS bytes too, or says it doesn't

## Goal

Every `benchmarks/verified.toml` row whose proof `admin/prove bytes` checks only against the Linux build either is checked against the Apple build too and passes, or carries `os = "linux"`, so no ✓ in README or BENCHMARKS.md covers macOS bytes that nothing checks.

## Plan

Found by [kixel-ai/rind#778](https://github.com/kixel-ai/rind/pull/778)'s iteration on 2026-11-16: aws-lc's Apple `.s` aligns its helpers to 32 bytes but not the function's entry, so with the entry 16 bytes off every helper call target differs from the Linux build's (P-256's first call targets entry+0x7b0, not +0x7a0). `admin/prove` builds and checks Linux targets only. #778 gave its P-256 rows `os = "linux"`. Rows already on main have the same gap: on x86_64, SHA-512, Ed25519 signing, and AES-GCM with AVX and MOVBE; on aarch64, SHA-256 and SHA-512, whose ✓ shows on the macOS bench host.

- First, make `admin/prove bytes` build each proven routine for the Apple target of its architecture (`x86_64-apple-darwin`, `aarch64-apple-darwin`) and compare it as it does the Linux build, listing which rows match.
- For a row that differs only by alignment, prefer aligning the Apple entry so the bytes match, where that changes no instruction the proof checks and does not slow the routine (benchmark it on the macOS host); otherwise give the row `os = "linux"`.
- ✅ m4, in the verified epic: it is about what the proofs claim, not a CI or main failure (maintainer, 2026-11-16; rejected: m0; skipping it).
