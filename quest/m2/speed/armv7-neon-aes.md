# [M] armv7 without the crypto extension runs aws-lc's NEON AES and GHASH

## Goal

On armv7 with NEON but without the crypto extension, AES (CTR, CBC, single blocks, so AES-KW and QUIC header protection) and AES-GCM run aws-lc's NEON assembly, closing the 1.1 to 3.4× gap to aws-lc-rs that `benchmarks/gaps.toml`'s armv7 NEON AES entry records, and that entry goes.

## Plan

Decided 2026-11-18 (maintainer, [kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619#issuecomment-6994276361)): ✅ keep this quest (rejected: drop it), with its proof quest under the verified-armv7 epic.

- Today rind runs aws-lc's constant-time `aes_nohw` and integer GHASH, ported to Rust, there. aws-lc-rs runs `bsaes-armv7` (bitsliced, CTR and CBC decryption), `vpaes-armv7` (single blocks, key schedule, CBC encryption), and `ghash-armv4`'s NEON GHASH. Import those three as `low/arm/` assembly the way `aesv8_armx.rs` and `ghashv8_armx.rs` are, and dispatch on NEON without the crypto extension; armv7 without NEON keeps the `nohw` code.
- Measured in [run 43646114817](https://github.com/kixel-ai/rind/actions/runs/43646114817): AES-CTR 1.1 to 1.2×, CBC decryption 1.2 to 1.5×, CBC encryption, AES-KW, and header protection 2.0 to 2.2×, AES-GCM, HPKE AES-128-GCM, and rustls's AES bulk 1.4 to 3.4× aws-lc-rs's time. Re-measure on the armv7 NEON tier before and after; keep `nohw` for any size or mode where it still wins.
- `bsaes` keys need their own schedule conversion: keep one key type and convert at key setup, so a key works for every mode.
- Constant time: all three are constant time by construction (bitsliced or vector-permute, no tables indexed by secrets); add ctgrind coverage for each new path under qemu as the armv7 ctgrind job runs.
- Wycheproof and the aws-lc-rs differential tests cover AES and AES-GCM already; check they run on the NEON tier.
- Its proof is [armv7's NEON AES and GHASH are proven](/quest/m5/verified-armv7/neon-aes.md).

## Waiting

- Maintainer: close the armv7 NEON gap in `benchmarks/gaps.toml` once a weekly bench run of the armv7 NEON tier shows it closed, then delete that entry and this quest. `admin/bench-report render --check` refuses an entry that covers no gap, so it can go only with the refreshed data.
