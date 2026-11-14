# [XL] aarch64's eight-way AES-192-GCM kernels are proven

## Goal

aws-lc's `aesv8_gcm_8x_enc_192` and `aesv8_gcm_8x_dec_192`, which rind runs for AES-192-GCM on aarch64 cores with the SHA3 instructions (Apple, Graviton 3 and later, Neoverse N2 and V), are proven in HOL Light for the whole blocks rind hands them, in place, so AES-192-GCM earns the ✓ on those cores.

## Plan

Found by the 2026-11-09 audit: [kixel-ai/rind#460](https://github.com/kixel-ai/rind/pull/460) landed these kernels hours after the 2026-11-07 audit planned AES-192 as AES-CTR and GHASH in turn, so no quest covered them.

- Runs (`low/aarch64/aes_gcm.rs:310-316`, `:340-379`): `low/aarch64/aws_lc/aesv8_gcm_8x_{enc,dec}_192.*.s`, 1,393 and 1,383 lines from aws-lc's `aesv8-gcm-armv8-unroll8.pl`, eight blocks at a time on `eor3`, called past the short pass's lengths with a whole number of blocks, the same input and output pointer, the running GHASH, the counter block, 13 round keys, and the 12-entry H table. Cores without SHA3 run AES-CTR and GHASH in turn, which [AES-GCM on aarch64](/quest/m4/verified/aes-gcm-aarch64.md) proves.
- Already proven: nothing of these two. s2n-bignum has no AES-192 kernel and no PR for one (searched 2026-11-09). Its `aes{128,256}_gcm_{enc,dec}_alt` are whole-block forms of the same aws-lc eight-way code, proven against `common/gcm.ml`: at rind's pin `arm/proofs/aes128_gcm_enc_alt.ml` is 11,713 lines for a 1,939-line source, and `aes256_gcm_dec_alt.ml` 14,358. [awslabs/s2n-bignum#490](https://github.com/awslabs/s2n-bignum/pull/490), approved but unmerged on 2026-11-12, moves most of each into shared files (`aes_gcm_enc_alt_proof.ml`, `aes_gcm_dec_alt_common.ml`) and cuts `aes128_gcm_enc_alt.ml` to about 1,800 lines, with in-place use allowed.
- Route: HOL Light proofs of rind's two routines in `proofs/hol-light/`, built on those shared files once #490 is in the pin, for 12 rounds, with the precondition rind's call meets (a nonzero whole number of blocks, `in_p = out_p`). aws-lc's routines also take a partial last block, masked in their tail, where the s2n-bignum forms return at once for one; rind passes whole blocks, so the theorem is stated for those, and the tail's masking is the code that differs most from the proven forms. Then an axiom per routine in `proofs/Rind/Aarch64/`, and the two match arms join the Lean proof of `aes_gcm.rs`.
- Sized XL on the pinned proofs' length. If #490's shared proof takes a 12-round instance cheaply, this is far smaller: re-size it from the calibration in [kixel-ai/rind#552](https://github.com/kixel-ai/rind/pull/552) and from #490 as merged.
- Traffic is low: no TLS 1.3 or QUIC cipher suite uses AES-192, so this ranks behind every AES-128 and AES-256 proof.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [aarch64's AES-GCM kernels are proven in place](/quest/m4/verified/aes-gcm-aarch64-in-place.md) - the pin with s2n-bignum's shared eight-way proofs and in-place theorems
- [AES-GCM on aarch64 is proven](/quest/m4/verified/aes-gcm-aarch64.md) - the Lean proof of `aes_gcm.rs` these kernels' axioms slot into
