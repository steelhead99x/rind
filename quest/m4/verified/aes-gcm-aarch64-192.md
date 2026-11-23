# [XL] aarch64's eight-way AES-192-GCM kernels are proven

## Goal

aws-lc's `aesv8_gcm_8x_enc_192` and `aesv8_gcm_8x_dec_192`, which rind runs for AES-192-GCM on aarch64 cores with the SHA3 instructions (Apple, Graviton 3 and later, Neoverse N2 and V), are proven in Lean on VG's aarch64 model, for the whole blocks rind hands them, in place, so AES-192-GCM earns the ✓ on those cores.

## Plan

Found by the 2026-11-09 audit: [kixel-ai/rind#460](https://github.com/kixel-ai/rind/pull/460) landed these kernels hours after the 2026-11-07 audit planned AES-192 as AES-CTR and GHASH in turn, so no quest covered them.

- Runs (`low/aarch64/aes_gcm.rs:305-312`, `:335-374`): `low/aarch64/aws_lc/aesv8_gcm_8x_{enc,dec}_192.*.s`, 1,393 and 1,383 lines from aws-lc's `aesv8-gcm-armv8-unroll8.pl`, eight blocks at a time on `eor3`, called past the short pass's lengths with a whole number of blocks, the same input and output pointer, the running GHASH, the counter block, 13 round keys, and the 12-entry H table. Cores without SHA3 run AES-CTR and GHASH in turn, which [AES-GCM on aarch64](/quest/m4/verified/aes-gcm-aarch64.md) proves.
- Already proven: nothing of these two. s2n-bignum has no AES-192 kernel and no PR for one (searched 2026-11-09). Its `aes{128,256}_gcm_{enc,dec}_alt` are whole-block forms of the same aws-lc eight-way code, proven against `common/gcm.ml`: since rind's pin moved to `3f01260f`, which has [awslabs/s2n-bignum#490](https://github.com/awslabs/s2n-bignum/pull/490), most of each proof is in shared files (`arm/proofs/utils/aes_gcm_enc_alt_proof.ml`, `aes_gcm_enc_alt_common.ml`, `aes_gcm_dec_alt_common.ml`), `aes128_gcm_enc_alt.ml` is 1,816 lines and `aes256_gcm_dec_alt.ml` 10,285, and every theorem allows in-place use.
- Route: Lean on VG's aarch64 model, which has AES, PMULL, and `eor3`, as [kixel-ai/rind#912](https://github.com/kixel-ai/rind/pull/912) proved aarch64 SHA-256, rind's extension in `proofs/verified-garbage/RindIsa/` adding what aws-lc's code uses beyond it, with a leakage contract, for 12 rounds, with the precondition rind's call meets (a nonzero whole number of blocks, `in_p = out_p`). aws-lc's routines also take a partial last block, masked in their tail; rind passes whole blocks, so the theorem is stated for those. s2n-bignum's HOL Light proofs of the 128- and 256-bit forms show the invariants, but a HOL Light proof built on their shared files would be rind's own, which [the m5 port](/quest/m5/verified/hol-light-to-lean.md) would then redo in Lean. Then an axiom per routine in `proofs/Rind/Aarch64/`, and the two match arms join the Lean proof of `aes_gcm.rs`.
- Sized XL: 2,776 lines of assembly, eight-way unrolled, against the trial's 124 instructions.
- Traffic is low: no TLS 1.3 or QUIC cipher suite uses AES-192, so this ranks behind every AES-128 and AES-256 proof.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [AES-GCM on aarch64 is proven](/quest/m4/verified/aes-gcm-aarch64.md) - the Lean proof of `aes_gcm.rs` these kernels' axioms slot into
