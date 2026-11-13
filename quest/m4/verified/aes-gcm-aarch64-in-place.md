# [M] aarch64's AES-GCM kernels are proven in place

## Goal

s2n-bignum's aarch64 AES-GCM kernels, which rind runs with the same input and output buffer, are proven for that use, so rind's in-place AES-GCM rests on a theorem instead of `admin/parse-asm/inplace.py`'s check of every length up to 64 blocks.

## Plan

- Runs: `aes{128,256}_gcm_{enc,dec}` by 4, and their `_alt` forms by 8 on cores with the SHA3 instructions, transliterated into `low/aarch64/aes{128,256}_gcm_{enc,dec}{,_alt}.rs`.
- Already proven: each kernel, CORRECT and SAFE, against SP 800-38D's GCM (`common/gcm.ml`), for whole blocks, by [awslabs/s2n-bignum#470](https://github.com/awslabs/s2n-bignum/pull/470), [#445](https://github.com/awslabs/s2n-bignum/pull/445), [#440](https://github.com/awslabs/s2n-bignum/pull/440), [#482](https://github.com/awslabs/s2n-bignum/pull/482), and [#485](https://github.com/awslabs/s2n-bignum/pull/485). At rind's pin (`b4f17ee`) every theorem requires `nonoverlapping` input and output.
- Upstream is doing this (found 2026-11-09, correcting the 2026-11-07 audit's "no upstream PR or issue addresses aliasing"): [awslabs/s2n-bignum#490](https://github.com/awslabs/s2n-bignum/pull/490), opened 2026-11-05 by `jargh`, who wrote most of s2n-bignum, and approved but unmerged on 2026-11-12, restates all eight theorems with `in_p = out_p \/ nonoverlapping (in_p, ...) (out_p, ...)` and documents in `include/s2n-bignum.h` that `out` "must either be in (in-place operation) or not overlap it".
- Route: wait for #490, then move `thirdparty/s2n-bignum` to a commit that has it and re-import. #490 also edits all eight kernels' assembly, so `admin/parse-asm/driver.aes_gcm.py` regenerates the eight files and the benchmarks rerun; [#491](https://github.com/awslabs/s2n-bignum/pull/491), closed on 2026-11-11 and folded into #490, reported a regression on large inputs in `aes128_gcm_enc_alt`, which rind runs. Point `low/aarch64/aes_gcm.rs`'s safety comment at the new theorems.
- Fallback, if #490 is closed or loses the aliasing: generalize each theorem to `in_p = out_p` in `proofs/hol-light/`, since each block is loaded before its output is stored. An out-of-place call is no route unless its copy measures free.
- #490 also rewrites `common/gcm.ml` and `common/fips197.ml`, the specs [VAES AES-GCM](/quest/m4/verified/aes-gcm-x86-vaes.md), [aarch64 without the crypto extension](/quest/m5/verified/aarch64-no-crypto.md), and [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md) prove against, so they build on the pin this quest lands.
- Upstream: offering work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Retire `inplace.py` once the theorems cover in-place use.

## Waiting

- awslabs/s2n-bignum: [#490](https://github.com/awslabs/s2n-bignum/pull/490) merges with its in-place theorems. Check with `gh pr view 490 --repo awslabs/s2n-bignum --json state,isDraft,mergedAt`; on 2026-11-12 it was open, approved, no longer a draft, and last pushed that day.
