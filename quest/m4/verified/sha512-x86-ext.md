# [L] x86_64 SHA-512 runs the SHA512 instructions once Intel lists them, proven

## Goal

On x86_64 CPUs with the SHA512 instructions (Arrow Lake, Lunar Lake, Panther Lake, Clearwater Forest, and Diamond Rapids), SHA-384, SHA-512, SHA-512/256, and so HMAC, HKDF, and Ed25519 signing over them, run OpenSSL's routine for those instructions with a proof, once Intel's "Data Operand Independent Timing Instructions" list holds `VSHA512RNDS2`, `VSHA512MSG1`, and `VSHA512MSG2`. Ed25519 verification there also needs [its half-size check proven](/quest/m4/verified/ed25519-half-scalar.md).

## Plan

- Gain: OpenSSL's `sha512_block_data_order_sha512ext` measured 5.4x faster than aws-lc's AVX routine on Arrow Lake, so about 4.7x the AVX2 routine rind runs there in its place. [kixel-ai/rind#821](https://github.com/kixel-ai/rind/pull/821) dropped it, its `HaveSha512` dispatch, and `RIND_TEST_X86_SHA512`, since Intel's list omits the instructions; git history keeps them.
- Then: restore those, take `vsha512\w*` out of `admin/ct-vartime`'s x86 `VARTIME`, and have the Arrow Lake and Diamond Rapids rows of `x86-cpu.yml` and `ct_sde_hmac` (HMAC-SHA384 and HMAC-SHA512 under SDE, as valgrind cannot run the instructions) run the routine.
- Already proven: nothing. s2n-bignum's x86_64 model lacks `vsha512rnds2`, `vsha512msg1`, and `vsha512msg2`.
- Route: add the three instructions to s2n-bignum's x86_64 model from Intel's manual, then a HOL Light proof of the routine against [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s FIPS 180-4 SHA-512 spec.
- Spec: [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s spec, unmerged, as rind's vendored s2n-bignum fork carries it; `benchmarks/verified.toml`'s ✓ notes the unmerged PR until upstream merges it (maintainer, 2026-11-13: rind forks an upstream it needs changed and vendors the fork, replacing the 2026-11-07 pin by commit from [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Waiting

- Intel: lists `VSHA512RNDS2`, `VSHA512MSG1`, and `VSHA512MSG2` as data-independent; check the page `admin/ct-vartime` links, last read as updated 2026-02-23.
