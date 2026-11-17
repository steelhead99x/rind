# [L] x86_64 SHA-256 on AVX2 without SHA-NI is proven

## Goal

SHA-256, and HMAC, HKDF, and PBKDF2 over it, earn the ✓ on x86_64 CPUs with AVX2 but without SHA-NI: Intel's cores from Haswell through Comet Lake and Cascade Lake, still common in clouds.

## Plan

- Runs: `generic::sha256`. OpenSSL's `sha256_block_data_order_avx2` no longer ships. It measured 1.12× faster than aws-lc's AVX routine on an i7-8700 and 1.13× on Arrow Lake.
- Already proven: nothing. aws-lc-verification has no SHA-256 proof.
- Route: a proof of `generic::sha256` against [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s FIPS 180-4 SHA-256 spec. The old route, a HOL Light proof of the AVX2 assembly, is of bytes rind no longer links.
- Spec: [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s spec, unmerged, as rind's vendored s2n-bignum fork carries it; `benchmarks/verified.toml`'s ✓ notes the unmerged PR until upstream merges it (maintainer, 2026-11-13: rind forks an upstream it needs changed and vendors the fork, replacing the 2026-11-07 pin by commit from [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
