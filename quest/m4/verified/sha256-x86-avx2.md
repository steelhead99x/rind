# [L] x86_64 SHA-256 on AVX2 without SHA-NI is proven

## Goal

SHA-256, and HMAC, HKDF, and PBKDF2 over it, earn the ✓ on x86_64 CPUs with AVX2 but without SHA-NI: Intel's cores from Haswell through Comet Lake and Cascade Lake, still common in clouds.

## Plan

- Runs: OpenSSL's `sha256_block_data_order_avx2` (`low/x86_64/openssl/`), which aws-lc leaves out: 1.12x faster than aws-lc's AVX routine on an i7-8700 and 1.13x on Arrow Lake.
- Already proven: nothing. aws-lc-verification has no SHA-256 proof.
- Route: a HOL Light proof in s2n-bignum's x86_64 model against [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s FIPS 180-4 SHA-256 spec, sharing the AVX2 model work of `proofs/hol-light/x86_64/sha512_block_data_order_avx2.ml`, whose routine comes from the same `sha512-x86_64.pl`. It enters `proofs/Rind/X86_64/ShaBlocks.lean` as an axiom.
- Spec: [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s spec, unmerged, as rind's vendored s2n-bignum fork carries it; `benchmarks/verified.toml`'s ✓ notes the unmerged PR until upstream merges it (maintainer, 2026-11-13: rind forks an upstream it needs changed and vendors the fork, replacing the 2026-11-07 pin by commit from [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
