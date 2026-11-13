# [L] x86_64 SHA-256 on AVX2 without SHA-NI is proven

## Goal

SHA-256, and HMAC, HKDF, and PBKDF2 over it, earn the ✓ on x86_64 CPUs with AVX2 but without SHA-NI: Intel's cores from Haswell through Comet Lake and Cascade Lake, still common in clouds.

## Plan

- Runs: OpenSSL's `sha256_block_data_order_avx2` (`low/x86_64/openssl/`), which aws-lc leaves out: 1.12x faster than aws-lc's AVX routine on an i7-8700 and 1.13x on Arrow Lake.
- Already proven: nothing. aws-lc-verification has no SHA-256 proof.
- Route: a HOL Light proof in s2n-bignum's x86_64 model against [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s FIPS 180-4 SHA-256 spec, sharing the AVX2 model work with [x86_64 SHA-512 on AVX2](/quest/m4/verified/sha512-x86-avx2.md), whose routine comes from the same `sha512-x86_64.pl`. It enters `proofs/Rind/X86_64/ShaBlocks.lean` as an axiom.
- Spec pin: build on [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415)'s spec at a pinned commit while it is unmerged, and move to the merged version when it lands; `benchmarks/verified.toml`'s ✓ notes the pin (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
