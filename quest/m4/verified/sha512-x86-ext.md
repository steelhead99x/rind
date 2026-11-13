# [L] x86_64 SHA-512 on the SHA512 instructions is proven

## Goal

SHA-384, SHA-512, SHA-512/256, Ed25519, and HMAC and HKDF over SHA-384 earn the ✓ on x86_64 CPUs with the SHA512 instructions (Arrow Lake, Lunar Lake, and later Intel cores).

## Plan

- Runs: OpenSSL's `sha512_block_data_order_sha512ext` (`low/x86_64/openssl/`), 5.4x faster than aws-lc's AVX routine on Arrow Lake.
- Already proven: nothing. s2n-bignum's x86_64 model lacks `vsha512rnds2`, `vsha512msg1`, and `vsha512msg2`.
- Route: add the three instructions to s2n-bignum's x86_64 model from Intel's manual, then a HOL Light proof of the routine against [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s FIPS 180-4 SHA-512 spec.
- Spec pin: build on [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s spec at a pinned commit while it is unmerged, and move to the merged version when it lands; `benchmarks/verified.toml`'s ✓ notes the pin (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [x86_64 SHA-512 on AVX2 is proven](/quest/m4/verified/sha512-x86-avx2.md) - the SHA-512 spec work and the `RunsSha512` widening this extends
