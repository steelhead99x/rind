# [L] x86_64 SHA-512 on the SHA512 instructions is proven

## Goal

SHA-384, SHA-512, SHA-512/256, Ed25519 signing, and HMAC and HKDF over SHA-384 earn the ✓ on x86_64 CPUs with the SHA512 instructions (Arrow Lake, Lunar Lake, and later Intel cores). Ed25519 verification there also needs [its half-size check proven](/quest/m4/verified/ed25519-half-scalar.md).

## Plan

- Runs: the unrolled body in `generic::sha512`. OpenSSL's `sha512_block_data_order_sha512ext` no longer ships. It measured 5.4× faster than aws-lc's AVX routine on Arrow Lake. The SHA512 instructions are not what the tests execute, so this tree does not ship an intrinsic kernel for them.
- Already proven: nothing. s2n-bignum's x86_64 model lacks `vsha512rnds2`, `vsha512msg1`, and `vsha512msg2`.
- Route: add the three instructions to s2n-bignum's x86_64 model from Intel's manual, then a HOL Light proof of the routine against [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s FIPS 180-4 SHA-512 spec.
- Spec: [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s spec, unmerged, as rind's vendored s2n-bignum fork carries it; `benchmarks/verified.toml`'s ✓ notes the unmerged PR until upstream merges it (maintainer, 2026-11-13: rind forks an upstream it needs changed and vendors the fork, replacing the 2026-11-07 pin by commit from [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
