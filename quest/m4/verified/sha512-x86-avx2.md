# [L] x86_64 SHA-512 on AVX2 is proven

## Goal

SHA-384, SHA-512, and SHA-512/256, and with them Ed25519 and HMAC and HKDF over SHA-384, earn the ✓ on x86_64 CPUs with AVX2 but without the SHA512 instructions: every AMD Zen and every Intel core from Haswell, the tier most x86_64 hosts run, which `benchmarks/verified.toml`'s entries now exclude with `!avx2`.

## Plan

- Runs: OpenSSL's `sha512_block_data_order_avx2` (`low/x86_64/openssl/`), which aws-lc leaves out: 1.18x faster than aws-lc's proven AVX routine on an i7-8700, 1.15x on Arrow Lake, and 1.47x faster than its scalar one on Zen 3. The proven AVX routine is slower, so switching to it fails the speed rule.
- Already proven: nothing of this routine. aws-lc-verification's SAW proof covers the AVX routine, from the same `sha512-x86_64.pl`, but not its AVX2 path.
- Route: a HOL Light proof in s2n-bignum's x86_64 model, whose AVX2 decoding is broad (add any instruction the routine uses that it lacks, such as BMI2's `rorx`), against [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s FIPS 180-4 SHA-512 spec. Then an axiom in `proofs/Rind/X86_64/AwsLc.lean`'s place for this routine, and `RunsSha512` widened to this tier.
- Spec pin: build on [awslabs/s2n-bignum#420](https://github.com/awslabs/s2n-bignum/pull/420)'s spec at a pinned commit while it is unmerged, and move to the merged version when it lands; `benchmarks/verified.toml`'s ✓ notes the pin (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
