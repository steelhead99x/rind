# The hot tiers get the speedups nobody has taken yet

## Goal

On the tiers rind already runs assembly for, each speedup the 2026-11-12 audit found that the fastest library does not have, or that rind's own structure hides, is taken or measured and refused: AVX-512 cores that downclock stop paying for 512-bit vectors, Ed25519 verification does about half the doublings, and an ML-DSA key expands once instead of on every call.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit). None of the three shows as a gap in BENCHMARKS.md: no report host has the cores the first is about, the second is past what aws-lc-rs does, and the report times ML-DSA on no host. The cold tiers' speed was m3's, and has landed; measuring is [the bench epic's](/quest/m2/bench/README.md).

- ✅ Adopt the rule that keeps 512-bit kernels off Intel cores that downclock for them, now and unmeasured (rejected: measure first, which needs an Ice Lake or Tiger Lake host nobody has; no quest).
- ✅ Ed25519 verification with half-size scalars, for single signatures only (rejected: a batch verification API too; neither). Nothing rind serves verifies in batches, and a batch API accepts a different set of signatures unless it is built with care.
- ML-DSA keys expand once, which needed no decision: it is the same API doing less work.

Considered and left out, so don't raise them again without new evidence:

- An RSA tier on AVX-IFMA, the VEX encoding Alder Lake and Zen 5 have without AVX-512. The evidence on `desktop` points against it, and the way to find out is an A/B with `OPENSSL_ia32cap` on OpenSSL, which has that tier, before any rind code.
- A batch API for Ed25519, as above.
- RSA key generation on armv7, 1.34 to 1.93 times aws-lc-rs's time in BENCHMARKS.md: nobody generates RSA keys on a 32-bit board often enough to care.
- wasm's simd128, SVE2, and riscv64's vector crypto: no consumer on any of them, and no host to measure the last two.
