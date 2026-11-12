# [M] 64-bit portable targets use 64-bit limbs

## Goal

On the portable backend's 64-bit targets (riscv64, loongarch64, s390x, powerpc64), RSA and the P-256, P-384, and P-521 arithmetic run on 64-bit limbs, and the nightly's portable row shows them at least as fast as aws-lc's C without assembly, or `benchmarks/gaps.toml` records why not. 32-bit targets, armv7 among them, keep their 32-bit limbs, and wasm32 gets the width that measures faster for it.

## Plan

Planned from the 2026-11-09 speed audit. Decided with the maintainer that day:

- Scope: correctness tooling, speed measurement, and portable speed ✅ (rejected: no portable speed work, correctness only). This lifts the targets epic's non-goal that speed on the new architectures waits for a consumer.
- Milestone: cold-tier speed work joins m3 ✅ (rejected: m2 beside the targets, m4).
- AGENTS.md's speed rule: run the fastest permissively licensed source; take a formally verified one only where it measures as fast at every size; otherwise run the fastest and plan its proof ✅ (rejected: verified code within about 10% on cold tiers only, or everywhere, as AGENTS.md said).

Evidence:

- The portable backend was generalized from armv7, so its arithmetic is 32-bit on every target: `low::PosInt`'s products are formed from 32-bit halves (`rind/src/low/generic/bignum.rs:12`, `mont_mul_limbs` at `:361`), and the curves run fiat-crypto's `p256_32`, `p384_32`, and `p521_32` with rind's 32-bit Montgomery loops (`rind/src/low/generic/p256.rs:29`, `p384.rs:24`, `p521.rs:25`).
- The nightly's portable row, x86_64 under `--cfg rind_portable` against aws-lc's C at opt-level 2, in [run 42526977036](https://github.com/moq-dev/rind/actions/runs/42526977036) on an EPYC 7763: RSA signing 2.6 to 3.9× aws-lc-rs's time, RSA verification 2.6 to 4.4×, key generation 2.8 to 3.0×, OAEP 3.0×, P-521 2.0 to 2.8×, P-256 verification 1.19 to 1.32×, and through them rustls full handshakes with an RSA-2048 certificate 2.47× and a P-521 one 2.23×. P-384 showed no gap over 1.07×.
- Expected gain: an estimate, not a measurement. Half the limbs is a quarter of a schoolbook multiply's word products, and the ratios above, against C that runs 64-bit limbs there, bound it at 2 to 4× for RSA and P-521.

Sources:

- fiat-crypto 0.3, already a dependency (`rind/Cargo.toml:29`), ships `p256_64`, `p256_scalar_64`, `p384_64`, `p384_scalar_64`, and `p521_64`. MIT OR Apache-2.0 OR BSD-1-Clause. Its arithmetic is proven in Coq, with the printing to Rust trusted.
- RSA: rind's Montgomery loop over `u64` limbs with `u128` products, unproven as the 32-bit loop is today. HACL*'s verified bignum is the alternative ALGORITHMS.md already turned down, for leaving scratch unwiped on the heap.

Measure first, on the portable row:

- fiat-crypto's `_64` multiplication and squaring against a `u128` loop of rind's, for each curve. On armv7 rind replaced fiat-crypto's multiplication because LLVM spilled its carry chains (`rind/src/low/generic/p256.rs:8`); whether it does on a 64-bit target is unknown. Under the rule above, fiat-crypto's proven code stays wherever it is as fast at every size.
- P-521's group order, where fiat-crypto's 9-word output measured 5× slower on armv7 (`rind/src/low/generic/p521.rs:11`).
- The row is x86_64, a stand-in: riscv64 has no carry flag, so the pick is unconfirmed there until a consumer has hardware. Say so in ALGORITHMS.md.

wasm32, a supported portable target since 2026-11-09:

- Its pointers are 32-bit but it multiplies `i64` natively. A 64×64→128 product needs the wide-arithmetic proposal (`i64.mul_wide_u`, `i64.add128`), which is at phase 4 and on by default in Firefox 155; Chrome's status was not confirmed. rustc lists it as the `wide-arithmetic` target feature (`rustc --print target-features --target wasm32-unknown-unknown`). Without it a `u128` product is a library call.
- So pick the width by a compile-time cfg, not `target_pointer_width` alone: recommend 64-bit limbs on 64-bit targets and on wasm32 built with `wide-arithmetic`, and 32-bit limbs elsewhere, whose 32×32→64 product is one `i64.mul`. One backend still compiles per target. Time both widths on wasm32, with and without the feature, before settling it.

Guidance:

- Keep both widths compiled under `cfg(test)` on x86_64 and aarch64, where the generic modules are checked word for word against s2n-bignum.
- A `u128` product must compile to multiply instructions, never a call whose time could depend on a secret: add the 64-bit paths to ctgrind on the portable build.
- Proof status: code that stays fiat-crypto's keeps its proof. Each rind loop that wins runs unproven, and the PR suggests its proof quest for [the verification epic](/quest/m3/verified/README.md).
- Update ALGORITHMS.md's portable column, PLATFORMS.md, and each generic module's header, and record what remains in `benchmarks/gaps.toml`.
