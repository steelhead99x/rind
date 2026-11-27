# [S] Poly1305 makes no multiply call on riscv64 without M or Zmmul

## Goal

On a 64-bit RISC-V target with neither the M extension nor Zmmul, Poly1305 calls no `__multi3` (or any other multiply routine) on secret limbs, `admin/ct-vartime` checks it, and build.rs's warning and `PLATFORMS.md`'s entry for that case are gone. No other target's Poly1305 changes.

## Plan

[steelhead99x/rind#191](https://github.com/steelhead99x/rind/pull/191), which supersedes fork PR #87, did the rest of this quest: the 26-bit limbs on every 32-bit portable target, custom target JSON read through `TARGET` and its `llvm-target` (failing closed to `rind_mul16_top`), `rind_mul16`'s half products on Thumb-M, ARMv4T and ARMv5TE, and RV32I, their secret-marked ctgrind test in `generic::mul16`, the `+mul16` rows of `admin/ct-vartime` with its division and floating-point scan, and `finish`'s select through `generic::hide`. What it left: riscv64 without a multiplier keeps `generic::poly1305`'s 64-bit limbs, whose 64x64->128 products are `__multi3` calls on the secret, and build.rs only warns (`riscv64_without_multiply`).

- Recommendation: send that target to `generic::poly1305_32` with `rind_mul16_soft`, which already builds each half product with shifts and adds for RV32I, rather than write a soft 64-bit product for `generic::poly1305`. That is build.rs returning `Half::Soft` for riscv64 without a multiplier and `low/portable/poly1305.rs` and `low/mod.rs` selecting `poly1305_32` under `rind_mul16` as well as on 32-bit targets. It must not set `rind_limb = "32"`, which would move rind's other arithmetic too.
- Checks: an `admin/ct-vartime` row for `riscv64imac-unknown-none-elf` with `-C target-feature=-m` (or a target JSON without M), `+mul16`, built with `-Zbuild-std` as the RV32I row is, that finds no multiply call and no secret branch in `Poly1305::blocks` and `finish`; `sh/build-target-test.sh` cases for that target with and without Zmmul; and the `poly1305_32` tests already run under `rind_mul16_soft` on the host.
- Speed: no riscv64 board without a multiplier is at hand, so the PR says the cost is not measured; the alternative is a library call on the secret, which AGENTS.md forbids.

## Related

- [The 26-bit limb Poly1305 is proven equal to RFC 8439](https://github.com/steelhead99x/rind/pull/318) - the proof plan for `poly1305_32`, in steelhead99x/rind#318 on `claude/base-upstream-main-esp32s3-refresh`
