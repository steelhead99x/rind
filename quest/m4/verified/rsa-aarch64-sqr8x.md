# [XL] aarch64's 8x RSA Montgomery squaring is proven

## Goal

aws-lc's aarch64 `__bn_sqr8x_mont`, which `bn_mul_mont` runs to square at widths that are a multiple of eight, is proven in HOL Light against s2n-bignum's `bignum_montmul` specification with both operands the same, through `bn_mul_mont`'s dispatch to it. RSA signing's squarings at RSA's sizes run it.

## Plan

- Runs: the `__bn_sqr8x_mont` part of `low/aarch64/aws_lc/bn_mul_mont.*.s` (aws-lc's `armv8-mont.pl`), about 630 instructions, entered from offset 0x4 when `x` and `y` are the same pointer. It squares by computing the off-diagonal products once and doubling them, then reduces eight words at a time.
- Route: extend `proofs/hol-light/aarch64/bn_mul_mont.ml` in s2n-bignum's aarch64 model, scalar instructions only, with the other two routines' statement for widths that are a multiple of eight and `x = y`, except that its frame is the 128-byte save area plus `16k` bytes of scratch, `16k + 128` bytes below the stack pointer, with nonoverlap hypotheses to match, and it saves and restores x19 to x28. It reuses their lemmas and tactics. With all three proven, one theorem covers `bn_mul_mont` at every width from two words.
- Decided 2026-11-12 (maintainer, /quest-unblock): ✅ its own quest, after `__bn_mul4x_mont` (rejected: one quest for all of `bn_mul_mont`). The theorem takes `n * n0 + 1 == 0 (mod 2^64)` as a hypothesis, matching `MontArgs` in `proofs/Rind/X86_64/RsaMont.lean`.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).

## Required

- [4x routine](/quest/m4/verified/rsa-aarch64-mul4x.md) - the lemmas and tactics this extends, and the order the maintainer set
