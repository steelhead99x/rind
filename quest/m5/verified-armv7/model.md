# [XL] An AArch32 instruction model checks armv7's assembly

## Goal

A machine-checked model of the 32-bit Arm instructions armv7's assembly uses, integer, NEON, and the ARMv8 crypto extension's AArch32 forms, in which a routine's object code can be proven against a spec, as s2n-bignum's models do for x86_64 and aarch64.

## Plan

- No proof tool rind uses has one: s2n-bignum models x86_64, aarch64, and part of RV32IM, and aws-lc-verification's NSym aarch64.
- s2n-bignum has since added a 32-bit architecture itself (found 2026-11-09, correcting the 2026-11-07 audit's "x86_64 and aarch64 only"), all at rind's pin (`b4f17ee`): [awslabs/s2n-bignum#452](https://github.com/awslabs/s2n-bignum/pull/452) generalized its proof infrastructure for 32-bit backends, [#455](https://github.com/awslabs/s2n-bignum/pull/455) added a partial RV32IM model (`thirdparty/s2n-bignum/riscv/proofs/`: integer only, for mldsa-native's RV32 backend), and [#459](https://github.com/awslabs/s2n-bignum/pull/459) and [#467](https://github.com/awslabs/s2n-bignum/pull/467) cosimulate it, the second against a Sail-backed executor. The draft [#492](https://github.com/awslabs/s2n-bignum/pull/492) sets out to prove s2n-bignum's instruction models equivalent to Sail's. An AArch32 model in HOL Light follows that path: 32-bit state, decoder, and cosimulation exist, and NEON and the crypto extension's AArch32 forms are the new work.
- Options, for the maintainer to pick from what this finds: extend s2n-bignum with an AArch32 model in HOL Light (its tactics and specs carry over; asking s2n-bignum whether they would take it is a post outside [the orgs AGENTS.md lists](/AGENTS.md#development), so stop and ask the maintainer first, with no standing approval), or a Lean model derived from Arm's ASL through Sail if it covers AArch32, so armv7's proofs live beside `proofs/`.
- Validate the model against hardware or qemu by random-instruction testing, as s2n-bignum validates its own.
- Prove the smallest routine first, `low/arm/bignum_eq.rs`'s compare, to exercise the model end to end.
