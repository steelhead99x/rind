# [XL] x86_64 SHA-NI SHA-256's frozen assembly is proven in HOL Light

## Goal

`proofs/hol-light/x86_64/` proves each frozen `asm!` block of x86_64's SHA-NI SHA-256, as rind's release build emits it, computes s2n-bignum's FIPS 180-4 spec, `sha256_hash_blocks`: the block function over its blocks, and the finish over its blocks then the padded block or blocks its register words give, with the digest's bytes. `admin/prove hol-light` and `admin/prove bytes` check them, as they do aarch64's.

## Plan

- Build on [awslabs/s2n-bignum#450](https://github.com/awslabs/s2n-bignum/pull/450) at 7ef212f3f517635c57174475f413c74013ae79a5: its `x86/proofs/sha256_compress_hw.ml` proves the same rounds on aws-lc's routine, and its bridge lemmas (`SHA256_RNDS2_BRIDGE`, `SHA256_MSG1_BRIDGE`, `SHA256_MSG2_BRIDGE`, `PSHUFB_BYTESWAP`) state the instructions' effect on the spec's words. Vendor its model additions (`x86/proofs/x86.ml`, `decode.ml`, `instruction.ml`) unchanged under `proofs/hol-light/s2n-bignum/`, as the epic's Plan says. `admin/prove` then applies rind's `x86.patch` to those vendored copies rather than the submodule's, so drop from the patch, its cosimulation, and the README's list the instructions #450 also adds, `PALIGNR`, `PUNPCKLQDQ`, and `PUNPCKHQDQ`, and redo any hunk #450's copies move.
- Its `x86/proofs/utils/sha256_spec.ml` differs from the vendored #415 copy only in a comment; keep one copy and say which in `proofs/hol-light/s2n-bignum/README.md`.
- Any instruction the frozen blocks use beyond #450's and `x86.patch`'s goes into `x86.patch`, with its cosimulation in `x86-cosim.ml` and its row in the README (maintainer, 2026-11-11, on [moq-dev/rind#627](https://github.com/moq-dev/rind/pull/627): rind carries its own extension of the model; rejected: send it upstream first and vendor it from that pull request).
- Prove the round body once where the blocks share it, as #450 does per group of four rounds, rather than simulate each copy.

## Required

- [Frozen assembly](/quest/m3/verified/sha256-block/frozen.md) - the blocks this proves, and their instruction set
