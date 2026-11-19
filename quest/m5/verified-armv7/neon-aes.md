# [L] armv7's NEON AES and GHASH are proven

## Goal

aws-lc's `bsaes-armv7`, `vpaes-armv7`, and `ghash-armv4` NEON routines, which armv7 runs for AES and AES-GCM without the crypto extension, are proven on the AArch32 model against FIPS 197 and SP 800-38D, so those operations earn the ✓ on that tier.

## Plan

Decided 2026-11-18 (maintainer, [kixel-ai/rind#619](https://github.com/kixel-ai/rind/pull/619#issuecomment-6994276361)): the proof of [the NEON AES switch](/quest/m2/speed/armv7-neon-aes.md) goes under this epic.

- Route: as [armv7's assembly](/quest/m5/verified-armv7/assembly.md) proves the other routines, against the FIPS 197 and SP 800-38D specs the x86_64 and aarch64 quests write, composed with the Rust proofs of rind's AES-GCM and mode glue.
- Bitsliced AES needs a proof that its bit-sliced S-box circuit computes the S-box; vpaes's needs its permutation tables proven to compose to it. Look for an existing proof of either (s2n-bignum, Fiat, Jasmin) before writing one.

## Required

- [The NEON AES switch](/quest/m2/speed/armv7-neon-aes.md) - the code this proves
- [The AArch32 model covers NEON and the crypto extension](/quest/m5/verified-armv7/model-neon.md) - the NEON instructions the proofs run on
