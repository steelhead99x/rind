# [M] The portable backend's RSA verification is proven over the four-product mul_add

## Goal

RSA-2048 PKCS#1 v1.5 and PSS SHA-256 verification on the portable backend earn the ✓ again: `low::generic::mont`'s `mul_add`, which issues four row products a block before their carry chain and finishes a remainder of one to three limbs a limb at a time, is proven to compute `x + u·y`, so the parked proofs build again and `benchmarks/verified.toml` gets back its two portable rows.

## Plan

- Why it is parked: kixel-ai/rind#1085 proved portable RSA verification over the one-limb `mul_add` loop. This fork's #76 blocks that loop by four, which measured portable RSA at 0.78 to 0.93 of aws-lc's C time against 0.85 to 0.97 (ALGORITHMS.md), and the sync that took #1085 kept the faster code, as AGENTS.md's speed rule says, and parked the proof: `proofs/parked/Rind/Portable/{Mont,Bignum,RsaMont}.lean`, outside the `Rind` library's glob.
- Reprove `mul_add_spec` in `Mont.lean` over the blocks, as its `mul_add2` proof already does for `as_chunks_mut::<BLOCK>`, `core::array::from_fn`'s products, and the indexed remainder loop: a block loop invariant over `wordsNat` of the prefix and the carry, then the remainder's, which is the current `mul_add_loop_spec`. The carry bound is `mul_add_limb_bound`'s, since each partial sum is at most `(2^64 - 1)^2 + 2 (2^64 - 1)`. The rest of `Mont.lean`, `Bignum.lean`, and `RsaMont.lean` take `mul_add_spec` as it is stated now, so nothing above it should change.
- Bring back: `git mv` the three files to `proofs/Rind/Portable/`; restore `admin/prove`'s loop that writes `RsaPublic RsaBytes RsaIfma RsaVerify RsaPss RsaKey SignatureBuffer RsaDispatch` from x86_64's (removed by the sync that parked them, steelhead99x/rind#349, where it replaced the loop with an `rm -f` of those files; `git show 53e5157c8:admin/prove` has it), which also drops that `rm -f`; restore `import Rind.Portable.RsaDispatch` and the six `rsa_*` and `rsa2048_mont_products` `#print axioms` checks in `Rind/Portable/Axioms.lean` (`git show 53e5157c8:proofs/Rind/Portable/Axioms.lean`); restore the two portable rows in `benchmarks/verified.toml` and its header comment (`git show 53e5157c8:benchmarks/verified.toml`), and re-render with `admin/bench-report render`; and revert proofs/README.md's "The portable backend" section and file list to say so.
- Check with `admin/prove lean` on a host that runs it (`admin/hw/lean-replay.sh`), and the `prove` workflow.

## Related

- [The portable backend's RSA verification is proven on 32-bit limbs](/quest/m5/verified/rsa-portable-limb32.md) - generalises the same `Mont.lean` to 32-bit limbs
- [RSA signing is proven](/quest/m4/verified/rsa-sign.md) - runs the same products for its private operation
