# [S] Ed25519's key-pair verification assumes no group fact

## Goal

Ed25519's `ed25519_key_pair_verify`, on x86_64 and aarch64, drops its assumption `hA` that the base point times the key's scalar is a point of `edwards25519_group`.

## Plan

- The fact is closure of `edwards25519_group` under `edPow`: `edB` is on the curve, and `edPow`'s multiples of a point on the curve stay on it. [Ed25519 AVX2 verification](/quest/m4/verified/ed25519-avx2-verify.md)'s [kixel-ai/rind#646](https://github.com/kixel-ai/rind/pull/646) adds `Rind/Edwards.lean`'s group of points over `ZMod p25519` and `Rind/Ed25519Group.lean`'s `edPow_ofPoint` and `edOnCurve_ofPoint`, which give it in a few lines: build on those rather than a second copy of the group.
- P-256's half of this quest landed in `Rind/NistOrder.lean`: every finite point of a NIST curve has order n, by an elementary count (at most 2p + 1 points, Lagrange, Cauchy, and a kernel check that x³ - 3x + b has no root mod p), so `P256Order` is `p256_order`, a theorem.

## Required

- [Ed25519 AVX2 verification](/quest/m4/verified/ed25519-avx2-verify.md) - lands `Rind/Edwards.lean`'s group and `Rind/Ed25519Group.lean`'s `edPow_ofPoint`, from which closure follows
