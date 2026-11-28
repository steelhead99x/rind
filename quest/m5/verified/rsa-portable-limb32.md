# [L] The portable backend's RSA verification is proven on 32-bit limbs

## Goal

RSA-2048 PKCS#1 v1.5 and PSS verification on the portable backend keep their ✓ on 32-bit targets too, wasm32 without `wide-arithmetic` and 32-bit microcontrollers, which run `low::generic::mont` over `low::generic::limb32`: `benchmarks/verified.toml`'s portable rows drop their "on 64-bit limbs" restriction.

## Plan

Found by [the portable backend's RSA verification](https://github.com/kixel-ai/rind/pull/1085), which proved `low::generic::mont` over 64-bit limbs only, since `admin/prove` translates the portable backend on x86_64, where `rind_limb` is 64.

- Translation: a second portable pass under `--cfg rind_limb="32"`, as CI's 32-bit-limb check builds, with the RSA proofs `admin/prove` writes from x86_64's copied to it as to the 64-bit pass.
- Proof: `Mont.lean`'s lemmas (parked in `proofs/parked/Rind/Portable/` until [the four-product `mul_add`](/quest/m4/verified/rsa-verify-portable-four-product.md) is proven) over a limb width of either 32 or 64 bits rather than `U64`, and `limb32`'s `join` and `limbs`, which split the 64-bit words `PosInt` holds into limbs and back.
- Report: the two rows' proofs name both widths.

## Required

- [The portable backend's RSA verification is proven over the four-product mul_add](/quest/m4/verified/rsa-verify-portable-four-product.md) - the 64-bit proof this generalises, back in the build

## Related

- [RSA signing is proven](/quest/m4/verified/rsa-sign.md) - runs the same products for its private operation
