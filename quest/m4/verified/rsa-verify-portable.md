# [L] The portable backend's RSA verification is proven

## Goal

RSA-2048 PKCS#1 v1.5 verification earns the ✓ on the portable backend (`arch = "portable"` in `benchmarks/verified.toml`): `Rind/X86_64/RsaDispatch.lean`'s proof runs on `admin/prove`'s portable translation, over `low/generic/mont.rs`'s Montgomery products, proven in Lean.

## Plan

Found by [the portable backend's proofs](https://github.com/kixel-ai/rind/pull/649): [kixel-ai/rind#624](https://github.com/kixel-ai/rind/pull/624) proved RSA verification's glue on x86_64 over its Montgomery products as hypotheses (`MontProducts` in `Rind/X86_64/RsaMont.lean`), and no quest proved the portable backend's products.

Decided 2026-11-13 (maintainer, /quest-merge of #649): ✅ keep this quest (rejected: drop).

- Runs: `low/generic/mont.rs`'s `mont_mul` and `mont_sqr`: since [kixel-ai/rind#702](https://github.com/kixel-ai/rind/pull/702), interleaved CIOS (`mont_mul_limbs`) below `SEPARATE` limbs, and above it a full product, by schoolbook passes split by Karatsuba from `KARATSUBA_MUL` limbs (`KARATSUBA_SQR` for squares), then `redc`'s reduction, over `Limb`, which is `u64` on 64-bit targets since [kixel-ai/rind#614](https://github.com/kixel-ai/rind/pull/614), and its `bignum_montifier`, `bignum_montredc`, and `neg_inverse` for key loading.
- Translation: add the RSA start points `admin/prove` gives x86_64 to the portable pass, with `low::generic::mont` included and `low::posint` translated as on x86_64.
- Proof: prove `mont_mul` and `mont_sqr` return `MontResult` at every width, CIOS, the Karatsuba split, and `redc` each against `Nat` arithmetic, then run `RsaDispatch.lean` and its imports on the portable translation by renaming the target, over a `RsaMont.lean` of the portable backend's own.
- Report: a `verified.toml` row for `rsa2048-pkcs1-sha256-verify` with `arch = "portable"`, and the portable section of `proofs/README.md` updated.

## Related

- [RSA signing is proven](/quest/m4/verified/rsa-sign.md) - runs the same products for its private operation
