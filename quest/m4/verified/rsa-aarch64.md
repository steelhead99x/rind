# [L] aarch64's RSA verification and signing are proven

## Goal

RSA verification and signing earn the ✓ on aarch64: the glue `proofs/Rind/X86_64/RsaDispatch.lean` proves for x86_64 runs on `admin/prove`'s aarch64 translation over the Montgomery products `proofs/Rind/Aarch64/RsaMont.lean`'s `mont_products` proves from aws-lc's `bn_mul_mont`, with no hypothesis on them. The proof covers the Linux build's object only: Apple's `aws_lc/bn_mul_mont.apple.s` lacks the entry's `.align 5`, so its branches can land at other offsets and no proof covers it. The ✓ on Apple needs its own byte check or proof of that object, which this quest includes.

## Plan

- Done: the products. `mont_mul_spec`, `mont_sqr_spec`, and `mont_products` follow from the axiom restating rind's HOL Light `BN_MUL_MONT_SUBROUTINE_CORRECT`, over aarch64's `MontArgs`, which bounds the width below `2^32`.
- Decided 2026-11-20 (owner, on [steelhead99x/rind#255](https://github.com/steelhead99x/rind/pull/255)): the axiom's `x + 32` and `m + 32` no-wrap hypotheses, which the 4x path needs at a multiple of four words, are a trusted step: the model has no addresses, and a slice of at least 32 bytes does not end at the top of the address space. This quest keeps it unless it models pointers.
- Translation: add the RSA start points `admin/prove` gives x86_64 (`high::rsa::VerifyingKey`'s loaders and `verify_*`, `low::posint`) to the aarch64 pass, with `low::aarch64::mont` already included, and leave aarch64's DER parsing and the RSA signing's opaque parts as x86_64 does.
- Proof: copy `Rind/X86_64/{RsaBytes,RsaPublic,RsaKey,RsaVerify,RsaPss,RsaDispatch}.lean` to `Rind/Aarch64/` by renaming the target in `admin/prove`, over aarch64's own `RsaMont.lean` and its `MontProducts`, and add the guards to `Rind/Aarch64/Axioms.lean`. Signing follows [RSA signing is proven](/quest/m4/verified/rsa-sign.md)'s proof of the private operation, run on aarch64's products.
- Apple: byte-check or prove `bn_mul_mont.apple.s`. The cheapest route is a byte check against the Linux object modulo the entry's alignment, as `admin/prove bytes` compares other builds' objects, if the two differ only in directives and branch offsets; otherwise a HOL Light proof of the Apple object as for the Linux one.
- Report: `verified.toml` rows for RSA verification and signing with `arch = "aarch64"`, and `proofs/README.md` updated.

## Waiting

- Claude: Apple's `bn_mul_mont.apple.s` has no proof or byte check yet; start on it once the Linux glue's translation builds, and drop this item when the Apple object is covered.

## Related

- [RSA signing is proven](/quest/m4/verified/rsa-sign.md) - runs the same products for its private operation
- [The portable backend's RSA verification is proven](/quest/m4/verified/rsa-verify-portable.md) - the same glue on another target
