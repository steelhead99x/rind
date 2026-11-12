# [M] Portable RSA above 3072 bits keeps pace with aws-lc's C

## Goal

On the nightly's portable row, RSA signing at 4096 bits and up, and verification at 3072 bits and up, take no more than aws-lc's C time without assembly, or `benchmarks/gaps.toml` records why not.

## Plan

Found by [the 64-bit limbs work](https://github.com/moq-dev/rind/pull/614), which brought RSA-2048 and RSA-3072 signing level with aws-lc's C on that row. Measured there on a shared x86_64 host under `--cfg rind_portable`, against aws-lc-rs built without assembly at opt-level 2: signing at 4096 bits 1.09×, 6144 1.20×, and 8192 1.25× aws-lc-rs's time; verification at 3072 bits 1.21×, 4096 1.28×, 6144 1.34×, and 8192 1.44×.

- Likely cause, to confirm first: rind's `low/generic/mont.rs` multiplies and squares by the schoolbook method at every width, and aws-lc's C (`crypto/fipsmodule/bn/mul.c`) switches to Karatsuba from 16 words (`BN_MULL_SIZE_NORMAL`, `BN_SQR_RECURSIVE_SIZE_NORMAL`), except in `bn_mod_mul_montgomery_small` up to 17 words, which RSA-2048's primes take. RSA-3072 signing's 24-word primes and verification's 48-word modulus are where the gap begins.
- If so, a Karatsuba product and square for the portable backend, of fixed structure: its split, the sign of each half-difference, and the carries chosen by masks, never by branches, with a ctgrind test, as `mont.rs`'s routines have. Measure its crossover against the schoolbook loop on the portable row, on both limb widths.
- Its correctness argument is the textbook identity; the tests check it word for word against s2n-bignum on x86_64 and aarch64, on both limb widths, as `mont.rs`'s tests do now. It runs unproven, as the loop it speeds up does: [RSA verification's proof](/quest/m4/verified/rsa-verify.md) and [signing's](/quest/m4/verified/rsa-sign.md) cover the portable loop through [the portable backend's proofs](/quest/m4/verified/portable.md).

## Related

- [The cold tiers are fast](/quest/m3/cold-speed/README.md) - the epic
