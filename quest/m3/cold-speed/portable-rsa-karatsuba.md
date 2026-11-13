# [M] Portable RSA above 3072 bits keeps pace with aws-lc's C

## Goal

On the nightly's portable row, RSA signing at 4096 bits and up, and verification at 3072 bits and up, take no more than aws-lc's C time without assembly, or `benchmarks/gaps.toml` records why not.

## Plan

Found by [the 64-bit limbs work](https://github.com/kixel-ai/rind/pull/614), which brought RSA-2048 and RSA-3072 signing level with aws-lc's C on that row. Measured there on a shared x86_64 host under `--cfg rind_portable`, against aws-lc-rs built without assembly at opt-level 2: signing at 4096 bits 1.09×, 6144 1.20×, and 8192 1.25× aws-lc-rs's time; verification at 3072 bits 1.21×, 4096 1.28×, 6144 1.34×, and 8192 1.44×.

- Likely cause, to confirm first: rind's `low/generic/mont.rs` multiplies and squares by the schoolbook method at every width, and aws-lc's C (`crypto/fipsmodule/bn/mul.c`) switches to Karatsuba from 16 words (`BN_MULL_SIZE_NORMAL`, `BN_SQR_RECURSIVE_SIZE_NORMAL`), except in `bn_mod_mul_montgomery_small` up to 17 words, which RSA-2048's primes take. RSA-3072 signing's 24-word primes and verification's 48-word modulus are where the gap begins.
- If so, a Karatsuba product and square for the portable backend, of fixed structure: its split, the sign of each half-difference, and the carries chosen by masks, never by branches, with a ctgrind test, as `mont.rs`'s routines have. Measure its crossover against the schoolbook loop on the portable row, on both limb widths.
- Its correctness argument is the textbook identity; the tests check it word for word against s2n-bignum on x86_64 and aarch64, on both limb widths, as `mont.rs`'s tests do now. It runs unproven, as the loop it speeds up does: [the portable backend's proofs](/quest/m4/verified/portable.md) cover that loop for RSA verification and [signing](/quest/m4/verified/rsa-sign.md).

Measured on an Intel Xeon (family 6, model 207) on 2026-11-12. The product and scratch are stack slots; only the used `2n` and `4n` prefix is zeroed, and left unwiped, as stack scratch is. A constant-time Karatsuba square does not beat the schoolbook square at a signing prime: three interleaved rounds, 64-bit limbs, schoolbook then Karatsuba, 1.15 µs then 1.25 µs at 32 limbs (4096-bit signing), 2.51 µs then 2.55 µs at 48 (6144-bit signing), and 4.48 µs then 4.55 µs at 64 (8192-bit signing). The crossover that does win is a 64-bit product from 48 limbs and a square from 96. 32-bit limbs were measured on an AMD Ryzen 5 7535HS (family 25, model 68) on 2026-11-12, release, median of three interleaved rounds, one Karatsuba split: a product first wins at 48 limbs (schoolbook 1.210 µs, Karatsuba 1.102 µs) and a square at 80 (1.835 µs and 1.725 µs). At the production cutoffs, 96 limbs, the product is 5.113 µs then 4.082 µs, and at 128 the square is 4.807 µs then 3.995 µs, so those cutoffs stay 96 and 128. Montgomery reduction stays schoolbook and is most of a square, so signing at 4096 bits and up and verification at 3072 and 4096 bits still run the schoolbook square. On the Xeon, against a build that never takes Karatsuba, an earlier short run was 0.99× at 3072-bit verification and 1.05× at 4096-bit signing (the square is schoolbook either way). After the scratch moved to the stack, the median of 28 rounds of 100 verifications was 0.92× at 6144 bits (199 µs versus 218 µs) and 0.90× at 8192 bits (355 µs versus 393 µs). Against aws-lc's C those sizes stayed about 1.15× to 1.22×. The goal is not met. `benchmarks/gaps.toml` still points here. Whether the remainder stays on this quest or moves to a follow-up for the reduction is a maintainer question on the PR that landed the Karatsuba.

## Related

- [The cold tiers are fast](/quest/m3/cold-speed/README.md) - the epic
