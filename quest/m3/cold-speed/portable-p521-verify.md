# [M] Portable P-521 verification keeps pace with aws-lc's C

## Goal

On the nightly's portable row, P-521 ECDSA verification takes no more than aws-lc's C time without assembly, or `benchmarks/gaps.toml` records why not.

## Plan

Found by [the 64-bit limbs work](https://github.com/moq-dev/rind/pull/614), after which P-521 ECDH, key generation, and signing measured 0.91 to 1.03× aws-lc-rs's time on a shared x86_64 host under `--cfg rind_portable`, and verification 1.23 to 1.31×.

Both run fiat-crypto's `p521_64` field arithmetic, so the gap is in rind's composition over it:

- `low/generic/p521.rs` takes and returns 64-bit words, as s2n-bignum's routines do, so every call converts each coordinate into fiat-crypto's unsaturated limbs through its byte encoding and back (`fe` and `words`), about 11 ns a round trip against 25 ns for a field multiplication, measured on that host.
- `mid::p521`'s `public_twin_multiply` adds through `public_add_affine`, which compares x's and y's at the accumulator's z with field multiplications made by separate `low` calls, each converting again.

Plan: keep coordinates in fiat-crypto's representation across a whole scalar multiplication on the portable backend, or convert by shifting words rather than through bytes; measure each on the portable row before choosing. The point formulas stay s2n-bignum's sequences, so the word-for-word tests against it still hold.

## Related

- [The cold tiers are fast](/quest/m3/cold-speed/README.md) - the epic
