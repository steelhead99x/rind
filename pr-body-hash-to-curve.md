feat(hash-to-curve): hash to P-256, P-384, and P-521 in constant time

## Problem

OPRF and FROST(P-256) need RFC 9380's simplified-SWU random-oracle suites for P-256, P-384, and P-521. The OPRF client hashes the password, so the map has to be constant time. rind had no hash-to-curve.

## Approach

The suites live in `mid`, with no public API. Each curve exposes `hash_to_curve`, `hash_to_field`, and `hash_to_scalar`.

`expand_message_xmd` uses rind's SHA-256, SHA-384, and SHA-512. An empty domain-separation tag is refused (RFC 9380 section 3.1). A requested length above 65535 bytes, or one that needs more than 255 hash blocks, is refused. A tag longer than 255 bytes is replaced by `H("H2C-OVERSIZE-DST-" || DST)` as section 5.3.3 requires, which Appendix K.2 checks. It is not truncated.

The map is Appendix F.2's straight-line simplified SWU. `sqrt_ratio` is Appendix F.2.1.2: one exponentiation by the public `(p - 3) / 4` and a conditional select, with no branch on the value. Field addition, subtraction, multiplication, squaring, negation, and inversion are the operations the NIST curves already run: s2n-bignum where rind already uses it, and fiat-crypto on armv7 and the portable backend, with the same correctness argument as those curves. Affine addition is the group law on those operations; equal points and opposite points are selected, not branched on. Each cofactor is 1, so clearing it is the identity.

The two uniform field elements stay on the stack. `L` outside 1..=128 is `ExpandError::OutputLength`. A reduction wider than two field elements is refused, because `bignum_montredc` reads only the lowest `2M` limbs.

`_NU_` encodings and edwards25519's Elligator 2 map are not implemented.

`quest/m4/protocols/hash-to-curve.md` stays. The quest says the map ships with its first consumer, and this change has no public API. Draft #616 edits that same quest file and also edits `rind/src/mid/p256.rs`, which this branch extends with the P-256 map.

## Impact

- No public API change.

## Alternatives

- Refusing a domain-separation tag longer than 255 bytes would match the abort in the `expand_message_xmd` steps, and would fail Appendix K.2. Section 5.3.3 requires the replacement hash instead.
- Encoding to the curve (`_NU_`) is left out. Only ECVRF's SSWU and ELL2 suites would use it, and that quest offers only TAI.

## Follow-ups

- OPRF needs to multiply the hashed point by a secret scalar, including the point at infinity, without branching on the infinity flag.
- No benchmark against aws-lc. The primitive has no public API and is not on a MoQ hot path.
- #614 moves the portable NIST-curve arithmetic onto 64-bit limbs in `low`, which these maps call. It does not edit `mid/p256.rs`.

## Testing

Head `dab34e89616f43841bcf592c68d0148281039cf4`.

`nix develop --command just ci upstream/main` exited 0 (fmt, clippy, nextest, structure, MSRV, cross builds, `admin/ct-vartime`, `cargo deny`, license, `admin/testing`, fixtures, patch, shell, nix).

`cargo test -p rind --lib hash_to_curve`:

```
test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 644 filtered out; finished in 0.02s
```

That includes the Appendix J suite vectors (P-256, P-384, P-521), the Appendix K `expand_message_xmd` vectors, the hostile-length checks, `p256_and_p384_match_aws_lc`, `rustcrypto_p521`, and `field_scalar_and_sha384_match_hash2curve`.

The same 15 tests with the portable backend forced (`RUSTFLAGS='--cfg rind_portable --cfg curve25519_dalek_backend="serial"'`):

```
test result: ok. 15 passed; 0 failed; 0 ignored; 0 measured; 401 filtered out; finished in 0.12s
```

`nix develop .#ctgrind --command admin/ctgrind unit ctgrind_maps_and_scalars`:

```
test mid::hash_to_curve::tests::ctgrind_maps_and_scalars ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 651 filtered out; finished in 0.44s
ERROR SUMMARY: 0 errors from 0 contexts (suppressed: 0 from 0)
```

## Review

Rounds by a model from a second vendor, different from the one that wrote the code. The SHAs are this branch's commits of those changes.

| Round | Head reviewed | Base | Score | Findings |
| --- | --- | --- | --- | --- |
| 1 (low effort) | `5e520cf5` | f5f82bca | 7/10 | none |
| 1 (deep) | `5e520cf5` | f5f82bca | 7/10 | 4 medium, 4 low |
| 2 | `1ff9d7c2` | f5f82bca | 9/10 | 1 low |
| 3 | `0ad967c1` | f5f82bca | 10/10 | none |

Seven round-1 findings were fixed. The eighth (replacing the block-count loop with `div_ceil`) was refuted, because that division would need an `admin/ct-vartime` allowance, and round 2 accepted the refutation. The round-2 low finding (a `const SWU` doc comment naming a test that doesn't exist) is fixed in `0ad967c1`.

Round 3 covered the hardening in `dd84f4db` (stack-held field elements, refused wide reductions, tests at each modulus and with 255- and 256-byte tags) and has no open findings.

`dab34e89` is not part of those rounds. It only adds `hash2curve` 0.14.0 to `Cargo.lock` so the dev-dependency resolves against current main.
