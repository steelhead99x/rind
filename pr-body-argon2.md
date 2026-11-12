feat(argon2): add Argon2id

## Problem

OPAQUE needs the Argon2id stretch RFC 9807 recommends, and rind has no password hash harder than PBKDF2. Argon2id is specified in RFC 9106.

## Approach

A public `argon2` module derives and verifies a key from a password. `Params` holds memory, passes, and lanes, with RFC 9106's two recommended sets as `RECOMMENDED` (one pass, four lanes, 2 GiB) and `RECOMMENDED_LOW_MEMORY` (three passes, four lanes, 64 MiB). Values below the RFC minimums are refused. The memory matrix is one allocation; a size the address space cannot hold, or an allocation the platform refuses, is `Error::OutOfRange`. `verify` allocates its tag fallibly. The docs say overcommit can still kill the process.

BLAKE2b (RFC 7693) and the BlaMka permutation are rind's. x86_64 selects AVX-512F, then AVX2, then SSSE3, then the scalar permutation. aarch64 selects NEON. The choice is made once per derivation. The password and the matrix are wiped under the `wipe` feature.

The data-dependent half indexes memory by a word of the previous block. That is the constant-time exception recorded in `AGENTS.md`, which this branch edits, as agreed on 2026-11-07. The data-independent first half addresses memory only from the pass, lane, and slice, which are public. The index arithmetic does not branch on the password; only the resulting lane and block are declassified. ctgrind covers BLAKE2b and that first half.

`quest/m4/protocols/argon2.md` stays. The constant-time exception it asked to record is the `AGENTS.md` edit above.

## Impact

- New `argon2::{Params, Secret, RECOMMENDED, RECOMMENDED_LOW_MEMORY}`. `Secret::derive` and `Secret::verify` take the parameters, salt, optional secret, associated data, and output.
- `Error::OutOfRange`, on the non-exhaustive `Error`, for a parameter outside RFC 9106's range or a memory size this call cannot allocate.

## Alternatives

- HACL*'s BLAKE2b hashes; it does not implement BlaMka. The hash is a few kilobytes beside the fill, so it was not used for the permutation.
- RustCrypto's `argon2` is the differential oracle. Its AVX2 fill was slower than the AVX-512F port on the machine where the fills were compared.
- libsodium's tree, checked out without a `configure` script, was not built. The reference AVX-512F fill, which that family comes from, was the fastest build that did run.

## Follow-ups

- A proof of the BlaMka permutation.
- libsodium was not measured as its own binary.

## Testing

Head `b538aa8de01a4ef66777726b7a88132ea6586fc7`.

`nix develop --command just ci upstream/main` exited 0. That run includes the Argon2 unit tests, `crosschecks` `argon2id::matches_rustcrypto`, `zeroing` `argon2`, `heap_scratch` `argon2`, the doctest, clippy, `admin/ct-vartime` (the public divisions in `layout` and `divisor` are allowlisted), `admin/testing`, and `cargo deny`.

The differential on its own:

```
test argon2id::matches_rustcrypto ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 71 filtered out; finished in 0.29s
```

`nix develop .#ctgrind --command admin/ctgrind unit --release -- argon2::tests::secret_password`:

```
test high::argon2::tests::secret_password ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 649 filtered out; finished in 0.12s
ERROR SUMMARY: 0 errors from 0 contexts (suppressed: 0 from 0)
```

Release fill, one lane, measured on the machine that wrote the fills (Intel Xeon, milliseconds per hash). Not re-measured on this host:

| memory | passes | rind AVX-512F | rind scalar | RustCrypto AVX2 | phc-argon2 AVX-512F |
| --- | --- | --- | --- | --- | --- |
| 1 MiB | 3 | 0.41 | 1.20 | 0.89 | 0.43 |
| 16 MiB | 1 | 4.05 | 8.81 | 5.69 | 4.12 |
| 64 MiB | 1 | 28.3 | 45.7 | 41.6 | 30.1 |

## Review

Rounds by a model from a second vendor, different from the one that wrote the code. The SHAs are this branch's commits of those changes. The head of this branch is the commit round 2 reviewed.

| Round | Head reviewed | Base | Score | Findings |
| --- | --- | --- | --- | --- |
| 1 (low effort) | `722daf96` | f5f82bca | 8/10 | none |
| 1 (deep) | `722daf96` | f5f82bca | 7/10 | 1 high, 5 medium, 4 low |
| 2 | `b538aa8d` | f5f82bca | 9/10 | none |

The deep round's high finding was a fuzz oracle that treated a truncated tag as a prefix of the full one. All ten findings were fixed (AVX2, SSSE3, and NEON memory fills came in the same pass), and round 2 confirmed each fix with no new findings.
