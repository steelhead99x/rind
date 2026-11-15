# [M] Argon2id in rind-dart and rind_cryptography

## Goal

rind-dart exposes rind's `argon2` module, and
[rind_cryptography](/rind-dart/cryptography/README.md) backs the
`cryptography` package's `Argon2id` with it, rather than throwing
`UnsupportedError('rind has no Argon2id')`.

## Plan

- Kept (maintainer, 2026-11-13).
- Runtime parameters (maintainer, 2026-11-13): ✅ `Params` buildable from
  memory, passes, and lanes, validated and bounded when built, with `derive`
  filling a `&mut [u8]`, as one API for Rust and FFI callers (rejected: an
  FFI-only entry point in rind-dart).
- `cryptography`'s `Argon2id` takes `memory`, `parallelism`, `iterations`,
  and `hashLength` at runtime. Today `rind::argon2::Params::new` takes memory,
  passes, and lanes at runtime, but `derive` and `verify` take a `[u8; N]`
  whose length is fixed at compile time; the decision above changes both to
  slices, so the FFI passes the package's choices through.
- Its `deriveKey` also takes an optional secret and associated data, which
  rind's `derive` does not; recommended: throw `UnsupportedError` when either
  is non-empty, as the adapter does for other unsupported parameters.
- Its tests run the package's Argon2id tests, which
  [compat/cryptography.txt](/rind-dart/cryptography/compat/cryptography.txt)
  does not skip today, so check they reach rind once it backs them.
- It needs a rind-dart release before rind_cryptography can depend on it.

