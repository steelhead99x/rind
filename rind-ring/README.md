<h1 align="center">rind-ring</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-ring)](https://crates.io/crates/rind-ring)
[![Documentation](https://img.shields.io/docsrs/rind-ring)](https://docs.rs/rind-ring/)

This crate offers [ring](https://github.com/briansmith/ring) 0.17's API, name for name, backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
A crate on ring swaps it in by renaming its dependency, with no code
changes:

```toml
[dependencies]
ring = { package = "rind-ring", version = "0.17" }
```

Every ring feature is accepted. As in ring, `alloc` gates RSA, `std` the
errors' `std::error::Error` impls, and `wasm32_unknown_unknown_js` the
browser's random source (see [WebAssembly](#webassembly)); the rest change
nothing. Like ring, it builds without `std`, but always needs a global
allocator, as rind does, even without `alloc`.

The rename reaches only the crate that makes it. A binary moves every crate
in its tree on ring 0.17 to rind, including dependencies that name ring such
as rustls and quinn-proto on their `ring` features, by patching ring in its
workspace's root `Cargo.toml` and then running `cargo update -p ring`:

```toml
[patch.crates-io]
ring = { git = "https://github.com/kixel-ai/rind-patch" }
```

Cargo builds the crate named `ring` in
[rind-patch](https://github.com/kixel-ai/rind-patch), a small repository of
its own, which re-exports rind-ring and accepts every ring feature.
crates.io has the name, so that crate is never published. Its version, 0.17.999, meets every ring
0.17 requirement. Where the patch is not used, such as for an exact
requirement like `=0.17.14` or before the lockfile is updated, Cargo builds
crates.io's ring and only warns, so check that `cargo tree -i ring` prints
`ring v0.17.999` from rind-patch alone. A dependency on ring 0.16 or
older keeps it, and a library cannot patch for the binaries that use it,
since Cargo applies a patch only in the workspace that declares it.

rind-ring panics wherever ring panics, such as `pbkdf2::derive` on an
output over (2^32 - 1) hash outputs, so its signatures match ring's
exactly (maintainer, 2026-10-31). rind itself never panics on caller
input.

## What rind cannot back

These items are not offered, so code using them, in a patched dependency
too, fails to build:

- `aead::chacha20_poly1305_openssh`: rind refuses it, having no SSH consumer.
- `test`, `deprecated_test`, and `test_file!`: ring's test harness, which
  is no cryptography. `test::rand`'s fixed random sources could not work,
  since rind draws its own randomness.
- `signature::RsaEncoding::encode`: ring's hidden, deprecated internal
  method, which takes a type callers cannot name.

## Behaves differently

- Where ring takes a `rand::SecureRandom` to generate a key or sign,
  rind draws from the system random source itself, as
  `rand::SystemRandom`, the only `SecureRandom`, does.
- An Ed25519 public key of small order verifies no signature, where
  ring verifies some that nobody made on it.
- A secret or private key wipes its memory on drop, which ring never
  does; a public key on its own is not wiped.
- A `error::KeyRejected`'s `Display` gives rind's reason, not ring's
  name for it, which ring documents as changing between releases.
- An RSA key whose integers disagree is refused when it loads, as
  aws-lc-rs refuses it, where ring takes a wrong `d`, which it never uses,
  and finds a wrong `e` or CRT integer only when it signs.
- `rsa::KeyPair::from_components` takes private integers with leading
  zero bytes, as aws-lc-rs does, where ring refuses those wider than it
  expects: refusing them would branch on their secret first bytes.

## WebAssembly

rind-ring builds for `wasm32-wasip2`, where CI runs its tests under wasmtime,
and for `wasm32-unknown-unknown`, the browser, where its
`wasm32_unknown_unknown_js` feature takes the JavaScript random source, as
ring's does, and CI runs ring's own tests in Node. Neither needs the C compiler targeting wasm that ring needs.
rind's constant-time checks do not cover wasm; [PLATFORMS.md](https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md) says why.

License: Apache-2.0 OR ISC OR MIT-0
