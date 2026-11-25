<h1 align="center">rind-rand-core</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-rand-core)](https://crates.io/crates/rind-rand-core)
[![Documentation](https://img.shields.io/docsrs/rind-rand-core)](https://docs.rs/rind-rand-core/)

This crate provides `SystemRandom`, a [rand_core](https://github.com/rust-random/rand) 0.10 RNG drawing from [rind](https://github.com/kixel-ai/rind/)'s random source, a fork of [Graviola](https://github.com/ctz/graviola/), for crates generic over one, such as RustCrypto's.
Its version tracks rand_core's, so rind-rand-core 0.10 takes rand_core 0.10.

```toml
[dependencies]
rand_core = "0.10"
rind-rand-core = "0.10"
```

It draws as `rind::rand::fill` does and fails as it does, so it is a `TryCryptoRng`.
Wrap it in `rand_core::UnwrapErr` where a crate takes an infallible `CryptoRng`:

```rust
use rand_core::{TryRng, UnwrapErr};
use rind_rand_core::SystemRandom;

let mut nonce = [0u8; 16];
SystemRandom.try_fill_bytes(&mut nonce).unwrap();

// For a crate taking a `CryptoRng`, which panics if rind cannot draw.
let rng = UnwrapErr(SystemRandom);
```

## What rind cannot back

Nothing: rand_core defines traits and ships no RNG whose API this crate could fall short of.

## WebAssembly

It builds for `wasm32-wasip2` and `wasm32-unknown-unknown`, the browser, where
rind needs its JavaScript random source, `getrandom = { version = "0.4",
features = ["wasm_js"] }`.

License: Apache-2.0 OR ISC OR MIT-0
