<h1 align="center">rind-jsonwebtoken</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-jsonwebtoken)](https://crates.io/crates/rind-jsonwebtoken)
[![Documentation](https://img.shields.io/docsrs/rind-jsonwebtoken)](https://docs.rs/rind-jsonwebtoken/)

This crate provides an integration between [jsonwebtoken](https://github.com/Keats/jsonwebtoken) and [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

Use it like:

```rust
rind_jsonwebtoken::DEFAULT_PROVIDER.install_default().unwrap();
```

And then use jsonwebtoken as normal.
Its API is `jsonwebtoken::crypto::aws_lc`'s, so swapping one for the other changes no other code.
It signs and verifies HS256/384/512, ES256/384, RS256/384/512, PS256/384/512, and EdDSA, and implements the key utilities jsonwebtoken needs for JWKs.

License: Apache-2.0 OR ISC OR MIT-0
