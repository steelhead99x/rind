<h1 align="center">rind-rustls</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-rustls)](https://crates.io/crates/rind-rustls)
[![Documentation](https://img.shields.io/docsrs/rind-rustls)](https://docs.rs/rind-rustls/)

This crate provides an integration between [rustls](https://github.com/rustls/rustls) and [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).

Use it like:

```rust
rind_rustls::default_provider().install_default().unwrap();
```

And then use rustls as normal.

Its API is rustls's `crypto::aws_lc_rs` provider's, item for item, so
swapping one for the other changes no other code. rind cannot back yet:

- `kx_group::MLKEM1024`, which `ALL_KX_GROUPS` leaves out.
- ML-DSA: `default_provider()` neither verifies nor signs with it.

Where it behaves differently:

- `default_provider()` puts ChaCha20-Poly1305 first on a CPU where rind runs
  AES without CPU instructions, for speed.
- `DEFAULT_CIPHER_SUITES` and `ALL_CIPHER_SUITES` list AES-128-GCM before
  AES-256-GCM, for speed.
- `hpke`'s suites are `&dyn Hpke`, not upstream's `&HpkeAwsLcRs<..>`.
- `hpke`'s NIST suites refuse a compressed public key, which RFC 9180 does
  not define, where upstream seals to one a message no recipient opens.
- `hpke`'s NIST suites refuse an X9.62 hybrid point (`0x06`/`0x07`) as a
  public or encapsulated key, as rind does everywhere; upstream takes one.
- `Ticketer` seals tickets with XChaCha20-Poly1305, where upstream's uses
  RFC 5077's AES-256-CBC and HMAC-SHA256.

License: Apache-2.0 OR ISC OR MIT-0
