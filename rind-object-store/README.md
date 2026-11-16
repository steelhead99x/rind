<h1 align="center">rind-object-store</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-object-store)](https://crates.io/crates/rind-object-store)
[![Documentation](https://img.shields.io/docsrs/rind-object-store)](https://docs.rs/rind-object-store/)

This crate provides a `CryptoProvider` for [object_store](https://github.com/apache/arrow-rs-object-store), backed by [rind](https://github.com/kixel-ai/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
It signs S3, Azure, and GCS requests.

Build object_store with its `aws-base`, `azure-base`, or `gcp-base` features rather than `aws`, `azure`, or `gcp`, which also compile aws-lc-rs.
Then hand the provider to each store's builder:

```rust,no_run
let store = object_store::gcp::GoogleCloudStorageBuilder::new()
    .with_bucket_name("bucket")
    .with_crypto_provider(rind_object_store::default_provider())
    .build()?;
```

It builds for `wasm32-wasip2` and `wasm32-unknown-unknown`, the browser, where
rind needs its JavaScript random source, `getrandom = { version = "0.4",
features = ["wasm_js"] }`. [PLATFORMS.md](https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md) lists what each adapter's
upstream needs there too, and why rind's constant-time checks do not cover wasm.

License: Apache-2.0 OR ISC OR MIT-0
