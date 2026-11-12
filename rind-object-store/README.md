<h1 align="center">rind-object-store</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/moq-dev/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-object-store)](https://crates.io/crates/rind-object-store)
[![Documentation](https://img.shields.io/docsrs/rind-object-store)](https://docs.rs/rind-object-store/)

This crate provides a `CryptoProvider` for [object_store](https://github.com/apache/arrow-rs-object-store), backed by [rind](https://github.com/moq-dev/rind/), a fork of [Graviola](https://github.com/ctz/graviola/).
It signs S3, Azure, and GCS requests.

Build object_store with its `aws-base`, `azure-base`, or `gcp-base` features rather than `aws`, `azure`, or `gcp`, which also compile aws-lc-rs.
Then hand the provider to each store's builder:

```rust,no_run
let store = object_store::gcp::GoogleCloudStorageBuilder::new()
    .with_bucket_name("bucket")
    .with_crypto_provider(rind_object_store::default_provider())
    .build()?;
```

object_store's own providers are `pub(crate)`, so this crate keeps `default_provider()`, which returns `Arc<dyn CryptoProvider>`.
Digests and HMAC are SHA-256, and signing is RS256, which is what S3, Azure, and GCS ask for. Any other algorithm returns `Error::NotSupported`.

License: Apache-2.0 OR ISC OR MIT-0
