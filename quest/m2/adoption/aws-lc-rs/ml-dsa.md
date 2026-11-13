# [S] ML-DSA in rind-aws-lc-rs

## Goal

rind-aws-lc-rs offers aws-lc-rs 1.x's ML-DSA items, backed by rind's: `signature::{ML_DSA_44, ML_DSA_65, ML_DSA_87}` and their `_SIGNING` algorithms, `PqdsaKeyPair`, and the other `Pqdsa*` types, behaving as aws-lc-rs's do. Its README and MIGRATING.md then list only what rind cannot back, and rustls's `aws_lc_rs` provider and rustls-webpki's `aws-lc-rs` feature build on it once rind-aws-lc-rs also has ML-KEM-1024.

## Plan

- Done, restored from fork main `f95af317`: the adapter's key pair holds an enum of the three parameter sets, verification maps onto `rind::signature::verify::ML_DSA_*`, and the tests cover aws-lc-rs's items. `to_pkcs8` and `to_pkcs8v1` fail for a key loaded without its seed. `from_raw_private_key` wraps an expanded key. README and MIGRATING.md list ML-DSA as offered.
- Still out: `PqdsaPrivateKey::as_raw_bytes` and `encoding::PqdsaPrivateKeyRaw`, which read the expanded key back. rind does not export that.
- rustls's `aws_lc_rs` provider still does not build: it names `tls_prf`, and rustls 0.23.46 also names `kem::ML_KEM_1024`. rustls-webpki's `aws-lc-rs` feature and rcgen's `aws_lc_rs` feature do build.

## Related

- [rustls provider parity](/quest/m3/parity/rustls.md) - rind-rustls's ML-DSA, on rind's own API
- [An aws-lc-rs patch shim](/quest/m2/adoption/aws-lc-rs/aws-lc-rs-patch.md) - leaves rustls's provider out of its fixture until rind-aws-lc-rs has ML-DSA and ML-KEM-1024
