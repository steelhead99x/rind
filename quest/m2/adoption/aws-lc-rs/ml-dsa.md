# [S] ML-DSA in rind-aws-lc-rs

## Goal

rind-aws-lc-rs offers aws-lc-rs 1.x's ML-DSA items, backed by rind's: `signature::{ML_DSA_44, ML_DSA_65, ML_DSA_87}` and their `_SIGNING` algorithms, `PqdsaKeyPair`, and the other `Pqdsa*` types, behaving as aws-lc-rs's do. Its README and MIGRATING.md then list only what rind cannot back, and rustls's `aws_lc_rs` provider and rustls-webpki's `aws-lc-rs` feature build on it once rind-aws-lc-rs also has ML-KEM-1024.

## Plan

- aws-lc-rs picks the parameter set at run time, through a `&'static PqdsaSigningAlgorithm`, where rind's `signature::sign::MlDsaKeyPair<P>` takes it as a type, so the adapter's key pair holds an enum of the three. Verification maps onto `rind::signature::verify::ML_DSA_*` through the adapter's existing `ParsedPublicKey` and `UnparsedPublicKey`.
- aws-lc-rs's `to_pkcs8` and `to_pkcs8v1` fail for a key loaded without its seed, where rind's `to_pkcs8` emits the expanded form; the adapter returns aws-lc-rs's error there. `from_raw_private_key` can wrap the expanded key in the PKCS#8 form rind loads. `PqdsaPrivateKey::as_raw_bytes`, which reads the expanded key back, has no rind counterpart and stays in the README's list.
- Test each item against aws-lc-rs, as the adapter's other algorithms are.

## Related

- [rustls provider parity](/quest/m3/parity/rustls.md) - rind-rustls's ML-DSA, on rind's own API
- [An aws-lc-rs patch shim](/quest/m2/adoption/aws-lc-rs/aws-lc-rs-patch.md) - leaves rustls's provider out of its fixture until rind-aws-lc-rs has ML-DSA and ML-KEM-1024
