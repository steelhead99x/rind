# [S] rind-openssl takes keys by pointer and exports private keys in OpenSSL's secure heap

## Goal

rind-openssl's key management accepts `OSSL_PARAM_OCTET_PTR` for the key
parameters it takes as `OSSL_PARAM_OCTET_STRING`, as OpenSSL's providers do
through `OSSL_PARAM_get_octet_string_ptr`, and exports private key material
through OpenSSL's secure heap, so `EVP_PKEY_todata` keeps an application's
secure-heap setting for rind's keys as it does for the default provider's.

## Plan

- Found by CodeRabbit's third pass on
  [kixel-ai/rind#1053](https://github.com/kixel-ai/rind/pull/1053); the
  maintainer took the split on 2026-11-25: a follow-up, since both sit in
  parameter and export code that X25519 and Ed25519 share, which
  [kixel-ai/rind#868](https://github.com/kixel-ai/rind/pull/868) also edits.
- `Param::octets` in `rind-openssl/src/params.rs` takes only
  `OSSL_PARAM_OCTET_STRING`, so `pub`, `seed`, `priv`, and `encoded-pub-key`
  given as `OSSL_PARAM_OCTET_PTR` are refused, for ML-KEM, ML-DSA, X25519,
  and Ed25519 alike. Read both forms, dereferencing the pointer form, and
  keep each caller's exact-length check after it.
- `pq_keymgmt::export` (and the X25519 and Ed25519 exports) passes `seed`
  and `priv` from ordinary Rust allocations. `OSSL_PARAM_dup`, which
  `EVP_PKEY_todata` uses, copies by where its source lives, so with the
  secure heap on, the copy sits in ordinary memory and is freed unwiped.
  Hand the callback private fields allocated with `CRYPTO_secure_malloc`,
  and wipe and free them after it returns, as the default provider does.
- Test both against the default provider: a key loaded by pointer, and an
  export with `CRYPTO_secure_malloc_init` on whose copy lands in the secure
  heap (`CRYPTO_secure_allocated`).

## Required

- [The NIST curves in rind's OpenSSL provider](/quest/m4/openssl-provider.md) - kixel-ai/rind#868's edits to the shared parameter and export code, which this builds on
