# [L] The NIST curves in rind's OpenSSL provider

## Goal

rind-openssl, the OpenSSL 3 provider that already backs X25519 and Ed25519,
also backs ECDSA and ECDH on the NIST curves where rind is faster than
OpenSSL's default provider (on an i7-8700: P-384 about 4x, and P-521), so a
Node, Python, Ruby, or nginx deployment that loads it gets them with no code
change.

## Plan

Planned by the maintainer on 2026-11-04 in m4. The provider, its documented
`openssl.cnf`, and its tests landed for X25519 and Ed25519 in
[kixel-ai/rind#658](https://github.com/kixel-ai/rind/pull/658); this is the rest.

- OpenSSL gives every curve one `EC` key type and one `ECDSA` and `ECDH`
  algorithm each, so a provider that registers them gets every EC key on any
  curve once the configuration prefers it. rind backs P-256, P-384, and P-521
  only, and must refuse every other curve (secp256k1, Brainpool, explicit
  parameters) rather than fall back, as `AGENTS.md` requires.
- `EVP_DigestSign` and `EVP_DigestVerify`, which TLS and X.509 use, hand the
  provider the message and a digest name, which rind's message API covers
  where the digest is the one rind pairs with the curve. `EVP_PKEY_sign` hands
  it a digest the caller made, which rind's API does not take.
- rind verifies SHA-256, SHA-384, and SHA-512 on each curve (such as
  `ECDSA_P384_SHA256_ASN1`) but signs only with the curve's own digest, so
  under `ec = 1` an `EVP_DigestSign` with another, such as P-384 with
  SHA-256, fails with rind's unsupported error rather than falling back, and
  the README lists it. A deployment that signs so keeps `ec` off.
  Recommended: add unpaired signing to rind only once a consumer needs it.
- Register only what measures faster, on `openssl speed` and on Node and
  Python workloads, and test it as the X25519 and Ed25519 work does:
  differentially against the default provider, OpenSSL's `evp_test` on its
  ECDSA and ECDH data through `sh/openssl.sh`, the `openssl` fuzz target, and
  ctgrind.
- Decided 2026-11-11 (maintainer, /quest-unblock): rind-openssl always
  wipes the keys it holds and the `OSSL_PARAM` buffers it fills with key
  material (rejected: a build flag off by default; wiping nothing).
  `AGENTS.md` leaves other scratch unwiped because safe Rust cannot read
  freed memory; that reason does not cover these buffers. They are heap
  scratch derived from a private key, and the provider's heap is the host
  process's, which C code reads. OpenSSL's own providers cleanse keys, so
  anything less is a regression for whoever switches.
- Decided 2026-11-12 (maintainer, /quest-unblock): the provider takes
  OpenSSL's `EC` key type for P-256, P-384, and P-521 only when its
  configuration section opts in with `ec = 1`. Keys on other curves then fail
  with rind's error, `EVP_DigestSign` and `EVP_DigestVerify` run on rind's
  message API, and `EVP_PKEY_sign` over a bare digest fails as unsupported
  (rejected: also add ECDSA over a caller's digest to rind, as aws-lc-rs's
  `EcdsaKeyPair::sign_digest`; register `EC` always, breaking secp256k1 and
  Brainpool for every deployment that loads rind; never, deleting this
  quest). It needs no change to rind's API and fails loudly rather than
  falling back.
