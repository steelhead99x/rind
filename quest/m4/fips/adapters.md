# [M] FIPS builds of rind-rustls and rind-aws-lc-rs

## Goal

rind-rustls and rind-aws-lc-rs accept their upstreams' `fips` feature and
back it with `rind-fips`, so a consumer that builds rustls or aws-lc-rs with
`fips` swaps to rind with no other change: `CryptoProvider::fips()` and
`try_fips_mode()` answer as aws-lc-rs's do.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- The adapter rule holds: the feature exists upstream, so it adds nothing.
  rind-aws-lc-rs's README stops listing `fips` as refused, and lists the
  aws-lc-rs FIPS functions rind's module cannot back.
- rind-rustls's FIPS provider offers what rustls's aws-lc-rs FIPS provider
  does: TLS 1.3 AES-GCM through the TLS IV unit, P-256 and P-384 ECDH,
  X25519MLKEM768 with ML-KEM inside the module and X25519 outside it, and
  ECDSA, RSA, Ed25519, and ML-DSA signatures. Each component's `fips()` is
  true exactly where aws-lc-rs's is.
- rind-fips has no `TlsRecordOpeningKey` (decided in
  [kixel-ai/rind#771](https://github.com/kixel-ai/rind/pull/771#issuecomment-6892740753)):
  rind-aws-lc-rs's FIPS build backs aws-lc-rs's by wrapping `aead::Key`.
- If rind-rustls's FIPS provider derives TLS 1.3's secrets through the
  module's HKDF, which needs a pseudorandom key the module takes in, register
  ACVP's TLS-v1.3 KDF in rind-acvp and answer it: `acvptool` drives it
  through `HKDF/<hash>/extract` and `HKDFExpandLabel/<hash>`, as the scope
  asked.
- Deno's FIPS build ([denoland/deno#36906](https://github.com/denoland/deno/pull/36906))
  swaps aws-lc-rs for its FIPS module through these same features, so it is
  the first test of the swap.
