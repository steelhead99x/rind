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
- Decided 2026-11-19 (owner): ✅ an empty HKDF `info` follows aws-lc-rs, which derives it with its service indicator unset (rejected: refusing it). The module cannot derive it, so a module-held HKDF key keeps a wiped copy in rind, used only for an empty `info`, and the README says so.
- Decided 2026-11-19 (owner): ✅ hold the `rind-fips` release; nothing is published. Until it is, a published `rind-aws-lc-rs` or `rind-rustls` cannot carry the optional `rind-fips` dependency.
- Under `fips`, `try_fips_mode()` fails, naming what still runs in rind, until every service the module approves runs in it; the commit that completes the routing flips it to `Ok(())`. Reporting `Ok` earlier claims operations the module's boundary does not hold.
- The rustls provider's first cut routes hashes, HMAC, TLS 1.3 HKDF, TLS 1.3 AES-GCM, QUIC, ECDH, ML-KEM and random through the module. Signature verification and signing, and the TLS 1.2 suites, are not in it yet, so `CryptoProvider::fips()` stays false until they are.

## Waiting

- Maintainer: AES-GCM sealing under a caller's nonce, which the module cannot do (it seals only under IVs it generates) and aws-lc-rs's FIPS build allows, unapproved. (a) Such a key stays in rind and is callable, opens included: nothing is refused and no approval is claimed, and `RandomizedNonceKey` and the TLS record keys are the approved path. (b) It opens in the module and seals in rind, which holds approved key material in two places. (c) It refuses the seal, which diverges from aws-lc-rs. Recommended: (a). Clear it by recording the choice here; the routing of those keys and the flip of `try_fips_mode()` follow.
- Maintainer: RSA private keys of an odd number of modulus bits, and PSS salts other than the hash's length, which the module cannot hold or produce. Keep refusing them, since the key cannot leave the module (public-key verification of any modulus or salt still works, in rind), or hold such a private key in rind, which puts approved and unapproved key material in two places. Recommended: keep the refusal, listed in the README.
- Maintainer: whether the TLS 1.2 AES-GCM suites report `fips()` once the module can seal TLS 1.2 records, as rustls's aws-lc-rs provider does. Clear it by recording the choice here.
- Maintainer: publishing `rind-fips` (held 2026-11-19). Clear it by publishing it or by deciding the `fips` features stay unpublished.
