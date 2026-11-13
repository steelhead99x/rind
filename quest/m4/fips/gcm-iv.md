# [M] AES-GCM with internally generated IVs

## Goal

rind's FIPS module seals AES-GCM only with IVs it generates, as IG C.H
requires for approved encryption: random 96-bit IVs from the DRBG (scenario
2), and a TLS 1.3 IV unit that owns the record sequence counter and refuses
to wrap (scenario 5). Opening keeps taking the peer's nonce.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- Match aws-lc-rs's FIPS-motivated types: `RandomizedNonceKey` over AES-GCM
  and `TlsRecordSealingKey`, `TlsRecordOpeningKey`, and `TlsProtocolId`.
  MIGRATING.md maps the TLS types to plain `Key`, "rind has no FIPS mode
  whose nonce rules they check", and rind-aws-lc-rs already offers all four
  over it (`rind-aws-lc-rs/src/aead.rs`, `src/aead/tls.rs`), so start from
  those rather than from nothing. `rind`'s own `RandomizedNonceKey` stays
  XChaCha20-Poly1305, which is not approved.
- TLS 1.2's explicit-nonce scenario 1 waits for a consumer: rind-rustls's
  FIPS build needs only TLS 1.3, as SP 800-52r2 allows.
- ACVP's AES-GCM sets with `ivGen: internal` test both; random-IV sealing
  draws from the module's DRBG (`rind/src/fips_rng.rs`), about 3.4 µs a
  draw on x86_64, which a random IV pays per seal.
