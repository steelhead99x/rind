# [M] AES-GCM with internally generated IVs

## Goal

rind's FIPS module seals AES-GCM only with IVs it generates, as IG C.H
requires for approved encryption: random 96-bit IVs from the DRBG (scenario
2), and a TLS 1.3 IV unit that owns the record sequence counter and refuses
to wrap (scenario 5). Opening keeps taking the peer's nonce.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- ✅ Match aws-lc-rs's FIPS-motivated types, on `rind-fips`: `RandomizedNonceKey`
  over AES-GCM draws a 96-bit IV inside the module (IG C.H scenario 2), and
  `TlsRecordSealingKey`, `TlsRecordOpeningKey`, and `TlsProtocolId` are the
  TLS 1.3 record keys. The sealing key owns the sequence counter and refuses
  a repeat, a step backward, or `u64::MAX` (scenario 5). Opening takes the
  peer's nonce. `rind`'s own `RandomizedNonceKey` stays XChaCha20-Poly1305.
- TLS 1.2's explicit-nonce scenario 1 waits for a consumer: rind-rustls's
  FIPS build needs only TLS 1.3, as SP 800-52r2 allows. `TlsProtocolId::TLS12`
  is refused.
- ✅ ACVP's AES-GCM sets with `ivGen: internal` and `ivGenMode: 8.2.2` are
  answered. The wrapper draws the IV from `rind/src/fips_rng.rs` and appends
  it after the tag, which is what `acvptool` reads. The sample files have no
  internal group; `admin/acvp` runs a synthetic one and checks each reply
  opens. The TLS counter is not an `ivGen` mode.
