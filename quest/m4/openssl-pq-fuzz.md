# [S] Fuzz rind-openssl's ML-KEM and ML-DSA

## Goal

`fuzz::openssl` drives rind-openssl's ML-KEM and ML-DSA key management, KEM,
and signature dispatch tables as it does X25519's and Ed25519's: parameter
arrays of any names, types, and sizes, and output buffers of any length,
with every answer matching rind's own `kem` and `ml_dsa` API, and every
error reaching OpenSSL's core with a known reason.

## Plan

- Follow-up from the PR that registered them, which left the target alone
  because [the NIST curves](/quest/m4/openssl-provider.md)'s PR,
  [kixel-ai/rind#868](https://github.com/kixel-ai/rind/pull/868), rewrites
  it; extend that version.
- Cover import with seed, expanded, and public forms that disagree, which
  must give a key that fails each use; generation from a `seed`; and
  encapsulation, decapsulation, signing, and verification with the
  parameters rind refuses (`ikme`, `context-string`, `deterministic`,
  `test-entropy`, `mu`, `message-encoding`).

## Required

- [The NIST curves in rind's OpenSSL provider](/quest/m4/openssl-provider.md) - its rewrite of the fuzz target, which this extends
