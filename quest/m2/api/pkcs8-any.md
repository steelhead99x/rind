# [M] A PKCS#8 key of unknown type loads in one call

## Goal

A caller holding a PKCS#8 private key of unknown algorithm, such as a TLS server reading its key file, loads it with one rind call that reads the algorithm identifier once and returns a signing key. The adapters stop trying each key type in turn.

## Plan

Found by the 2026-11-12 audit. rind has no such call, so two adapters each wrote a chain of attempts: `rind-rustls/src/sign.rs`'s `any_supported_type` tries RSA, three ECDSA curves, and Ed25519 in turn and joins every refusal into one message, and `rind-rcgen/src/lib.rs:328` tries four algorithms and reports only that none parsed. Each failed attempt parses the whole document again, and neither can say "this is an X25519 key, which cannot sign".

- Parse the `AlgorithmIdentifier` once and dispatch on its OID and, for ECDSA, its curve. An OID rind does not know is an error that says so.
- The key is hostile input: no panic, and the cost of a refusal is bounded by the one parse.
- What it returns depends on the shape [the API takes](/quest/m2/api/shape.md): an enum over the key pair types is the audit's recommendation, since each adapter wraps the key in its own trait anyway. Settle it once the spike has moved these types.
- Each key type accepts exactly what its own `from_pkcs8` accepts today.
- It is additive, so it does not hold rind 0.4.
- MIGRATING.md gains the row, and both adapters move to the call. rind-rustls's `any_supported_type` takes a `PrivateKeyDer` (`rind-rustls/src/sign.rs:17`), which is PKCS#8, PKCS#1 RSA, or SEC1 ECDSA: it uses the call for PKCS#8 alone and keeps its PKCS#1 and SEC1 paths, with the tests that load each (`sign.rs:363-395`). rind-jsonwebtoken is told its algorithm by the caller and needs none.

## Required

- [The API takes one shape](/quest/m2/api/shape.md) - the key pair types this returns, in their final modules
