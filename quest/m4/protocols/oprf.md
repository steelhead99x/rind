# [L] rind offers OPRFs

## Goal

A public `oprf` module implements RFC 9497's OPRF and VOPRF modes for its P-256, P-384, P-521, and ristretto255 suites: the client blinds an input and finalizes the server's evaluation into the PRF output, and a verifiable server proves, for one input or a batch, that it used the key it published. Privacy Pass's privately verifiable token (RFC 9578, type `0x0001`, VOPRF(P-384, SHA-384)), its batched ristretto255 token (draft-ietf-privacypass-batched-tokens, type `0x0005`), and [OPAQUE](/quest/m4/protocols/opaque.md) run on it.

## Plan

- Builds on `mid`'s RFC 9380 hashes to the NIST curves and their scalars (`mid::p256::hash_to_curve::{hash_to_curve, hash_to_scalar}`, and P-384's and P-521's) and `expand_message_xmd`, and on the crate-internal ristretto255 in `rind/src/mid/ristretto255.rs`, whose `rfc9497_oprf` test already runs this suite's OPRF-mode vectors; the NIST curves' arithmetic is s2n-bignum's, and fiat-crypto's on armv7 and the portable backend, both already in rind. The DLEQ proof's verification is public and may run variable time; everything holding the client's input, blind, or the server's key runs in constant time.
- API: one `&'static Suite` per suite; the modes are separate types (an `oprf::ServerKey` and a `voprf::ServerKey`, each wiped, from `generate` or RFC 9497's `DeriveKeyPair`), so an unverified evaluation cannot reach a verifying client. The client's `blind(suite, input)` returns the `BlindedElement` to send and a `Blind` that `finalize(self, ..)` consumes, the VOPRF one taking the `Proof` and server public key; outputs are fixed-size per suite. POPRF is left out until its first consumer, the public-metadata Privacy Pass token (draft-ietf-privacypass-public-metadata-issuance), is final.
- Linking ristretto255 brings its s2n-bignum field and point routines into the release build for the first time, so `admin/prove bytes` starts checking them and ALGORITHMS.md's inventory needs their rows, as its tables need ristretto255's.
- Test against RFC 9497's Appendix A vectors (the cfrg/draft-irtf-cfrg-voprf repository's `allVectors.json`), differentially against the `voprf` crate as a dev-dependency (aws-lc-rs has no OPRF; AWS-LC's trust tokens are a different protocol), and ctgrind on blinding, evaluation, and finalization.

## Required

None. ristretto255 is in `rind/src/mid/ristretto255.rs`, and the NIST hashes are in `mid::p256::hash_to_curve`, `mid::p384::hash_to_curve`, and `mid::p521::hash_to_curve`.
