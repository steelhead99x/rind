# [L] rind offers FROST threshold signatures

## Goal

A public `frost` module implements RFC 9591's two-round FROST for its Ed25519, ristretto255, and P-256 ciphersuites: a trusted dealer splits a signing key into shares, any threshold of participants commit and sign, and a coordinator aggregates their shares into one signature, identifying a participant whose share is invalid. A FROST(Ed25519, SHA-512) signature verifies with rind's existing `signature::verify::ED25519`.

## Plan

- Builds on the crate-internal ristretto255 in `rind/src/mid/ristretto255.rs` for its ciphersuite, adding the scalar and element operations FROST needs beyond its encoding, map, and multiplications, and on `mid::p256::hash_to_curve::hash_to_scalar`, RFC 9380's `hash_to_field`, which FROST(P-256)'s hashes use; Ed25519 and P-256 reuse rind's s2n-bignum arithmetic, and curve25519-dalek's and fiat-crypto's on armv7 and the portable backend. Nonce commitments are fixed-base multiplications; aggregation and share verification handle public data and may run variable time.
- API: one `&'static Suite` per ciphersuite; a wiped `SigningShare` and public `VerifyingShare`s with the group's `VerifyingKey`; `SigningNonces::commit(&share)` returns nonces and the `Commitments` to send, and `SigningNonces::sign(self, ..)` consumes them, so a nonce cannot sign twice; a `SigningPackage` binds the message to the commitments. Nonces are hedged with the share as RFC 9591 recommends, drawing the rest from the system's random source.
- Out of scope until a consumer asks: distributed key generation, which RFC 9591 leaves out; FROST(secp256k1) and its Taproot variant (which Bitcoin and Nostr projects use through `frost-secp256k1-tr`), which need secp256k1, an [aws-lc-rs extra on demand](/quest/m3/parity/aws-lc-extras.md); and FROST(Ed448), which nothing uses.
- Test against RFC 9591's Appendix E vectors (the cfrg/draft-irtf-cfrg-frost repository's `poc` JSON), differentially against the Zcash Foundation's `frost-ed25519`, `frost-ristretto255`, and `frost-p256` 3.x as dev-dependencies (aws-lc-rs has no FROST), and ctgrind on signing and dealing.
