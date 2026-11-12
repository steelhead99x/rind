# [L] HOL Light specs of ChaCha20-Poly1305 equal the Lean ones

## Goal

HOL Light specs of ChaCha20, Poly1305, and the RFC 8439 AEAD, in s2n-bignum's style, are proven equal to `proofs/Rind/Spec.lean`'s, as `Rind/S2nSha256.lean` does for SHA-256, so HOL Light proofs of aws-lc's routines on x86_64 and aarch64 carry over to the Lean glue.

## Plan

- Write the specs against RFC 8439, checked on its test vectors in HOL Light as `Rind/ChaCha20Poly1305Test.lean` checks the Lean ones.
- [aarch64's quest](/quest/m4/verified/chacha20-poly1305-aarch64.md) and the armv7 assembly quest use them too.
