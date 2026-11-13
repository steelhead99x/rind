# [XS] An AEAD nonce is built from an IV and a sequence number

## Goal

`aead::Nonce::from_sequence(iv, seq)` builds the nonce TLS 1.3, QUIC, and HPKE all use, the 12-byte IV with a 64-bit sequence number XORed into its last eight bytes, so no caller of rind writes that XOR by hand.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ add `Nonce::from_sequence(iv: &[u8; 12], seq: u64) -> Nonce` (rejected: a typed key that owns the counter and refuses to reuse one; leave it as decided).

This reopens a decision. MIGRATING.md maps aws-lc-rs's `NonceSequence` and its counters to "`Key`, given a `Nonce` per call from a sequence number the protocol keeps", and that stands: the protocol still keeps the counter, and rind adds no `NonceSequence`. What it leaves each protocol to write is the XOR, around `Nonce::assume_unique_for_key` (`rind/src/aead.rs:410`). A wrong byte order there reuses no nonce and fails no test until it meets another implementation.

The evidence is thinner than the interview said, so weigh it before starting. The workspace has one hand-written copy, in HPKE's `step` (`rind/src/high/hpke.rs:598-604`). rind-rustls does not write it: `rind-rustls/src/aead.rs`'s `nonce(iv, seq)` and `rind-rustls/src/quic.rs:74` call rustls's own `Nonce::new`. rind-dimpl and rind-openmls are handed whole nonces. So today this serves HPKE and any consumer that builds TLS, QUIC, or MLS records on rind without rustls.

- The sequence number is big-endian in the last eight bytes, as RFC 8446 section 5.3 and RFC 9180 section 5.2 both specify.
- HPKE calls it and deletes its loop. rind-rustls keeps rustls's helper, which its upstream provider uses too.
- Its documentation says what the caller still promises. `Nonce` already says each value seals once under a key, and here that means a sequence number is used once under an IV and key: the counter never repeats, wraps, or starts over while the key lives. The constructor cannot check that, so it says so where the counter is handed in, and HPKE keeps refusing to seal once its counter would wrap.
- Test it against RFC 9180's test vectors, which give the nonce for each sequence number.
- It is additive, so it does not hold rind 0.4. MIGRATING.md's `NonceSequence` row names it.
