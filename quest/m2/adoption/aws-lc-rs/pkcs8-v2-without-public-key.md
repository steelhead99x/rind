# [S] rind loads a PKCS#8 v2 key without its public key, as aws-lc-rs does

## Goal

rind's PKCS#8 decoder takes a v2 (RFC 5958) document whose optional `publicKey` is absent, as AWS-LC does, so rind-aws-lc-rs's `Ed25519KeyPair::from_pkcs8` and `from_pkcs8_maybe_unchecked` load the two vectors in aws-lc-rs's `ed25519_from_pkcs8_tests.txt` it refuses today. rind-aws-lc-rs's README then drops "or is missing" from its "Behaves differently" entry, and `rind-aws-lc-rs/tests/aws-lc-rs/ed25519_tests.rs` drops its `V2_WITHOUT_PUBLIC_KEY` skip.

## Plan

- The refusal is `rind/src/high/pkcs8.rs`'s `Key::decode`, which pairs v2 with a present public key. RFC 5958 makes the field optional in v2, and AGENTS.md says to follow aws-lc-rs on what to accept.
- `Key::decode` serves X25519, ECDSA (through SEC1), Ed25519, ML-DSA, and RSA. Check each key type against aws-lc-rs before accepting it, through `fuzz::keys` and a differential test of a v2 document without the field, since AWS-LC's rule may differ by key type.
- rind-ring reads Ed25519 PKCS#8 with its own parser, which refuses the document as ring does, so it is unaffected; its tests confirm that.
