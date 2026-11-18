# The API steers callers away from misuse

## Goal

rind's public API steers callers away from the misuse and wasted work a 2026-11-08 security and performance audit found: chained HKDF expands written by hand, public keys recomputed on every call, caller-chosen AES-CBC IVs, and hazards nothing documents, and a startup CPU check every caller must make although it can no longer fail. Its modules also take one shape, so a caller who has learned one key type can guess the next one's constructors and accessors. Adapters change only to drop the workarounds they carry today.

## Plan

The audit checked every module of `rind` against AGENTS.md's rules and found nothing high-severity, and no panic reachable from public input. Decided with the maintainer on 2026-11-08:

- Scope: the goal above ✅ (rejected: non-breaking changes only, docs only).
- Additive quests: HKDF chaining, cached agreement keys, and a hygiene and docs pass ✅, all three.
- Breaking changes: a typed AES-CBC IV, and deleting the runtime CPU check that can no longer fail ✅. Rejected, so don't raise them again without new evidence:
  - Replacing `SharedSecret`'s `AsRef<[u8]>` with a named accessor. Documenting HKDF in the examples gets most of the value, and the rename would churn every TLS and HPKE caller.
  - Moving GCM's 32- and 64-bit tags under a legacy name. WebCrypto requires them, and `TagLength`'s docs already warn about them.
  - Collapsing `constant_time::verify`'s `WrongLength` and `NotEqual` into one error. Matching only `NotEqual` is a contrived misuse, and every caller uses `?`.
  - Pinning the key's hash in `verify_digest` and `sign_digest`, as aws-lc-rs does (maintainer, 2026-11-09: ✅ leave it as documented; rejected: refuse a mismatched digest in 0.4). The digest's hash replacing the algorithm's is deliberate and documented, WebCrypto permits any hash with any curve, and the adapters that promise aws-lc-rs's or ring's behaviour add the check themselves.
- Milestone: m2 ✅ (rejected: m1, m3). None of this blocks MoQ.
- Releases, decided with the maintainer on 2026-11-09: one rind 0.4 that carries all three breaking changes, and a MoQ-side PR ready before the adapter patch releases publish ✅ (rejected: the 0.4 quest alone, accepting that MoQ's build breaks until fixed; leaving both to release-plz). The third is the cached agreement keys, whose `public_key()` returns a borrow in [kixel-ai/rind#529](https://github.com/kixel-ai/rind/pull/529) though this epic planned them as additive. [rind 0.4 ships once](/quest/m2/api/release-0.4.md) holds the release.
- Decided 2026-11-12 (maintainer, /quest-audit), after a second audit that read the modules side by side instead of one at a time. It found no misuse hazard, but the modules disagree with each other, and three adapters each carry their own HKDF-Expand:
  - 0.4 waits for every breaking change planned by then ✅ (rejected: only ML-KEM and wiping, with the API fixes in 0.5; ship the first three as planned). [Its quest](/quest/m2/api/release-0.4.md) lists them.
  - Shape: spike per-algorithm modules as a draft PR for the maintainer to accept or reject, and fold the naming fixes into whichever shape wins ✅ (rejected: keep today's modules and fix names only; commit to per-algorithm modules without a spike). The maintainer accepted the spike in [kixel-ai/rind#781](https://github.com/kixel-ai/rind/pull/781) on 2026-11-15: `ecdsa`, `ed25519`, `ml_dsa`, and `rsa` modules, each with `KeyPair` and `PublicKey`, and no shared runtime verifier ✅ (rejected: keep `signature` and fix names only). The same PR gave `kem`'s public key, SLH-DSA, and Argon2id, which landed meanwhile, the same shape: a borrowed `DecapsulationKey::public_key()`, an `slh_dsa` module shaped as `ml_dsa`, and `argon2::Secret` shaped as `pbkdf2::Secret`. Its leftovers are the bindings' own APIs, in [pyrind takes rind 0.4's shape](/quest/m2/api/pyrind-shape.md) and [rind for Dart takes rind 0.4's shape](/quest/m2/api/rind-dart-shape.md).
  - A record nonce: add `Nonce::from_sequence` ✅ (rejected: a typed key that owns the counter; leave MIGRATING.md's "no `NonceSequence`" as decided).
- Dropped as not worth a quest:
  - Fixed buffers sized for RSA (`PublicKey` 3584 B, `encoding::Pkcs8` 4.8 KB, `Signature` 1032 B). They sit on no hot path, and fixed capacity is ARCHITECTURE.md's design.
  - `RandomizedNonceKey`'s `getrandom` call per seal. Its only consumer seals rustls tickets.
  - The per-packet copy in rind-str0m's SRTP. aws-lc-rs's ciphers are in place too, and MoQ doesn't use SRTP.
  - Taking `agree(&PublicKey)` instead of bytes. TLS parses each peer key once per handshake anyway.
  - A streaming `hmac::Context::verify`. It has no consumer; the hygiene quest documents signing and then calling `constant_time::verify`.
- Owned elsewhere: storing and loading ML-KEM decapsulation keys is in [HPKE's post-quantum KEMs](/quest/m4/protocols/hpke-pq.md).
