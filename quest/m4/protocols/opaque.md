# [L] rind offers OPAQUE

## Goal

A public `opaque` module implements RFC 9807's OPAQUE-3DH in its two Argon2id configurations, over ristretto255 and over P-256: registration, login, the session key, and the export key. A server never sees the password, and a stolen record allows only an offline attack paced by Argon2id. WhatsApp's encrypted backups and `lldap` run OPAQUE today, through `opaque-ke`.

## Plan

- Builds on rind's `oprf` module (OPRF mode) and [Argon2id](/quest/m4/protocols/argon2.md); the 3DH key exchange, envelope, and key schedule are HKDF, HMAC, and Diffie-Hellman rind already has.
- API: one `&'static Suite` per configuration, its Argon2id parameters included; a wiped `ServerSetup` (OPRF seed and AKE key pair); each side's state a type that its next step consumes (`ClientRegistration`, `ClientLogin`, `ServerLogin`), so a step cannot run twice or out of order. Messages and records are fixed-size types with `from_bytes` and `as_bytes`. Server-side lookups of an unknown user return a fake response indistinguishable from a real one, as RFC 9807 requires.
- Test against RFC 9807's vectors (Appendix C, which `opaque-ke` carries as code), which stretch with the identity function, so only tests reach an identity stretch; differentially against `opaque-ke` with the same suite as a dev-dependency (aws-lc-rs has no OPAQUE), and ctgrind on both sides' secret paths.

## Required

- [Argon2id](/quest/m4/protocols/argon2.md) - the key stretching function
