# [S] ML-DSA context strings

## Goal

rind's `ml_dsa` API signs and verifies with a FIPS 204 context string, and
rind-openssl takes OpenSSL's `context-string` parameter instead of refusing
it with an `unsupported by rind` error.

## Plan

Kept on 2026-11-25 when the maintainer settled [kixel-ai/rind#1053](https://github.com/kixel-ai/rind/pull/1053)'s follow-ups.

- The mid layer already signs and verifies with any context; only the
  public API and the provider fix it to the empty one, which is what TLS and
  X.509 use.
- A consumer to build for: LAMPS's composite ML-DSA signatures
  (draft-ietf-lamps-pq-composite-sigs) sign their ML-DSA component with a
  context, as may a protocol that separates domains so. None of rind's has
  asked yet; start this once one does.
- API options, none of which adds a `sign_with_context`:
  - Breaking: `KeyPair::sign(context, message)` and
    `PublicKey::verify(context, message, signature)`, so every caller passes
    `&[]` for pure ML-DSA.
  - A handle: `KeyPair::signer(context)?` and `PublicKey::verifier(context)?`,
    each refusing a context over 255 bytes once, with `sign(message)` and
    `verify(message, signature)` on it; `KeyPair::sign` stays as the empty
    context's. Recommended: no caller changes, and the length check happens
    where the context is given.
- Decided 2026-11-25 (maintainer): ✅ the breaking shape, `KeyPair::sign(context, message)` and
  `PublicKey::verify(context, message, signature)`, one way to sign (rejected: the
  `signer(context)` / `verifier(context)` handle, which keeps a second way beside
  `KeyPair::sign`). It lands in a breaking release with a MIGRATING.md entry.
- rind-openssl's `set_params` then keeps the context on the signing context,
  and `sh/openssl.sh` stops leaving out the `hexcontext-string` stanzas.

