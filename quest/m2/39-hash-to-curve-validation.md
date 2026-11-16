# [L] Hash-to-curve validation

## Goal

Secret OPRF inputs are timed, the identity hash boundary is tested through the public API, and shared helpers are not copied across curves.

## Plan

Difficulty: 7/10 (estimate).

Fork PR #39, head `035092e6`. Score 7/10. Upstream twin #791; fork #112 mirrors it. A partial diff is saved as `forkpr-39-partial-grok.diff`. Discard the local merge `70c65b04`.

Mediums:
- Time every secret OPRF input: the server key, `blind_evaluate`, the VOPRF proof and `Blind::new`.
- Add a ristretto255 identity-hash boundary test.
- The identity regression calls internal helpers; use the public API.

Lows:
- ctgrind marks a key that never reaches the arithmetic.
- A test-only argument was added to the shipped `nist_group!` macro.
- The wasm gate skips the empty-DST checks.
- A TESTING.md row is wrong.
- Helpers are copied across three curves.

Also needs fork fixes `6b27ab63` and `9c9e33ef`, which the one update will bring.
