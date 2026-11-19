# [S] dimpl checks signatures for every provider

## Goal

dimpl runs its RFC 8446 §4.4.3 check (a CertificateVerify's scheme matches
the certificate's curve) for every provider, not only behind its internal
`_crypto-common` feature, and `rind-dimpl` moves to the dimpl release that
carries it without enabling that feature. Reported as
[algesten/dimpl#208](https://github.com/algesten/dimpl/issues/208).

## Plan

Planned by the maintainer on 2026-10-28.
[kixelated/rind#16](https://github.com/kixelated/rind/pull/16) enabled the
feature in `rind-dimpl` to keep the check. Once released, drop it from
`rind-dimpl/Cargo.toml` in the PR that bumps dimpl, keeping the test that a
mismatched scheme is refused.

The fix, [algesten/dimpl#209](https://github.com/algesten/dimpl/pull/209),
adds `SignatureVerifier::cert_named_group(&self, cert_der) ->
Result<NamedGroup, CertificateError>`, a required method once `_crypto-common`
is off. Implement it in `rind-dimpl/src/sign.rs` with the curve parse
`Verifier::verify_signature` already does, shared by both. Dropping the
feature rather than keeping its default implementation stops `rind-dimpl`
relying on an underscored feature dimpl calls internal. dimpl holds the fix
for 0.10.0 because it breaks the provider API, so the bump also absorbs
whatever else 0.10.0 breaks.

## Waiting

- algesten/dimpl: merges [#209](https://github.com/algesten/dimpl/pull/209) and publishes 0.10.0. On 2026-11-15 the issue and PR were still open, its maintainer said the fix waits for 0.10.0, and the newest release was 0.9.0 (2026-10-25). Check with `gh pr view 209 -R algesten/dimpl --json state`, then dimpl's releases on crates.io.
