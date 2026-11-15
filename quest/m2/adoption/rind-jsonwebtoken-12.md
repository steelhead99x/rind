# [S] rind-jsonwebtoken supports jsonwebtoken 12

## Goal

A published rind-jsonwebtoken 12.0.x is a provider for jsonwebtoken 12, offering exactly the API jsonwebtoken's own providers offer there, so its users get jsonwebtoken 12's fixes: claim type confusion for `sub`, `iss`, and `aud`, refusal of unknown critical header extensions, refusal of empty HMAC keys, and no panicking dummy provider installed when none is set.

## Plan

Found by the 2026-11-14 [upstream-updates](/quest/m2/upstream-updates.md) run. jsonwebtoken 12.0.0 shipped on 2026-11-13; its breaking changes for providers are the RustCrypto dependency updates (`rsa` 0.10, `p256` 0.14, `signature` 3) and the empty-HMAC-key refusal.

- Bump `rind-jsonwebtoken`'s `jsonwebtoken` requirement to 12 and its `pkcs1` to the major jsonwebtoken 12's RSA keys use (0.8.0 is out), and the crate to 12.0.0, as `sh/adapter-versions.sh` requires.
- `admin/adapter-api` diffs the adapter's API against jsonwebtoken's own providers; follow it.
- Whether to keep an 11.x maintenance line is the maintainer's call at the time; ask with what each costs.

## Scheduled

- 2026-11-20 - jsonwebtoken 12.0.0 clears Dependabot's 7-day cooldown
