# [S] OPAQUE refuses an OPRF evaluation that reflects the client's blinded element

## Goal

Registration's `store` and login's `LoginState::finish` (`rind/src/high/opaque.rs`) refuse a server's evaluated element that equals the blinded element the client sent in that exchange, before running Argon2id, so a server cannot have the client derive a record and export key without its per-account OPRF key, which would let the Argon2id work for one password guess be reused across accounts.

## Plan

- Found by the full review of steelhead99x/rind#349, which brought `opaque.rs` in unchanged from kixel-ai/rind. The owner decided (2026-11-28) to land the sync with upstream's code as is and plan this here, to fix in rind or raise upstream.
- Compare the evaluated element with the blinded one in constant time and return the existing protocol error on a match, in both paths. Check what RFC 9807 and the reference implementations do with a reflected evaluation, and follow it.
- A test feeds each path its own blinded element as the evaluation and expects the refusal.
- Report it upstream through [upstream-reports](/quest/m2/upstream-reports.md) once the fix exists, so the next sync does not bring the old code back.
