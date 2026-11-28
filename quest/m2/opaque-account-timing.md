# [M] OPAQUE's KE2 takes the same path for known and unknown accounts

## Goal

`respond` in `rind/src/high/opaque.rs` does the same work for an account that exists and one that does not: the lookup supplies fixed-size fields either way, and the suite check and record choice do not branch on whether the account exists, so repeated unauthenticated login requests cannot tell accounts apart by timing.

## Plan

- Found by the full review of steelhead99x/rind#349, which brought `opaque.rs` in unchanged from kixel-ai/rind. Today `respond` copies a stored record for a known account but assembles a dummy record from three inputs for an unknown one, and the suite check branches on the record being present. The owner decided (2026-11-28) to land the sync as is and plan this here.
- Have the caller's lookup return a fixed-size record, a fake one for an unknown account derived as RFC 9807 describes for unknown clients, and select between real and fake without a branch.
- A ctgrind test marks account presence secret and checks `respond` takes no branch or index on it.
- Report it upstream through [upstream-reports](/quest/m2/upstream-reports.md) once the fix exists.
