# [S] The opt-z constant-time row builds with fat LTO and one codegen unit

## Goal

`ctgrind.yml`'s `profile (opt-z)` row builds as consumers who optimize for size usually do, with `lto = "fat"` and `codegen-units = 1` beside `opt-level = "z"`, and its valgrind suites, adapters included, pass there with suppressions that inlining cannot move.

## Plan

Found by [kixel-ai/rind#969](https://github.com/kixel-ai/rind/pull/969), which added the `profile` job. The maintainer decided there (2026-11-23): ✅ not yet; first anchor the PEM suppressions on something inlining can't move, as this quest (rejected: enable fat LTO on the row now).

- At opt-z with fat LTO and one codegen unit, rind's unit and Wycheproof suites pass under ctgrind, but `rind-rcgen`'s and `rind-dimpl`'s adapter tests fail 2: rustls-pki-types' PEM framing, whose branches on delimiters are public by design, is inlined into frames that `admin/ctgrind.supp`'s `rustls-pki-types-pem-*` entries do not match, since each must end in a rustls-pki-types frame.
- Anchor those entries on a frame fat LTO keeps, such as a test-side `#[inline(never)]` wrapper around the adapter's call into the PEM parser, instead of the inlined frames' names.
- Then set `CARGO_PROFILE_RELEASE_LTO=fat` and `CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1` on the opt-z row, and check a dispatched `ctgrind` run with `-f jobs='profile:opt-z'` passes.
