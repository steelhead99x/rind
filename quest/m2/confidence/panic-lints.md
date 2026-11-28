# [L] Clippy forbids accidental panics in rind and non-ring adapters

## Goal

`just check` and CI forbid `clippy::unwrap_used`, `clippy::indexing_slicing`, `clippy::arithmetic_side_effects`, and `clippy::panic` across `rind` core and every non-`rind-ring` adapter crate in the workspace, keeping documented `.expect(...)` and `assert!(...)` invariants (such as release-mode `asm!` preconditions) and allowing test code to panic freely. Existing violations in covered crates are refactored to provably infallible forms or narrowed behind reasoned `#[expect(..., reason = "...")]` annotations, and `admin/prove` and `admin/ctgrind` stay green.

Non-goals: covering `rind-ring` (which intentionally mirrors `ring`'s panics), forbidding `expect_used` or `unreachable`, changing any public API signature, or adding `#[no_panic]` attributes.

## Plan

Decided 2026-11-27 (maintainer, `/quest-plan`):

- ✅ Scope and strictness: `rind` core plus all non-`rind-ring` adapter crates, forbidding `clippy::unwrap_used`, `clippy::indexing_slicing`, `clippy::arithmetic_side_effects` (which also covers integer division and remainder), and `clippy::panic`, while allowing documented `.expect(...)`, `assert!(...)` for `asm!` wrapper preconditions, and `#[expect(..., reason = "...")]` where an invariant cannot yet be encoded in types (rejected: omitting `arithmetic_side_effects`; `rind` core only; adding `#[no_panic]` checks on entry points). Including `arithmetic_side_effects` also guards against compiler-inserted overflow checks that branch on secrets and fail `ctgrind` in dev builds.

Milestone m2 (`confidence`): mechanical assurance checks that keep `rind` correct and panic-free live here. `rind`'s `AGENTS.md` already forbids panics on hostile input, and the 2026-11-09 audit confirmed no panic reachable from public input; this gate prevents regressions from future changes.

Guidance for the implementer:

- `just check` runs Clippy through `RUSTC_WORKSPACE_WRAPPER=clippy-driver` on `nextest`, which compiles `#[cfg(test)]` code too. Add a workspace `clippy.toml` enabling `allow-unwrap-in-tests = true`, `allow-indexing-slicing-in-tests = true`, and `allow-panic-in-tests = true` (and scope `arithmetic_side_effects` cleanly away from test code, or apply the restriction lints to library targets / non-test items) so unit tests stay concise.
- Pair the new lints with `clippy::allow_attributes_without_reason = "warn"` (matching `moq`) so every remaining suppression states its invariant and is easy to audit.
- Exclude `rind-ring` (intentional parity panics, see [parity/README.md](/quest/m3/parity/README.md)), `thirdparty/`, and unpublished bench/fuzz/test-harness crates unless they opt in.
- Prefer type-level fixes over suppressions: `slice::as_chunks` / fixed-size arrays instead of `chunks_exact` + `try_into().unwrap()`, iterators / `split_at_checked` instead of raw indexing, `NonZero` divisors, and wrapping/saturating/checked arithmetic where overflow is impossible or explicitly defined.
- Watch the Lean proof pipeline (`admin/prove`): `proofs/` translates `rind`'s Rust via Charon + Aeneas and checks hand-quoted dispatch blocks verbatim ([proofs/README.md](/proofs/README.md)). Run `admin/prove` and `admin/ctgrind` on any touched proven or secret-handling modules, and keep proven Rust shapes compatible with Aeneas or update the proofs alongside.
- Watch performance on hot paths (`low/` and `mid/`): replacing panicking arithmetic or indexing with `Result`-returning `checked_*` can regress codegen; prefer wrapping/infallible array ops and check benchmarks if a hot loop changes.

Public API: none.
