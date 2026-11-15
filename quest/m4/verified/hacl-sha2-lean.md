# [M] HACL*'s SHA-2 block functions are proven in Lean

## Goal

The portable backend's SHA-256 and SHA-512 block functions, libcrux-sha2's `sha256_update_nblocks` and `sha512_update_nblocks`, are translated with the rest of the portable backend and proven against FIPS 180-4 in Lean, so `sha256_update_nblocks_spec` and `sha512_update_nblocks_spec` in `proofs/Rind/Portable/Hacl.lean` stop being axioms and the portable SHA-2 ✓ rests on no HACL* theorem.

## Plan

Follows [the portable backend's proofs](https://github.com/kixel-ai/rind/pull/649), which took the axiom route because Charon cannot translate the two functions.

Decided 2026-11-12 (maintainer, /quest-unblock): ✅ approve the HACL* axioms route for [kixel-ai/rind#649](https://github.com/kixel-ai/rind/pull/649), so two restated F* theorems join the trust base, and replace them here once Charon is fixed (rejected: hold that PR until Charon is fixed).

- The blocker: libcrux-macros' `unroll_for!` unrolls each function's 64 or 80 rounds into one deeply nested body, and Charon panics translating it when it reaches its fixed `MAX_STACK_DEPTH` of 1024 (`charon/src/utils.rs`). `admin/prove`'s portable pass therefore leaves them opaque, as Charon leaves other crates' bodies.
- Once Charon translates them, have `admin/prove`'s portable pass translate the two bodies and prove each against `Rind/HashSpec.lean`'s `sha256.compress` and `Rind/Sha2.lean`'s `processBlock`, as `Rind/X86_64/ChaCha20.lean` proves HACL*'s ChaCha20 rounds. The axioms' statements are the theorems to prove, so nothing above `Hacl.lean` changes.
- Decided 2026-11-13 (maintainer, /quest-merge of #649): ✅ keep this quest (rejected: drop). ✅ approve filing the Charon panic upstream now (rejected: wait for [the upstream reports batch](/quest/m2/upstream-reports.md), the maintainer files it), because the fix blocks rind's own proof work, unlike most `UPSTREAM.md` entries. An agent drafted the issue below; the maintainer approves its text before it is posted.
- The unrolled bodies are long straight-line code; if `step*` is slow on them, prove one round as a lemma and let the unrolled body reuse it.

### Draft issue for AeneasVerif/charon

Title: Panic "stack depth limit exceeded" on deeply nested control flow from an unrolled loop

> Charon panics translating libcrux-sha2's `sha256_update_nblocks` (and `sha512_update_nblocks`). libcrux-macros' `unroll_for!` unrolls their 64 or 80 rounds into one function body whose blocks nest past the fixed `MAX_STACK_DEPTH` of 1024 in `charon/src/utils.rs`, and the control-flow reconstruction panics:
>
> ```
> stack depth limit exceeded (transform/control_flow/ullbc_to_llbc.rs)
> ```
>
> **Version:** Aeneas nightly release `nightly-2026.11.03-ab34bd2`, which ships Charon, with Rust nightly 2026-09-17.
>
> **Reproduce:** in [kixel-ai/rind](https://github.com/kixel-ai/rind), add `--include 'libcrux_sha2::hacl::sha256_update_nblocks' --extract-opaque-bodies` to `admin/prove`'s portable pass and run `nix develop .#prove --command admin/prove lean`. Charon panics translating `sha256_update`.
>
> **Expected:** the function translates, or Charon reports an error for that item and continues, rather than panicking. The body is straight-line code, so its depth comes from nesting, not from recursion; an iterative traversal, or a limit that scales with the body, would avoid it.
>
> We want the translation to prove these functions in Lean with Aeneas instead of assuming HACL*'s F* theorems about them.

## Waiting

- AeneasVerif/charon: translate a function whose body nests past Charon's fixed `MAX_STACK_DEPTH` without panicking. Check by bumping Charon in `flake.nix` and running the reproduction in `UPSTREAM.md`'s "Charon panics on HACL*'s unrolled SHA-2", which then translates both functions.
- Maintainer: approve the draft issue text above, or edit it, so an agent posts it to AeneasVerif/charon; an agent cannot post outside the maintainer's orgs without that approval. Done once the issue exists and `UPSTREAM.md`'s entry links it.

## Related

- [Every hand model of untranslated Rust is retired](/quest/m4/verified/aeneas-fn-pointers.md) - retires the other places `proofs/` stands in for Rust the translation leaves out
