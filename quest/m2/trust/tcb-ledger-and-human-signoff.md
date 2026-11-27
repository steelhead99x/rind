# [XS] Adopt the human sign-off policy for unsafe, assembly, and proof axioms

## Goal

The repository states which changes need the maintainer's sign-off, so a security reviewer can read what a human has looked at, while day-to-day agent-assisted PRs stay light. The maintainer confirms or adjusts the draft below, and the PR that adopts it adds it to `CONTRIBUTING.md` and, if chosen, a `.github/CODEOWNERS`.

## Plan

[The TCB & Axiom Ledger](/proofs/README.md#tcb--axiom-ledger) and `admin/vg-binding` landed (the 2026-11-21 plan's first two parts); this is what remained, a governance promise only the maintainer can make.

Drafted wording for `CONTRIBUTING.md`, under a new `# Sign-off` heading, which the PR that adopts it copies:

> These changes land only on the maintainer's explicit approval, which an agent never gives itself and a merge queue pick does not imply:
>
> - **`unsafe`**: any added or changed `unsafe` block or `unsafe impl`. Reviewers find these in the diff itself: AUDIT.md's `unsafe` table is a dated per-area count, so it does not show a changed block.
> - **Assembly**: a hand edit to `asm!`, `naked_asm!`, or `global_asm!` under `rind/src/low/`, or a bump of an importer's `REV` (`admin/import-*`, `thirdparty/s2n-bignum/RIND.md`), which regenerates it.
> - **Proof trust**: a new or changed Lean `axiom`, `bv_decide`, or hand model (an `admin/prove` `check_quote`), the TCB & Axiom Ledger's tables moving, a change to `UNCOVERED` in `admin/vg-binding`, `proofs/hol-light/`, or `admin/prove-bytes`'s allowed differences.
> - **FFI**: a change to an exported `extern "C"` function or its types in rind-dart, rind-openssl, rind-python, or rind-fips.
>
> A PR that adds `unsafe` where `.github/CODEOWNERS` names no path adds that path, and its author requests the maintainer's review by hand, since GitHub reads CODEOWNERS from the base branch; the maintainer's own PR needs no request, and the maintainer's sign-off comment on it counts.
>
> Everything else, including new safe Rust, tests, docs, and benchmarks, needs no sign-off beyond the queue's checks.

Drafted `.github/CODEOWNERS`, if the maintainer wants the review requested automatically. Its paths are where `unsafe` lives today (AUDIT.md's table, plus the few files outside `low` that hold it); the policy covers any `unsafe` block, so a new one elsewhere adds its path, as the wording's last paragraph says:

```
/rind/src/low/                  @kixelated
/rind/src/fips_rng.rs           @kixelated
/rind/src/mid/p256.rs           @kixelated
/rind-aws-lc-rs/src/kem.rs      @kixelated
/proofs/                        @kixelated
/admin/prove*                   @kixelated
/admin/vg-binding               @kixelated
/admin/ledger                   @kixelated
/admin/import-*                 @kixelated
/thirdparty/s2n-bignum/         @kixelated
/rind-dart/                     @kixelated
/rind-openssl/                  @kixelated
/rind-python/                   @kixelated
/rind-fips/                     @kixelated
```

The maintainer decided on 2026-11-25: adopt the wording above in `CONTRIBUTING.md` under `# Sign-off` and add the drafted `.github/CODEOWNERS`, so each such PR requests the maintainer's review, without requiring code-owner approval in `main`'s ruleset: GitHub does not let an author approve their own PR, so a required code-owner review would block the maintainer's own PRs on those paths. Set that requirement in dotfiles' `bin/repo-settings` once a second owner exists. Check it is done: `CONTRIBUTING.md` has the `# Sign-off` heading, `.github/CODEOWNERS` exists, and this quest is deleted.
