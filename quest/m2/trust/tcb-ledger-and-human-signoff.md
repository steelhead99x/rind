# [S] Publish TCB & Axiom Ledger, bind VG theorems in CI, and draft human sign-off policy

## Goal

Security reviewers can read a single 1-page TCB & Axiom Ledger at the top of `proofs/README.md` and `AUDIT.md` listing every trusted component, Lean axiom, and hand-written model; CI checks that verified-garbage (`vg`) proof theorems actually bind to the compiled binary functions; and the repo has a drafted human sign-off policy for `unsafe`, assembly, and proof-axiom changes ready for maintainer adoption.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ publish the TCB & Axiom Ledger, enforce VG theorem binding in CI, and draft the human sign-off policy (rejected: skip).

- **1-page TCB & Axiom Ledger**:
  - Add a concise, scannable ledger near the top of `proofs/README.md` and link/mirror it in `AUDIT.md` enumerating:
    - What is machine-checked (Lean 4 / Aeneas / Vale / verified-garbage) vs. what sits in the Trusted Computing Base (Lean kernel, Aeneas extractor, assembler/LLVM lowering, CPU ISA models, and the 10 hand-written models / ~3,451 lines tracked in `quest/m4/verified/aeneas-fn-pointers.md`).
    - Every `axiom`, `sorry` (must be 0), and custom assumption across `proofs/`, with a script or CI check that fails if an unlisted axiom is added.
- **VG theorem-binding check**:
  - Close the gap noted in `proofs/README.md` (around lines 245-247 and 1505) by adding an automated check (e.g. in `admin/vg-bytes` or a companion CI check) that verifies each compiled VG symbol checked against machine bytes actually corresponds to a proven theorem of the matching type/specification, not just an unreferenced byte slice.
- **Human sign-off policy for `unsafe`, assembly, and proof axioms**:
  - Draft a concrete policy (in `CONTRIBUTING.md` / `SECURITY.md` / `.github/CODEOWNERS` as appropriate) stating what requires human maintainer sign-off (new `unsafe` blocks, assembly edits, Lean axioms/TCB edits, FFI boundary changes) while keeping day-to-day agent-assisted PRs lightweight. Because adopting a binding review/governance promise is a maintainer decision, surface the proposed policy wording clearly in the PR for the maintainer to confirm or adjust before merge.
