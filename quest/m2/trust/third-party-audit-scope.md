# [S] Scope phased third-party security audit and prepare grant funding packet

## Goal

The repository contains a concrete, auditor-ready Phase 1 security audit scope (`low` + `mid` core primitives + Lean TCB/axioms, explicit file/LOC inventory, threat model, and out-of-scope boundaries) plus a drafted funding/grant brief targeting OSTIF, Sovereign Tech Fund, or Prossimo so the maintainer can initiate an external audit without starting from scratch.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ scope a phased third-party audit and prepare an OSTIF / Sovereign Tech Fund / Prossimo funding plan (rejected: skip). Per [quest/m2/trust/README.md](/quest/m2/trust/README.md), this quest prepares the scope and materials; actually engaging an auditor or submitting a grant remains a maintainer action.

- **Phased audit scope document** (linked from `AUDIT.md` or stored under `docs/` / `AUDIT.md` section):
  - **Phase 1 (highest risk, focused scope)**: `rind`'s `low` assembly/SIMD/portable kernels, `mid` constant-time arithmetic & key/RNG/wiping primitives, `rind-rustls` TLS provider boundary, and the formal verification TCB (Lean axioms, hand-written models, Aeneas/VG extraction assumptions). Include an exact file and LOC breakdown, build/test reproduction commands, and known threat model assumptions.
  - **Phase 2 (follow-on)**: Post-quantum schemes (`ml-kem`, `ml-dsa`, `slh-dsa`), protocols (`hpke`, `oprf`, `frost`, `spake2plus`, `vrf`, `blind_rsa`), and FFI bindings (`rind-python`, `rind-dart`, `rind-fips`, `rind-openssl`).
  - Explicitly note what is already machine-checked vs. what needs human cryptographic review (e.g. assembly-to-spec correspondence, side-channel leakage outside model assumptions, API misuse resistance, RNG/fork/zeroization edge cases).
- **Grant / funding application packet**:
  - Draft a concise project summary, public-good impact statement (pure-Rust memory-safe crypto with formal proofs, zero-C-toolchain `rustls` backend), target budget/timeline estimate, and checklist tailored to OSTIF, Sovereign Tech Fund (STF), and ISRG Prossimo.
  - Surface any open maintainer decisions (preferred audit firm/program, desired timeline, public report commitment) clearly in the PR; submitting applications or contacting auditors is left to the maintainer after merge.

## Related

- [Publish TCB & Axiom Ledger, bind VG theorems in CI, and draft human sign-off policy](/quest/m2/trust/tcb-ledger-and-human-signoff.md)
- [Define 1.0 roadmap, gate semver with cargo-semver-checks, scope changelogs, and document security backports](/quest/m2/trust/roadmap-1.0-and-backports.md)
