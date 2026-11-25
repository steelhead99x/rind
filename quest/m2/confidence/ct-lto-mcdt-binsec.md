# [M] Check constant-time under LTO, tighten MCDT analysis, and expand BINSEC harnesses

## Goal

Constant-time verification catches compiler regressions introduced by release LTO or size optimization (`opt-level = "z"`/`"s"`), verifies MCDT hardware-register dominance rather than section-level relocations, scans `i686` and `x86_64` portable code for variable-time instructions, and covers ECDSA ASN.1, RSA-PSS, SLH-DSA, and protocol hot paths in BINSEC.

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ close the LTO, MCDT, `ct-vartime`, and BINSEC gaps found in the audit (rejected: skip).

- **LTO and size-opt CT runs**: add a nightly `ctgrind` / `ct-vartime` build configuration using `lto = "thin"` and one using `opt-level = "z"` (or `"s"`), since release consumers frequently enable LTO or size optimization where LLVM can re-introduce secret-dependent branches or `udiv`/`sdiv`.
- **Tighten `admin/ct-vartime`**:
  - Replace or augment the coarse section-level MCDT relocation check (`admin/ct-vartime`) with CFG/dominance verification (checking that every secret-operating path executes under the DIT/DIT-guard rather than merely referencing the guard symbol somewhere in the section).
  - Include `i686` and `x86_64` portable (`rind_portable`) builds in `admin/ct-vartime` so variable-time instructions (`div`/`idiv`, non-CT shifts/table lookups) are caught there too.
- **Expand BINSEC harnesses**: add symbolic constant-time BINSEC harnesses for ECDSA ASN.1 signing/encoding, RSA-PSS signing, SLH-DSA signing, and secret-handling protocol steps (HPKE/OPRF/SPAKE2+/FROST where tractable), and wire them into the nightly BINSEC workflow.
- Fix any constant-time violation uncovered by these checks in the same PR (or file an `m0` bug if a separate deep kernel rewrite is needed).

## Related

- [The portable backend's secret branches are checked on i686, s390x, and riscv64](/quest/m2/confidence/ct-portable-targets.md)
- [Constant-time checks run in debug builds too](/quest/m2/confidence/ct-portable-debug.md)
