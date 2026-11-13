# [M] Intel's MXCSR-dependent timing and DOITM are handled

## Goal

No instruction that Intel lists as timing-dependent on MXCSR (MCDT) runs on secret data in rind without Intel's mitigation, `admin/ct-vartime` fails if one is added, and `PLATFORMS.md` says Intel's data-independent timing needs the OS to enable DOITM on processors that enumerate it with current microcode, and that SGX enclaves on those processors get it regardless of the OS.

## Plan

Found on 2026-11-12, reading pyca/verified-garbage, which checks MCDT with `ci/check_mcdt.py` and documents DOITM in its README. Decided with the maintainer the same day: ✅ a quest in m2 (rejected: m0, since neither has a known exploit).

- Start from Intel's own MCDT guidance and instruction list, not VG's copy. VG names vector multiplies such as `vpmuludq`, `vpmullw`, `vpmulhw`, and `vpmadd52luq`/`vpmadd52huq`, and Intel's fix of setting MXCSR to `0x1FBF` around the code.
- Rind runs these on secrets in at least AVX2 Poly1305, aws-lc's IFMA RSAZ, and AVX2 ML-KEM and ML-DSA. Trace every routine, imported assembly and intrinsics alike.
- Mitigate as aws-lc and BoringSSL do, if either does. Otherwise save, set, and restore MXCSR at each affected entry point, measured against the bar.
- DOITM: Intel guarantees data-independent timing only with DOITM enabled on processors that enumerate it (from Ice Lake and Gracemont on); one that does not enumerate it with the latest microcode behaves as if it were enabled, and enclave mode enables it regardless of the OS. The guarantee excludes the `VSHA512*` instructions. Say which kernels set it, as far as rind can know.
