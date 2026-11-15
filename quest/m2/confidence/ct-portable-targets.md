# [M] The portable backend's secret branches are checked on i686, s390x, and riscv64

## Goal

On every target rind runs only its portable backend for, starting with `i686`, big-endian `s390x`, and `riscv64gc` (PLATFORMS.md), a constant-time check runs the portable code's `ct_*` tests and fails on any branch or memory address that depends on a secret, as `admin/ctgrind` does for x86_64 and aarch64 and `admin/ct-qemu` for armv7. A branch a check finds is fixed in this quest's PR.

## Plan

Found by the 2026-11-14 [upstream-updates](/quest/m2/upstream-updates.md) run, from public advisories: libsodium's `b38e2c9b`, `d6d7c2f5`, `96ccf42f`, and `8ec13adc` (2026-11-11 to 11-12) stop compilers turning ML-KEM's, ML-DSA's, and Elligator 2's sign-mask arithmetic into branches on 32-bit PowerPC and RISC-V, and RUSTSEC-2026-0426 reports LLVM turning a Rust conditional subtraction into a secret-dependent jump on i586 and s390x. rind's portable ML-KEM and ML-DSA use the same idioms (`low/generic/mlkem_poly.rs`'s `mlkem_reduce`, `low/generic/mldsa_poly.rs`), and today's checks see branches only on x86_64, aarch64, and armv7; `admin/ct-vartime` covers these targets but looks only for variable-time instructions.

- Prefer `admin/ctgrind`'s taint check wherever valgrind runs the target, since it flags a branch or address on a secret whichever way the secret steers it: i686 natively on an x86_64 host, and s390x and riscv64 on a native host if one is available (valgrind supports both). Elsewhere extend `admin/ct-qemu` with `qemu-s390x` and `qemu-riscv64`, which needs no native host but compares two seeds' traces, so it misses a branch both seeds steer the same way: its `ct_qemu_*` tests there pick secrets that drive each branch-prone idiom both ways, such as zero and nonzero coefficients and a sign mask set and clear.
- Run it nightly with the other constant-time workflows, not in `just ci`.
- Cover every primitive the portable backend runs on a secret, not only the lattice ones: the field arithmetic, hash-to-curve, AES and GHASH (`aes_nohw`, `ghash_nohw`), and RSA.
