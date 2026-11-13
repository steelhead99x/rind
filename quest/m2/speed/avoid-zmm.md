# [S] Intel cores that downclock for 512-bit vectors run the 256-bit kernels

## Goal

On the Intel cores that lower their clock when 512-bit registers are in use, rind picks its 256-bit kernels wherever it has a 512-bit one, as BoringSSL and Linux do, so a server that mixes rind with other work does not slow the other work down.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ adopt the rule now, unmeasured (rejected: measure first; no quest). No host here can measure it: `fedora` is Zen 5, which does not downclock, and SDE emulates instructions, not frequency. The rule comes from two projects that did measure, so rind borrows it and says so.

- Today the choice looks only at feature bits. `HaveAvx512ForAesGcm::check()` (`rind/src/low/x86_64/cpu.rs:173-177`) admits any core with the features, and AES-GCM takes the 512-bit kernel from 2 KB (`AVX512_KERNEL_MINIMUM_CIPHER_LEN`, `rind/src/low/x86_64/aes_gcm.rs:517`). The 256-bit VAES kernel it would fall back to is already in the tree, and so is `is_intel()` (`cpu.rs:374`).
- The rule: BoringSSL's `CRYPTO_cpu_avoid_zmm_registers` and Linux's `zmm_exclusion_list` in `arch/x86/crypto`. The audit read Linux's list as Intel family 6 models 85, 106, 108, 125, 126, 140, and 141 (Skylake-X through Tiger Lake). Read both again at a pinned revision, cite them in the code, and take the list from there, not from this file. Whether aws-lc carries the same rule is unchecked; if it does not, note that this is one place rind follows BoringSSL instead.
- Inventory every routine that touches a zmm register, and apply the rule to each that has a 256-bit sibling. On 2026-11-12 they were two: AES-GCM (the `_mm512` intrinsics in `aes_gcm.rs`, `ghash.rs`, and `aes.rs`, and BoringSSL's `aes_gcm_{enc,dec}_update_vaes_avx512` and `gcm_init_vpclmulqdq_avx512`), and ML-KEM's 8-way sampler (`mlkem768_sample_poly_ntt_8x.rs`, behind `HaveAvx512ForMlKem`, `cpu.rs:220-225`). One with no 256-bit sibling keeps its 512-bit path, listed in the PR with what the fallback would cost.
- Searching for `zmm` overcounts. The `mlkem_*` and `mldsa_*` routines and `sha3_keccak4_f1600_alt.rs` are chosen under AVX2 and run 128-bit or 256-bit instructions, on xmm or ymm registers. `zmm` appears only in their `out("zmmN")` clobber lists, which tell the compiler the upper halves are not preserved. Count a routine only if an instruction or intrinsic in it is 512 bits wide.
- Not RSA. The interview named the IFMA RSA routines, and the code check found they are `rsaz_amm52x{20,30,40}_x2_ifma256`, which use ymm registers only (`rsaz_avx512.rs` has no zmm), so the rule does not touch them.
- Test the choice under SDE's Ice Lake and Tiger Lake models (`-icl`, `-tgl`), which report those family and model numbers, next to a model the rule leaves alone.
- PLATFORMS.md says which cores take the 256-bit path and that the reason is borrowed, not measured. Name the measurement that would settle it for whoever gets such a host: AES-GCM throughput on one core while another runs scalar work, with and without the rule.

## Related

- [VAES AES-GCM](/quest/m4/verified/aes-gcm-x86-vaes.md) - proves the kernels this chooses between
