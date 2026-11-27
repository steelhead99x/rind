#!/usr/bin/env bash
# Run COMMAND once for each slower CPU tier this host can be denied down to,
# with the `RIND_CPU_DISABLE_*` variables that hide its features and the
# `RIND_TEST_*` variables that fail the run that lands on the wrong path, as
# `build.yml`'s tier tests and `sanitizers.yml`'s AddressSanitizer run it. A
# release build honours the denials only with `--cfg rind_cpu_disable`.
#
# Usage: sh/cpu-tiers.sh COMMAND [ARGS...]
set -euo pipefail

if (($# == 0)); then
    echo "usage: sh/cpu-tiers.sh COMMAND [ARGS...]" >&2
    exit 1
fi

# Rust's name for the host's architecture, which `uname -m` gives as arm64 on
# macOS, and may give as x86_64 in an emulated Git Bash on Windows on Arm.
host=$(rustc -vV | sed -n 's/^host: //p')
case "${host%%-*}" in
    x86_64)
        tiers=(
            # rind's AVX2 SHA-1 and OpenSSL's AVX2 SHA-256 for CPUs without
            # the SHA extensions
            "RIND_CPU_DISABLE_sha=1 RIND_CPU_DISABLE_intel=1"
            # Vale's aes-gcm and avx2 ML-KEM without avx512 or vaes, and
            # RSA's CRT one exponentiation at a time on a runner with AVX-512
            # IFMA
            "RIND_CPU_DISABLE_avx512bw=1 RIND_CPU_DISABLE_avx512f=1 RIND_CPU_DISABLE_vaes=1 RIND_TEST_X86_AVX512_RSA=0"
            # s2n-bignum's _alt routines, and aws-lc's Montgomery
            # multiplication and RSAZ exponentiation, for CPUs with AVX2 but
            # without BMI2 and ADX, such as Haswell
            "RIND_CPU_DISABLE_adx=1 RIND_TEST_X86_BMI2_ADX=0 RIND_TEST_X86_AVX2=1"
            # aws-lc's SSE4.1 ChaCha20-Poly1305, its SSSE3 ChaCha20, SHA-1,
            # and SHA-256, its scalar SHA-512, the portable ML-KEM arithmetic,
            # and the SSE2 selects for CPUs without AVX2, such as AMD's
            # Bulldozer and Jaguar; x86-cpu's Sandy Bridge run covers aws-lc's
            # AVX SHA routines, which Intel's cores run there
            "RIND_CPU_DISABLE_avx2=1 RIND_CPU_DISABLE_sha=1 RIND_CPU_DISABLE_intel=1 RIND_TEST_X86_AVX2=0 RIND_TEST_X86_SSE41=1"
            # rind's AES-GCM and GHASH intrinsics without VEX encoding, and
            # aws-lc's AES-NI CTR, for CPUs with AES-NI but without AVX, such
            # as Westmere and the Goldmont and Tremont Atoms
            "RIND_CPU_DISABLE_avx=1 RIND_TEST_X86_AVX=0 RIND_TEST_X86_AES_HARDWARE=1"
            # aws-lc's vpaes and SSSE3 GHASH for CPUs without AES-NI or
            # PCLMULQDQ, such as Core 2 and Nehalem, where rind-rustls and
            # rind-dimpl prefer ChaCha20-Poly1305, and without SSE4.1 too, as
            # the first Core 2s lack it, ChaCha20 and Poly1305 in separate
            # passes
            "RIND_CPU_DISABLE_aes=1 RIND_CPU_DISABLE_pclmulqdq=1 RIND_CPU_DISABLE_avx=1 RIND_CPU_DISABLE_sse41=1 RIND_TEST_X86_AES_HARDWARE=0 RIND_TEST_X86_SSE41=0"
            # aws-lc's integer SHA-1 and SHA-256, its SSE2 AES and integer
            # GHASH, and HACL*'s ChaCha20 at every length, for CPUs without
            # SSSE3, such as QEMU's default `qemu64` model; every faster path
            # needs SSSE3 too
            "RIND_CPU_DISABLE_ssse3=1 RIND_TEST_X86_SSSE3=0 RIND_TEST_X86_SSE41=0 RIND_TEST_X86_AVX2=0 RIND_TEST_X86_AES_HARDWARE=0"
        )
        ;;
    aarch64)
        tiers=(
            # the by-4 AES-GCM and Keccak-f kernels for cores without SHA3,
            # and aws-lc's NEON ChaCha20-Poly1305 for those without SVE2, such
            # as Neoverse N1, failing a run whose OS hides the crypto
            # extension, and on Apple silicon the `dsb nsh; isb sy` barrier
            # after DIT for cores without `sb`
            "RIND_CPU_DISABLE_sha3=1 RIND_CPU_DISABLE_sve2=1 RIND_CPU_DISABLE_sb=1 RIND_TEST_ARM_CRYPTO_EXT=1 RIND_TEST_ARM_SVE2=0"
            # vpaes, NEON GHASH, and scalar SHA-1 and SHA-256 for cores
            # without the crypto extension, such as the Raspberry Pi 4's
            "RIND_CPU_DISABLE_aes=1 RIND_CPU_DISABLE_pmull=1 RIND_CPU_DISABLE_sha2=1 RIND_TEST_ARM_CRYPTO_EXT=0"
        )
        ;;
    *)
        echo "error: sh/cpu-tiers.sh knows the tiers of x86_64 and aarch64 only" >&2
        exit 1
        ;;
esac

for tier in "${tiers[@]}"; do
    echo "sh/cpu-tiers.sh: $tier" >&2
    # Each tier is a list of assignments, split into words on purpose.
    # shellcheck disable=SC2086
    env $tier "$@"
done
