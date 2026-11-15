#!/usr/bin/env bash
# Replay a fuzz target's corpus once on each CPU tier of an architecture, so
# the inputs the fuzzer found on the runner's own paths also check the others.
# Each tier denies what the one before it denied and more, walking down the
# tiers TESTING.md lists, since a faster path that needs only some of a tier's
# denied features would otherwise still run. The target must take
# `RIND_CPU_DISABLE_*`, as a build with `--cfg rind_cpu_disable` does. Extra
# arguments go to libFuzzer.
#
# Usage: sh/fuzz-replay.sh ARCH TARGET CORPUS [ARGS...]
#
# ARCH is the target's: x86_64, aarch64, or armv7, which an arm64 runner runs
# natively; or x86_64-sde, which runs it under Intel SDE.
set -euo pipefail

usage="usage: sh/fuzz-replay.sh ARCH TARGET CORPUS [ARGS...]"
arch=${1:?$usage}
target=${2:?$usage}
corpus=${3:?$usage}
shift 3

# The features each tier denies beyond the one before.
runner=()
case "$arch" in
    # fuzz.yml fuzzes on x86_64 itself, so this list skips the runner's own
    # paths. The tiers are: VAES without AVX-512; AVX2 and ADX without VAES or
    # the SHA extensions; Haswell's AVX2 without ADX; Sandy Bridge's AVX
    # without AVX2 or MOVBE, which reaches rind's VEX-encoded AES-GCM rather
    # than Vale's; AES-NI without AVX; SSSE3 without AES-NI; and SSE2.
    x86_64)
        tiers=(
            "avx512f avx512bw"
            "vaes sha sha512 intel"
            "adx"
            "avx2 movbe"
            "avx"
            "aes pclmulqdq sse41"
            "ssse3"
        )
        ;;
    # A runner has AVX-512, VAES, and the SHA extensions or lacks them from run
    # to run, and has no SHA512 instructions, so Diamond Rapids, which selects
    # every path, runs them all, then VAES without AVX-512. The x86_64 replay
    # covers the tiers below. LeakSanitizer is off under SDE: see UPSTREAM.md,
    # "LeakSanitizer deadlocks under Intel SDE".
    x86_64-sde)
        runner=(env ASAN_OPTIONS=detect_leaks=0 sde -dmr --)
        tiers=(
            ""
            "avx512f avx512bw"
        )
        ;;
    aarch64)
        tiers=(
            ""
            "sha3"
            "aes pmull sha2"
        )
        ;;
    # The crypto extension, NEON alone, and neither.
    armv7)
        tiers=(
            ""
            "aes pmull sha1 sha2"
            "neon"
        )
        ;;
    *)
        echo "error: no CPU tiers for $arch" >&2
        exit 1
        ;;
esac

deny=()
for tier in "${tiers[@]}"; do
    for feature in $tier; do
        deny+=("RIND_CPU_DISABLE_$feature=1")
    done
    echo "==> replaying $corpus on $arch denying: ${deny[*]:-nothing}" >&2
    env "${deny[@]}" "${runner[@]}" "$target" -runs=0 "$@" "$corpus"
done
