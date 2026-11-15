#!/usr/bin/env bash
# Lint rind's library for bare-metal targets (`target_os = "none"`), where it
# builds without std, as `just bare-metal` and `just check`'s cross module run
# it. Clippy does not generate code, so each target that keeps an assembly
# backend is also built: that assembles its `global_asm`. `xtensa` lints the
# ESP32's Xtensa targets instead. Those are tier 3 and need espup's toolchain
# (`ESP_TOOLCHAIN`, by default `esp`), as `just xtensa` and
# `.github/workflows/xtensa.yml` run it. Compile only: nothing here links a
# program, runs one, or checks timing on these cores.
#
# Usage: sh/bare-metal.sh [xtensa]
set -euo pipefail

if (( $# > 1 )) || [[ ${1:-} != "" && $1 != xtensa ]]; then
    echo "Usage: $0 [xtensa]" >&2
    exit 2
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# getrandom has no source on `target_os = "none"` until the program names one,
# which a library build cannot, so its custom backend stands in. ESP-IDF has
# getrandom's own backend, so those rows do not set this.
custom='--cfg getrandom_backend="custom"'
# The x86_64 assembly needs SSE2. This target is soft-float and leaves SSE
# off, so `xmm` operands are refused until SSE2 is on, and LLVM aborts while
# splitting vector results if soft-float stays enabled beside it.
# `-soft-float` clears that.
# See UPSTREAM.md, "Clearing soft-float with -C target-feature will become an error".
sse2='-C target-feature=+sse,+sse2,-soft-float'
# Without SSE2, dalek's default simd backend does not compile, and the
# portable backend must not emit `stmxcsr`.
scalar='--cfg curve25519_dalek_backend="serial"'
cargo=(cargo)

# Cargo uses one rustflags source and ignores the rest, in this order
# (rustflags_from_env, then the target variable, then build.rustflags):
# CARGO_ENCODED_RUSTFLAGS, RUSTFLAGS, CARGO_TARGET_<triple>_RUSTFLAGS,
# CARGO_BUILD_RUSTFLAGS. Append this script's flags to that one source.
# Splitting is on spaces, and quote characters stay in the token, which is
# how `getrandom_backend="custom"` reaches rustc.
append_words() {
    local part
    local -a bits=()
    IFS=' ' read -r -a bits <<< "$1"
    for part in "${bits[@]}"; do
        [[ -n $part ]] && args+=("$part")
    done
}

run_cargo() {
    local target=$1 extra=$2
    shift 2
    local var target_flags mode joined
    var="CARGO_TARGET_$(printf '%s' "$target" | tr 'a-z.-' 'A-Z__')_RUSTFLAGS"
    target_flags=${!var-}
    local -a args=()
    if [[ -v CARGO_ENCODED_RUSTFLAGS ]]; then
        mode=encoded
        local rest=${CARGO_ENCODED_RUSTFLAGS} piece
        while [[ $rest == *$'\x1f'* ]]; do
            piece=${rest%%$'\x1f'*}
            [[ -n $piece ]] && args+=("$piece")
            rest=${rest#*$'\x1f'}
        done
        [[ -n $rest ]] && args+=("$rest")
    elif [[ -v RUSTFLAGS ]]; then
        mode=rustflags
        append_words "$RUSTFLAGS"
    elif [[ -n $target_flags ]]; then
        mode=target
        append_words "$target_flags"
    elif [[ -v CARGO_BUILD_RUSTFLAGS ]]; then
        mode=build
        append_words "$CARGO_BUILD_RUSTFLAGS"
    else
        mode=target
    fi
    append_words "$extra"
    if [[ ${#args[@]} -eq 0 ]]; then
        "$@"
        return
    fi
    joined=$(printf '%s ' "${args[@]}")
    joined=${joined% }
    case $mode in
        encoded)
            local IFS=$'\x1f'
            joined="${args[*]}"
            env -u RUSTFLAGS "CARGO_ENCODED_RUSTFLAGS=$joined" "$@"
            ;;
        rustflags)
            env -u CARGO_ENCODED_RUSTFLAGS "RUSTFLAGS=$joined" "$@"
            ;;
        build)
            env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS "CARGO_BUILD_RUSTFLAGS=$joined" "$@"
            ;;
        target)
            env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS "$var=$joined" "$@"
            ;;
    esac
}

# Flags every lint of TARGET needs. ESP-IDF uses getrandom's own backend.
# Bare-metal x86_64 also needs SSE2. dalek's default stays off AVX there:
# cpufeatures reports a SIMD feature on this os only when it is a target
# feature, and this script does not enable AVX.
required_flags() {
    local target=$1
    case $target in
        xtensa-*-espidf) ;;
        x86_64-unknown-none) printf '%s' "$custom $sse2" ;;
        *) printf '%s' "$custom" ;;
    esac
}

# rows TARGET COMMAND [ARGS...]: debug, whose `debug_assertions` code release
# leaves out, and release, each with and without `wipe`.
rows() {
    local target=$1
    shift
    local flags profile features arg
    flags=$(required_flags "$target")
    # Cargo arguments precede `--`. Anything after it is for rustc, so the
    # profile and the target have to be inserted before that separator.
    local -a before=() after=()
    local seen=0
    for arg in "$@"; do
        if [[ $seen -eq 1 ]]; then
            after+=("$arg")
        elif [[ $arg == -- ]]; then
            seen=1
        else
            before+=("$arg")
        fi
    done
    for profile in dev release; do
        for features in "" wipe; do
            if [[ $seen -eq 1 ]]; then
                run_cargo "$target" "$flags" "${cargo[@]}" "${before[@]}" \
                    --target "$target" --profile "$profile" --features "$features" \
                    -- "${after[@]}"
            else
                run_cargo "$target" "$flags" "${cargo[@]}" "${before[@]}" \
                    --target "$target" --profile "$profile" --features "$features"
            fi
        done
    done
}

lint() {
    local target=$1
    shift
    rows "$target" clippy "$@" -p rind --lib --locked -- --deny warnings
}

check_lib() {
    local target=$1
    shift
    rows "$target" check "$@" -p rind --lib --locked
}

# clippy is a check build, so it never assembles `global_asm`. Build the
# library once per target that selects an assembly backend, so an assembler
# rejection fails here. The assembly text does not change with the profile
# or `wipe`.
assemble() {
    local target=$1
    run_cargo "$target" "$(required_flags "$target")" "${cargo[@]}" build -p rind --lib --locked \
        --target "$target"
}

# aws-lc builds for none of these, so rind-bench must leave it out of its
# dependencies there, as its benches leave out aws-lc-rs's rows.
no_aws_lc() {
    local target=$1
    local crates status
    status=0
    crates=$(run_cargo "$target" "" "${cargo[@]}" tree -p rind-bench -e normal,build,dev --locked \
        --target "$target" --prefix none --format '{p}') || status=$?
    if (( status != 0 )); then
        echo "error: cargo tree failed for $target" >&2
        exit "$status"
    fi
    if grep -E '^aws-lc' <<<"$crates"; then
        echo "error: rind-bench depends on aws-lc for $target" >&2
        exit 1
    fi
}

if [[ ${1:-} == xtensa ]]; then
    cargo=(cargo "+${ESP_TOOLCHAIN:-esp}")
    # Tier 3 ships no prebuilt standard library, so it is built from source.
    # ESP32-S2 has no compare-and-swap, so it builds `reuse_cache_without_cas`.
    # ESP-IDF is checked, not linted: there clippy's `missing_const_for_thread_local`
    # flags thread-locals whose initializers are already `const`.
    # See UPSTREAM.md, "Clippy flags const thread-local initializers".
    for target in xtensa-esp32-none-elf xtensa-esp32s2-none-elf xtensa-esp32s3-none-elf; do
        lint "$target" -Zbuild-std=core,alloc
    done
    check_lib xtensa-esp32s3-espidf -Zbuild-std=std,panic_abort
    # Every bench is empty on Xtensa. criterion's wait-timeout does not build
    # against ESP-IDF's libc, and ring and OpenSSL have no Xtensa port. The
    # check still fails if a bench names either. ESP-IDF uses getrandom's
    # own backend.
    run_cargo xtensa-esp32s3-espidf "" "${cargo[@]}" check -Zbuild-std=std,panic_abort \
        -p rind-bench --benches --locked --target xtensa-esp32s3-espidf
    exit 0
fi

# ARMv6-M (Cortex-M0+, the RP2040) and RV32IMC (the ESP32-C3) have no
# compare-and-swap, so they build `reuse_cache_without_cas`. ARMv7E-M
# (Cortex-M4 and M7, such as the nRF52840) has it, on the portable backend.
# A-profile `armv7a-none-eabi` and R-profile `armv7r-none-eabihf` keep the
# 32-bit ARM backend: bare metal never asks a kernel, so that backend's
# NEON and crypto paths stay off and the base assembly is what runs.
# `aarch64-unknown-none` keeps the aarch64 backend. Its tier is the
# compile-time target features: NEON by default, and the crypto extension
# only when the target enables it. Soft-float aarch64 has no NEON, so it
# stays on the portable backend. `x86_64-unknown-none` keeps the x86_64
# backend only with SSE2 and soft-float cleared, which this script enables:
# without SSE2 the target has no `xmm` registers and the build stays
# portable. With them the backend reads CPUID. AVX, AVX2, SHA512, and
# AVX-512 run only when those target features are enabled. XCR0 does not
# mean an interrupt saves YMM or ZMM. The script does not enable them.
for target in \
    thumbv6m-none-eabi \
    riscv32imc-unknown-none-elf \
    thumbv7em-none-eabihf \
    armv7a-none-eabi \
    armv7r-none-eabihf \
    aarch64-unknown-none \
    aarch64-unknown-none-softfloat \
    x86_64-unknown-none; do
    lint "$target"
done
for target in \
    armv7a-none-eabi \
    armv7r-none-eabihf \
    aarch64-unknown-none \
    x86_64-unknown-none; do
    assemble "$target"
done
# `x86_64-unknown-none` with no extra target features: portable backend,
# dalek `serial`, and no `stmxcsr`. The rows above build the SSE2 assembly
# backend instead.
no_sse2() {
    local target=x86_64-unknown-none
    local profile features root rlib
    for profile in dev release; do
        for features in "" wipe; do
            run_cargo "$target" "$custom $scalar" "${cargo[@]}" clippy -p rind --lib --locked \
                --target "$target" --profile "$profile" --features "$features" -- --deny warnings
        done
    done
    run_cargo "$target" "$custom $scalar" "${cargo[@]}" build -p rind --lib --locked \
        --target "$target"
    root=${CARGO_TARGET_DIR:-target}
    local found=0
    while IFS= read -r rlib; do
        found=1
        if grep -a -q stmxcsr "$rlib"; then
            echo "error: $target without SSE2 contains stmxcsr ($rlib)" >&2
            exit 1
        fi
    done < <(find "$root/$target/debug" -name 'librind*.rlib')
    if ((found == 0)); then
        echo "error: no rlib for $target without SSE2" >&2
        exit 1
    fi
}
no_sse2

no_aws_lc thumbv7em-none-eabihf
