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

# Cargo already chooses one rustflags source and ignores the rest:
# CARGO_ENCODED_RUSTFLAGS, RUSTFLAGS, CARGO_TARGET_<triple>_RUSTFLAGS,
# CARGO_BUILD_RUSTFLAGS, then config (`--config`, config files, `include`,
# `target.<triple>` and `target.'cfg(...)'`). An empty target variable is
# not a source. Replacing that source from here would have to parse Cargo's
# config. A wrapper appends this script's flags to each `--target` rustc
# invocation instead, including the cfg
# probe, so a `cfg(...)` table is evaluated by the same rustc Cargo builds
# with. A host build script has no `--target` and is left alone. Splitting
# is on spaces, and quote characters stay in the token, which is how
# `getrandom_backend="custom"` reaches rustc.
run_cargo() {
    local target=$1 extra=$2
    shift 2
    # The target selects the flags in `extra`. Cargo sees it as `--target`.
    : "$target"
    local wrapper base sum dir inner
    wrapper=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/bare-metal-rustc
    # Cargo runs one RUSTC_WRAPPER. Keep a wrapper the caller already
    # exported: this script appends its flags, then that wrapper runs rustc.
    inner=${RUSTC_WRAPPER:-}
    # Cargo fingerprints its own rustflags, not flags a wrapper appends.
    # Two flag sets for one triple (SSE2, and no SSE2 with dalek `serial`)
    # would otherwise reuse one build script and compile the wrong backend.
    base=${CARGO_TARGET_DIR:-target}
    sum=$(printf '%s' "$extra" | cksum | awk '{ print $1 }')
    dir=$base/rind-bare-metal-$sum
    env "RIND_BARE_METAL_RUSTFLAGS=$extra" \
        "RIND_BARE_METAL_INNER_WRAPPER=$inner" \
        "RUSTC_WRAPPER=$wrapper" "CARGO_TARGET_DIR=$dir" "$@"
}

# Flags every lint of TARGET needs. ESP-IDF uses getrandom's own backend.
# Bare-metal x86_64 also needs SSE2. This script does not enable AVX.
# cpufeatures on `target_os = "none"` reports it only when that target
# feature is on.
required_flags() {
    local target=$1
    case $target in
        xtensa-*-espidf) ;;
        x86_64-unknown-none) printf '%s' "$custom $sse2" ;;
        *) printf '%s' "$custom" ;;
    esac
}

# rows TARGET COMMAND [ARGS...]: debug, whose `debug_assertions` code release
# leaves out, and release.
rows() {
    local target=$1
    shift
    local flags profile arg
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
        if [[ $seen -eq 1 ]]; then
            run_cargo "$target" "$flags" "${cargo[@]}" "${before[@]}" \
                --target "$target" --profile "$profile" -- "${after[@]}"
        else
            run_cargo "$target" "$flags" "${cargo[@]}" "${before[@]}" \
                --target "$target" --profile "$profile"
        fi
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
# rejection fails here. The assembly text does not change with the profile.
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
    # Every bench is an empty program on Xtensa. criterion's wait-timeout does
    # not build against ESP-IDF's libc, and ring and OpenSSL have no Xtensa
    # port, so those paths are `cfg`'d out. This check compiles the empty
    # programs. A name inside that `cfg` is not typechecked. ESP-IDF uses
    # getrandom's own backend.
    run_cargo xtensa-esp32s3-espidf "" "${cargo[@]}" check -Zbuild-std=std,panic_abort \
        -p rind-bench --benches --locked --target xtensa-esp32s3-espidf
    exit 0
fi

# ARMv6-M (Cortex-M0+, the RP2040) and RV32IMC (the ESP32-C3) have no
# compare-and-swap, so they build `reuse_cache_without_cas`. ARMv7E-M
# (Cortex-M4 and M7, such as the nRF52840) has it, on the portable backend.
# A-profile `armv7a-none-eabi`, R-profile `armv7r-none-eabihf`, and
# `aarch64-unknown-none` are on the portable backend too: their assembly makes
# unaligned accesses, which a strict-align target faults on. Soft-float
# aarch64 has no NEON either. `x86_64-unknown-none` keeps the x86_64
# backend only with SSE2 and soft-float cleared, which this script enables:
# without SSE2 the target has no `xmm` registers and the build stays
# portable. With them the backend reads CPUID. AVX, AVX2, SHA512, VAES,
# VPCLMULQDQ, and AVX-512 run only when those target features are enabled.
# XCR0 does not mean an interrupt saves YMM or ZMM. The script does not
# enable them.
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
assemble x86_64-unknown-none
# The rlib this cargo invocation wrote. A `find` of the shared debug
# directory also sees an older rlib from the SSE2 assemble row above.
rlib_from_messages() {
    local json=$1
    grep '"reason":"compiler-artifact"' "$json" \
        | grep '"name":"rind"' \
        | grep -o '"[^"]*librind[^"]*\.rlib"' \
        | tr -d '"' \
        | tail -n 1 || true
}

# `stmxcsr` is the bytes 0F AE /3. The mnemonic is not in the object code, so
# grepping the rlib for that text misses an emitted instruction and can pass
# on a build that still raises `#UD`. Disassemble this build's objects. GNU
# objdump and llvm-objdump (macOS's objdump) both read the rlib's archive
# directly and skip its metadata member, so no `ar` dialect is involved.
reject_stmxcsr() {
    local rlib=$1
    local dump
    if ! command -v objdump >/dev/null; then
        echo "error: objdump is required to check for stmxcsr" >&2
        exit 1
    fi
    # Tens of megabytes of text, so a file rather than a shell variable.
    dump=$(mktemp)
    local error=''
    if ! objdump -d "$rlib" >"$dump"; then
        error="objdump failed on $rlib"
    elif ! grep -E -q '\.o\)?:[[:space:]]*file format' "$dump"; then
        error="objdump found no object file in $rlib"
    elif grep -E -q '(^|[[:space:]])stmxcsr([[:space:]]|$)' "$dump"; then
        error="$rlib emits stmxcsr"
    fi
    rm -f "$dump"
    if [[ -n $error ]]; then
        echo "error: $error" >&2
        exit 1
    fi
}

# `x86_64-unknown-none` with no extra target features: portable backend,
# dalek `serial`, and no `stmxcsr`. The rows above build the SSE2 assembly
# backend instead.
no_sse2() {
    local target=x86_64-unknown-none
    local profile json rlib
    for profile in dev release; do
        run_cargo "$target" "$custom $scalar" "${cargo[@]}" clippy -p rind --lib --locked \
            --target "$target" --profile "$profile" -- --deny warnings
    done
    json=$(mktemp)
    run_cargo "$target" "$custom $scalar" "${cargo[@]}" build -p rind --lib --locked \
        --target "$target" --message-format=json >"$json"
    rlib=$(rlib_from_messages "$json")
    rm -f "$json"
    if [[ -z ${rlib:-} || ! -f "$rlib" ]]; then
        echo "error: no rlib for $target without SSE2" >&2
        exit 1
    fi
    reject_stmxcsr "$rlib"
}
no_sse2

no_aws_lc thumbv7em-none-eabihf
