#!/usr/bin/env bash
# Lint rind's library for bare-metal targets (`target_os = "none"`), where it
# builds without std, as `just bare-metal` and `just check`'s cross module run
# it. Clippy does not generate code, so each target that keeps an assembly
# backend is also built: that assembles its `global_asm`. Nothing here
# links a program, runs one, or checks timing on these cores.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# getrandom has no source on these targets until the program names one, which
# a library build cannot, so its custom backend stands in.
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

# lint TARGET [CLIPPY-ARGS...]: debug, whose `debug_assertions` code release
# leaves out, and release.
lint() {
    local target=$1
    shift
    local flags rustflags
    flags="CARGO_TARGET_$(tr 'a-z.-' 'A-Z__' <<<"$target")_RUSTFLAGS"
    rustflags=$custom
    if [[ $target == x86_64-unknown-none ]]; then
        rustflags+=" $sse2"
    fi
    for profile in dev release; do
        env "$flags=$rustflags" cargo clippy "$@" -p rind --lib --locked --target "$target" \
            --profile "$profile" -- --deny warnings
    done
}

# clippy is a check build, so it never assembles `global_asm`. Build the
# library once per target that selects an assembly backend, so an assembler
# rejection fails here. The assembly text does not change with the profile.
assemble() {
    local target=$1
    local flags rustflags
    flags="CARGO_TARGET_$(tr 'a-z.-' 'A-Z__' <<<"$target")_RUSTFLAGS"
    rustflags=$custom
    if [[ $target == x86_64-unknown-none ]]; then
        rustflags+=" $sse2"
    fi
    env "$flags=$rustflags" cargo build -p rind --lib --locked --target "$target"
}

# aws-lc builds for none of these, so rind-bench must leave it out of its
# dependencies there, as its benches leave out aws-lc-rs's rows.
no_aws_lc() {
    local target=$1
    local crates
    crates=$(cargo tree -p rind-bench -e normal,build,dev --locked --target "$target" \
        --prefix none --format '{p}')
    if grep -E '^aws-lc' <<<"$crates"; then
        echo "error: rind-bench depends on aws-lc for $target" >&2
        exit 1
    fi
}

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
# VPCLMULQDQ, and AVX-512 run only when those target features are enabled. XCR0 does not
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
    if ! dump=$(objdump -d "$rlib"); then
        echo "error: objdump failed on $rlib" >&2
        exit 1
    fi
    if ! grep -E -q '\.o\)?:[[:space:]]*file format' <<<"$dump"; then
        echo "error: objdump found no object file in $rlib" >&2
        exit 1
    fi
    if grep -E -q '(^|[[:space:]])stmxcsr([[:space:]]|$)' <<<"$dump"; then
        echo "error: $rlib emits stmxcsr" >&2
        exit 1
    fi
}

# `x86_64-unknown-none` with no extra target features: portable backend,
# dalek `serial`, and no `stmxcsr`. The rows above build the SSE2 assembly
# backend instead.
no_sse2() {
    local target=x86_64-unknown-none
    local flags rustflags json rlib
    flags="CARGO_TARGET_$(tr 'a-z.-' 'A-Z__' <<<"$target")_RUSTFLAGS"
    rustflags="$custom $scalar"
    for profile in dev release; do
        env "$flags=$rustflags" cargo clippy -p rind --lib --locked --target "$target" \
            --profile "$profile" -- --deny warnings
    done
    json=$(mktemp)
    env "$flags=$rustflags" cargo build -p rind --lib --locked --target "$target" \
        --message-format=json >"$json"
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
