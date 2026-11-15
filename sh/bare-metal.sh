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
# (rustflags_from_env, then the target variable, then build.rustflags, then
# the config file): CARGO_ENCODED_RUSTFLAGS, RUSTFLAGS,
# CARGO_TARGET_<triple>_RUSTFLAGS, CARGO_BUILD_RUSTFLAGS, then
# target.<triple>.rustflags or build.rustflags from Cargo's config. Append
# this script's flags to that one source. Splitting is on spaces, and quote
# characters stay in the token, which is how `getrandom_backend="custom"`
# reaches rustc.
append_words() {
    local part
    local -a bits=()
    IFS=' ' read -r -a bits <<< "$1"
    for part in "${bits[@]}"; do
        [[ -n $part ]] && args+=("$part")
    done
}

# A backslash written as '\'' trips shellcheck, so the comparisons use this.
bs=$'\\'

unescape_basic() {
    local s=$1 out="" i=0 c
    local n=${#s}
    while (( i < n )); do
        c=${s:i:1}
        if [[ $c == "$bs" ]]; then
            local nch=${s:i+1:1}
            if [[ $nch == '"' || $nch == "$bs" ]]; then
                out+=$nch
                i=$((i + 2))
                continue
            fi
        fi
        out+=$c
        i=$((i + 1))
    done
    printf '%s' "$out"
}

# A rustflags string is split on spaces. Each element of a rustflags array
# is one argument, even when it contains a space. A `#` outside a string is
# a comment, and an array ends at `]`.
append_toml_rustflags() {
    local -n dest=$1
    local value=$2
    value=${value#"${value%%[![:space:]]*}"}
    local i=0 c n=${#value} q
    if [[ $value == '"'* || $value == "'"* ]]; then
        q=${value:0:1}
        local inner=""
        i=1
        while (( i < n )); do
            c=${value:i:1}
            if [[ $q == '"' && $c == "$bs" ]]; then
                inner+=${value:i:2}
                i=$((i + 2))
                continue
            fi
            if [[ $c == "$q" ]]; then
                break
            fi
            inner+=$c
            i=$((i + 1))
        done
        if [[ $q == '"' ]]; then
            inner=$(unescape_basic "$inner")
        fi
        local part
        local -a bits=()
        IFS=' ' read -r -a bits <<< "$inner"
        for part in "${bits[@]}"; do
            [[ -n $part ]] && dest+=("$part")
        done
        return
    fi
    if [[ $value == '['* ]]; then
        local in="" cur=""
        while (( i < n )); do
            c=${value:i:1}
            if [[ -n $in ]]; then
                if [[ $in == '"' && $c == "$bs" ]]; then
                    cur+=${value:i:2}
                    i=$((i + 2))
                    continue
                fi
                if [[ $c == "$in" ]]; then
                    if [[ $in == '"' ]]; then
                        dest+=("$(unescape_basic "$cur")")
                    else
                        dest+=("$cur")
                    fi
                    in=""
                    cur=""
                    i=$((i + 1))
                    continue
                fi
                cur+=$c
                i=$((i + 1))
                continue
            fi
            if [[ $c == '"' || $c == "'" ]]; then
                in=$c
                i=$((i + 1))
                continue
            fi
            if [[ $c == ']' ]]; then
                return
            fi
            i=$((i + 1))
        done
    fi
}

toml_value_closed() {
    local s=$1
    s=${s#"${s%%[![:space:]]*}"}
    local i=0 c n=${#s} depth=0 in=0
    if [[ $s == '"'* ]]; then
        i=1
        while (( i < n )); do
            c=${s:i:1}
            if [[ $c == "$bs" ]]; then
                i=$((i + 2))
                continue
            fi
            if [[ $c == '"' ]]; then
                return 0
            fi
            i=$((i + 1))
        done
        return 1
    fi
    if [[ $s == '['* ]]; then
        while (( i < n )); do
            c=${s:i:1}
            if (( in )); then
                if [[ $c == "$bs" ]]; then
                    i=$((i + 2))
                    continue
                fi
                if [[ $c == '"' ]]; then
                    in=0
                fi
                i=$((i + 1))
                continue
            fi
            if [[ $c == '"' ]]; then
                in=1
            elif [[ $c == '[' ]]; then
                depth=$((depth + 1))
            elif [[ $c == ']' ]]; then
                depth=$((depth - 1))
                if (( depth == 0 )); then
                    return 0
                fi
            fi
            i=$((i + 1))
        done
        return 1
    fi
    return 0
}

declare -gA target_cfg_cache=()

target_cfg_text() {
    local target=$1
    if [[ -z ${target_cfg_cache[$target]+x} ]]; then
        target_cfg_cache[$target]=$(rustc --print cfg --target "$target" 2>/dev/null || true)
    fi
    printf '%s\n' "${target_cfg_cache[$target]}"
}

cfg_has() {
    local cfgs=$1 key=$2 value=${3-} line
    if [[ -z $value ]]; then
        while IFS= read -r line; do
            [[ $line == "$key" ]] && return 0
        done <<<"$cfgs"
        return 1
    fi
    while IFS= read -r line; do
        [[ $line == "$key=\"$value\"" ]] && return 0
    done <<<"$cfgs"
    return 1
}

trim_ws() {
    local s=$1
    s=${s#"${s%%[![:space:]]*}"}
    s=${s%"${s##*[![:space:]]}"}
    printf '%s' "$s"
}

# Split EXPR on commas that are not inside (), quotes. Result in cfg_parts.
split_top_commas() {
    local s=$1 i=0 c depth=0 in="" cur=""
    local n=${#s}
    cfg_parts=()
    while (( i < n )); do
        c=${s:i:1}
        if [[ -n $in ]]; then
            cur+=$c
            if [[ $in == '"' && $c == "$bs" ]]; then
                i=$((i + 1))
                if (( i < n )); then
                    cur+=${s:i:1}
                fi
                i=$((i + 1))
                continue
            fi
            if [[ $c == "$in" ]]; then
                in=""
            fi
            i=$((i + 1))
            continue
        fi
        if [[ $c == '"' || $c == "'" ]]; then
            in=$c
            cur+=$c
            i=$((i + 1))
            continue
        fi
        if [[ $c == '(' ]]; then
            depth=$((depth + 1))
            cur+=$c
            i=$((i + 1))
            continue
        fi
        if [[ $c == ')' ]]; then
            depth=$((depth - 1))
            cur+=$c
            i=$((i + 1))
            continue
        fi
        if [[ $c == ',' && depth -eq 0 ]]; then
            cfg_parts+=("$cur")
            cur=""
            i=$((i + 1))
            continue
        fi
        cur+=$c
        i=$((i + 1))
    done
    cfg_parts+=("$cur")
}

# True when EXPR matches TARGET's `rustc --print cfg` list. Cargo uses that
# list for `target.'cfg(...)'` tables, without the rustflags added later.
cfg_eval() {
    local expr=$1 cfgs=$2
    expr=$(trim_ws "$expr")
    [[ -n $expr ]] || return 0
    local inner p
    local -a parts=()
    if [[ $expr == all\(*\) ]]; then
        inner=${expr#all(}
        inner=${inner%)}
        split_top_commas "$inner"
        parts=("${cfg_parts[@]}")
        for p in "${parts[@]}"; do
            cfg_eval "$(trim_ws "$p")" "$cfgs" || return 1
        done
        return 0
    fi
    if [[ $expr == any\(*\) ]]; then
        inner=${expr#any(}
        inner=${inner%)}
        split_top_commas "$inner"
        parts=("${cfg_parts[@]}")
        for p in "${parts[@]}"; do
            cfg_eval "$(trim_ws "$p")" "$cfgs" && return 0
        done
        return 1
    fi
    if [[ $expr == not\(*\) ]]; then
        inner=${expr#not(}
        inner=${inner%)}
        cfg_eval "$(trim_ws "$inner")" "$cfgs" && return 1
        return 0
    fi
    if [[ $expr =~ ^([A-Za-z0-9_]+)[[:space:]]*=[[:space:]]*\"([^\"]*)\"$ ]]; then
        cfg_has "$cfgs" "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}"
        return
    fi
    if [[ $expr =~ ^([A-Za-z0-9_]+)[[:space:]]*=[[:space:]]*\'([^\']*)\'$ ]]; then
        cfg_has "$cfgs" "${BASH_REMATCH[1]}" "${BASH_REMATCH[2]}"
        return
    fi
    if [[ $expr =~ ^[A-Za-z0-9_]+$ ]]; then
        cfg_has "$cfgs" "$expr"
        return
    fi
    return 1
}

# SPEC is a target triple or cfg(...), with one layer of quotes removed.
# Prints "specific" when Cargo would apply that table to TRIPLE.
spec_kind() {
    local spec=$1 triple=$2
    spec=$(trim_ws "$spec")
    if [[ $spec == \'*\' ]]; then
        spec=${spec:1:${#spec}-2}
    elif [[ $spec == \"*\" ]]; then
        spec=${spec:1:${#spec}-2}
    fi
    if [[ $spec == "$triple" ]]; then
        printf specific
        return
    fi
    if [[ $spec == cfg\(*\) ]]; then
        local inner=${spec#cfg(}
        inner=${inner%)}
        if cfg_eval "$(trim_ws "$inner")" "$(target_cfg_text "$triple")"; then
            printf specific
        fi
    fi
}

section_kind() {
    local section=$1 triple=$2
    section=${section%%#*}
    section=$(trim_ws "$section")
    if [[ $section == build ]]; then
        printf build
        return
    fi
    local name=${section#target.}
    [[ $name != "$section" ]] || return 0
    spec_kind "$name" "$triple"
}

# Start a rustflags value. KIND is build, specific, or empty.
begin_rustflags() {
    local kind=$1 value=$2
    [[ -n $kind ]] || return 0
    pending_kind=$kind
    if toml_value_closed "$value"; then
        take_rustflags "$kind" "$value"
        pending_kind=""
    else
        collecting=1
        buf=$value
    fi
}

parse_config_file() {
    local file=$1 triple=$2
    local section="" collecting=0 buf="" line pending_kind=""
    while IFS= read -r line || [[ -n $line ]]; do
        line=${line%%$'\r'}
        if (( collecting )); then
            buf+=$'\n'"$line"
            if toml_value_closed "$buf"; then
                take_rustflags "$pending_kind" "$buf"
                collecting=0
                buf=""
                pending_kind=""
            fi
            continue
        fi
        [[ $line =~ ^[[:space:]]*# ]] && continue
        if [[ $line =~ ^[[:space:]]*\[([^]]+)\] ]]; then
            section=${BASH_REMATCH[1]}
            continue
        fi
        if [[ $line =~ ^[[:space:]]*build\.rustflags[[:space:]]*=[[:space:]]*(.*)$ ]]; then
            begin_rustflags build "${BASH_REMATCH[1]}"
            continue
        fi
        if [[ $line =~ ^[[:space:]]*target\.(.*)\.rustflags[[:space:]]*=[[:space:]]*(.*)$ ]]; then
            begin_rustflags "$(spec_kind "${BASH_REMATCH[1]}" "$triple")" "${BASH_REMATCH[2]}"
            continue
        fi
        if [[ $line =~ ^[[:space:]]*rustflags[[:space:]]*=[[:space:]]*(.*)$ ]]; then
            begin_rustflags "$(section_kind "$section" "$triple")" "${BASH_REMATCH[1]}"
        fi
    done <"$file"
}

take_rustflags() {
    local kind=$1 value=$2
    [[ -n $kind ]] || return 0
    if [[ $kind == build ]]; then
        append_toml_rustflags build_args "$value"
    else
        append_toml_rustflags specific_args "$value"
    fi
}

# Cargo's config rustflags for TARGET, appended to `args`. $CARGO_HOME comes
# first, then ancestor `.cargo/config.toml` files from the filesystem root
# down to here. A matching target.<triple> or target.'cfg(...)' list replaces
# build.rustflags. Lists from several files are concatenated. Dotted keys
# (`build.rustflags`) are the same tables.
config_rustflags() {
    local target=$1
    local -a files=() build_args=() specific_args=()
    local home=${CARGO_HOME:-$HOME/.cargo}
    local dir ancestors=() i file
    if [[ -f $home/config.toml ]]; then
        files+=("$home/config.toml")
    elif [[ -f $home/config ]]; then
        files+=("$home/config")
    fi
    dir=$PWD
    while true; do
        ancestors+=("$dir")
        [[ $dir == / ]] && break
        dir=$(dirname "$dir")
    done
    i=${#ancestors[@]}
    while (( i > 0 )); do
        i=$((i - 1))
        dir=${ancestors[$i]}
        if [[ -f $dir/.cargo/config.toml ]]; then
            files+=("$dir/.cargo/config.toml")
        elif [[ -f $dir/.cargo/config ]]; then
            files+=("$dir/.cargo/config")
        fi
    done
    for file in "${files[@]}"; do
        parse_config_file "$file" "$target"
    done
    if (( ${#specific_args[@]} )); then
        args+=("${specific_args[@]}")
    elif (( ${#build_args[@]} )); then
        args+=("${build_args[@]}")
    fi
}

run_cargo() {
    local target=$1 extra=$2
    shift 2
    local var target_flags joined
    var="CARGO_TARGET_$(printf '%s' "$target" | tr 'a-z.-' 'A-Z__')_RUSTFLAGS"
    target_flags=${!var-}
    local -a args=()
    if [[ -v CARGO_ENCODED_RUSTFLAGS ]]; then
        local rest=${CARGO_ENCODED_RUSTFLAGS} piece
        while [[ $rest == *$'\x1f'* ]]; do
            piece=${rest%%$'\x1f'*}
            [[ -n $piece ]] && args+=("$piece")
            rest=${rest#*$'\x1f'}
        done
        [[ -n $rest ]] && args+=("$rest")
    elif [[ -v RUSTFLAGS ]]; then
        append_words "$RUSTFLAGS"
    elif [[ -n $target_flags ]]; then
        append_words "$target_flags"
    elif [[ -v CARGO_BUILD_RUSTFLAGS ]]; then
        append_words "$CARGO_BUILD_RUSTFLAGS"
    else
        config_rustflags "$target"
    fi
    append_words "$extra"
    if [[ ${#args[@]} -eq 0 ]]; then
        "$@"
        return
    fi
    # Unit separators keep an argument that contains a space intact. Cargo
    # splits RUSTFLAGS and the target variable on spaces, which would break
    # a config array element such as `-C link-arg=-Wl,foo bar`.
    local IFS=$'\x1f'
    joined="${args[*]}"
    env -u RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS -u "$var" \
        "CARGO_ENCODED_RUSTFLAGS=$joined" "$@"
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
# on a build that still raises `#UD`. Disassemble this build's objects.
reject_stmxcsr() {
    local rlib=$1
    local dir dump
    if ! command -v ar >/dev/null || ! command -v objdump >/dev/null; then
        echo "error: ar and objdump are required to check for stmxcsr" >&2
        exit 1
    fi
    dir=$(mktemp -d)
    dump=$(mktemp)
    # The EXIT trap stays in this subshell.
    (
        trap 'rm -rf "$dir" "$dump"' EXIT
        cd "$dir"
        if ! ar x "$rlib"; then
            echo "error: ar could not read $rlib" >&2
            exit 1
        fi
        shopt -s nullglob
        objs=(./*.o)
        if ((${#objs[@]} == 0)); then
            echo "error: $rlib contains no object file" >&2
            exit 1
        fi
        if ! objdump -d "${objs[@]}" >"$dump"; then
            echo "error: objdump failed on $rlib" >&2
            exit 1
        fi
        if grep -E -q '(^|[[:space:]])stmxcsr([[:space:]]|$)' "$dump"; then
            echo "error: $rlib emits stmxcsr" >&2
            exit 1
        fi
    )
}

# `x86_64-unknown-none` with no extra target features: portable backend,
# dalek `serial`, and no `stmxcsr`. The rows above build the SSE2 assembly
# backend instead.
no_sse2() {
    local target=x86_64-unknown-none
    local profile features json rlib
    for profile in dev release; do
        for features in "" wipe; do
            run_cargo "$target" "$custom $scalar" "${cargo[@]}" clippy -p rind --lib --locked \
                --target "$target" --profile "$profile" --features "$features" -- --deny warnings
        done
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
