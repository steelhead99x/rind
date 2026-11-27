#!/usr/bin/env bash
# Drive sh/bare-metal.sh with a fake cargo and check the command list, that
# the caller's rustflags are left alone, and that failure still propagates.
# That part needs no toolchain and no network. When cargo and rustc are
# installed, a later probe checks that Cargo's own config reaches the build
# and that the wrapper's cfg is added on top. Bash only.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
script=$root/sh/bare-metal.sh
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

cat >"$tmp/cargo" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
dir=${RECORD_DIR:?}
n=0
while [[ -e $dir/$n.args ]]; do
    n=$((n + 1))
done
out=$dir/$n
# shellcheck disable=SC2216 # Record argv unchanged, including empty arguments.
printf '%s\0' "$@" >"$out.args"
{
    if [[ -v RUSTFLAGS ]]; then
        printf 'RUSTFLAGS=%s\n' "$RUSTFLAGS"
    fi
    if [[ -v CARGO_ENCODED_RUSTFLAGS ]]; then
        printf 'ENCODED=%s\n' "$CARGO_ENCODED_RUSTFLAGS"
    fi
    if [[ -v CARGO_BUILD_RUSTFLAGS ]]; then
        printf 'CARGO_BUILD_RUSTFLAGS=%s\n' "$CARGO_BUILD_RUSTFLAGS"
    fi
    if [[ -v RIND_BARE_METAL_RUSTFLAGS ]]; then
        printf 'SCRIPT=%s\n' "$RIND_BARE_METAL_RUSTFLAGS"
    fi
    if [[ -v RUSTC_WRAPPER ]]; then
        printf 'WRAPPER=%s\n' "$RUSTC_WRAPPER"
    fi
    if [[ -v RIND_BARE_METAL_INNER_WRAPPER ]]; then
        printf 'INNER=%s\n' "$RIND_BARE_METAL_INNER_WRAPPER"
    fi
    if [[ -v CARGO_TARGET_DIR ]]; then
        printf 'TARGET_DIR=%s\n' "$CARGO_TARGET_DIR"
    fi
    env | grep '^CARGO_TARGET_.*_RUSTFLAGS=' || true
} >"$out.env"
if [[ ${FAIL_CARGO:-} == 1 ]]; then
    exit 1
fi
if [[ ${FAIL_TREE:-} != "" ]] && [[ $* == *tree* ]]; then
    exit "$FAIL_TREE"
fi
if [[ ${PRINT_AWS:-} == 1 && $* == *tree* ]]; then
    printf '%s\n' 'aws-lc-rs v1.0.0'
fi
# The no-SSE2 build disassembles the rlib named in this invocation's JSON.
# An empty file is not an object archive, so leave a real one with no
# stmxcsr instruction.
if [[ $* == *--message-format=json* && $* == *build* && $* == *x86_64-unknown-none* ]]; then
    lib=${CARGO_TARGET_DIR:-target}/x86_64-unknown-none/debug
    mkdir -p "$lib"
    printf '.text\n' | as -o "$lib/empty.o"
    ar cr "$lib/librind.rlib" "$lib/empty.o"
    rm -f "$lib/empty.o"
    printf '%s\n' "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"rind\",\"kind\":[\"lib\"]},\"filenames\":[\"$lib/librind.rlib\"]}"
fi
exit 0
EOF
chmod +x "$tmp/cargo"

run() {
    local record=$1
    shift
    mkdir -p "$record/cargo-home"
    # An empty CARGO_HOME keeps a developer config out of the command list.
    # A caller can override it with `env CARGO_HOME=...`.
    # Drop a developer rustc wrapper too, so the recorded chain is this
    # test's. A case that wants one sets it in the command.
    env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u RUSTC_WRAPPER \
        CARGO_HOME="$record/cargo-home" \
        CARGO_TARGET_DIR="$record/target" \
        PATH="$tmp:$PATH" RECORD_DIR="$record" \
        "$@"
}

args_of() {
    local part
    while IFS= read -r -d '' part || [[ -n $part ]]; do
        printf '%s\n' "$part"
    done <"$1"
}

# The caller's rustflags, left untouched. Unit separators print as spaces.
flags_of() {
    local line val
    while IFS= read -r line; do
        case $line in
            ENCODED=* | RUSTFLAGS=* | CARGO_BUILD_RUSTFLAGS=*)
                val=${line#*=}
                printf '%s' "${val//$'\x1f'/ }"
                return
                ;;
        esac
    done <"$1"
    while IFS= read -r line; do
        case $line in
            CARGO_TARGET_*_RUSTFLAGS=*)
                printf '%s' "${line#*=}"
                return
                ;;
        esac
    done <"$1"
}

target_dir_of() {
    local line
    while IFS= read -r line; do
        if [[ $line == TARGET_DIR=* ]]; then
            printf '%s' "${line#TARGET_DIR=}"
            return
        fi
    done <"$1"
}

# Flags this script adds, through the wrapper, on top of Cargo's source.
script_flags() {
    local line
    while IFS= read -r line; do
        if [[ $line == SCRIPT=* ]]; then
            printf '%s' "${line#SCRIPT=}"
            return
        fi
    done <"$1"
}

assert_has() {
    local haystack=$1 needle=$2
    if [[ $haystack != *"$needle"* ]]; then
        echo "missing [$needle] in [$haystack]" >&2
        exit 1
    fi
}

assert_lacks() {
    local haystack=$1 needle=$2
    if [[ $haystack == *"$needle"* ]]; then
        echo "unexpected [$needle] in [$haystack]" >&2
        exit 1
    fi
}

assert_lacks_line() {
    local haystack=$1 prefix=$2
    local line
    while IFS= read -r line; do
        if [[ $line == "$prefix"* ]]; then
            echo "unexpected line [$line]" >&2
            exit 1
        fi
    done <<<"$haystack"
}

# Unknown arguments fail before cargo runs.
if run "$tmp/bad" "$script" foo; then
    echo "expected usage failure" >&2
    exit 1
fi
if [[ -e $tmp/bad/0.args ]]; then
    echo "usage failure invoked cargo" >&2
    exit 1
fi

# Default path: eight targets, two clippy rows each, then the one assembly
# build, SSE2 x86_64 (the arm and aarch64 `none` targets are portable),
# then the no-SSE2 x86_64 rows (two clippy and one build), then two tree
# checks: thumbv7em-none-eabihf, then armv7a-none-eabi. The caller's
# RUSTFLAGS and target variable stay as they were.
# This script's flags go to the wrapper. Only x86_64-unknown-none gains SSE2.
default=$tmp/default
if ! run "$default" env \
    RUSTFLAGS='-Cdebuginfo=0' \
    CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS='-Ctarget-cpu=generic' \
    "$script"; then
    echo "default path failed" >&2
    exit 1
fi
count=$(find "$default" -name '*.args' | wc -l)
if [[ $count -ne 22 ]]; then
    echo "default path ran $count commands, want 22" >&2
    exit 1
fi
i=0
while [[ $i -lt 16 ]]; do
    args=$(args_of "$default/$i.args")
    caller=$(flags_of "$default/$i.env")
    added=$(script_flags "$default/$i.env")
    envfile=$(cat "$default/$i.env")
    assert_has "$args" "clippy"
    assert_lacks "$args" "+esp"
    # `--target` and `--profile` are cargo's, so they precede rustc's `--`.
    assert_has "$args" "--profile"
    profile_at=$(grep -n '^--profile$' <<<"$args" | head -1 | cut -d: -f1)
    dash_at=$(grep -n '^--$' <<<"$args" | head -1 | cut -d: -f1)
    if [[ -z $dash_at || $profile_at -gt $dash_at ]]; then
        echo "--profile follows -- in [$args]" >&2
        exit 1
    fi
    assert_has "$caller" "-Cdebuginfo=0"
    assert_lacks "$caller" "getrandom_backend"
    assert_has "$added" 'getrandom_backend="custom"'
    assert_lacks "$added" "target-cpu=generic"
    assert_lacks "$added" "curve25519_dalek_backend"
    assert_has "$envfile" "CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS=-Ctarget-cpu=generic"
    assert_has "$envfile" "bare-metal-rustc"
    assert_lacks_line "$envfile" "ENCODED="
    if [[ $args == *x86_64-unknown-none* ]]; then
        assert_has "$added" "target-feature=+sse,+sse2,-soft-float"
    else
        assert_lacks "$added" "soft-float"
    fi
    i=$((i + 1))
done
x86=$(args_of "$default/16.args")
assert_has "$x86" "build"
assert_has "$x86" "x86_64-unknown-none"
assert_has "$(script_flags "$default/16.env")" 'getrandom_backend="custom"'
assert_has "$(script_flags "$default/16.env")" "target-feature=+sse,+sse2,-soft-float"
nosse=$(args_of "$default/17.args")
assert_has "$nosse" "clippy"
assert_has "$nosse" "x86_64-unknown-none"
nosse_flags=$(script_flags "$default/17.env")
assert_has "$nosse_flags" 'curve25519_dalek_backend="serial"'
assert_lacks "$nosse_flags" "soft-float"
nosse_build=$(args_of "$default/19.args")
assert_has "$nosse_build" "build"
assert_has "$nosse_build" "x86_64-unknown-none"
tree_args=$(args_of "$default/20.args")
assert_has "$tree_args" "tree"
assert_has "$tree_args" "thumbv7em-none-eabihf"
arm_tree=$(args_of "$default/21.args")
assert_has "$arm_tree" "tree"
assert_has "$arm_tree" "armv7a-none-eabi"
# Cargo does not fingerprint wrapper flags. Each flag set gets its own
# target dir, so a later row cannot reuse an earlier build script.
thumb_dir=$(target_dir_of "$default/0.env")
if [[ $thumb_dir != "$(target_dir_of "$default/2.env")" \
    || $thumb_dir == "$(target_dir_of "$default/14.env")" \
    || $(target_dir_of "$default/14.env") == "$(target_dir_of "$default/17.env")" ]]; then
    echo "flag sets shared a target dir" >&2
    exit 1
fi

# A target-scoped variable stays set. Cargo reads it when nothing outranks
# it. This script does not copy it into the wrapper flags.
target_case=$tmp/target
run "$target_case" env \
    CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS='-Ctarget-cpu=generic' \
    "$script" >/dev/null
target_env=$(cat "$target_case/0.env")
assert_has "$target_env" "CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS=-Ctarget-cpu=generic"
assert_has "$(script_flags "$target_case/0.env")" 'getrandom_backend="custom"'
assert_lacks "$(script_flags "$target_case/0.env")" "target-cpu=generic"
assert_lacks_line "$target_env" "ENCODED="

# CARGO_BUILD_RUSTFLAGS stays set. The wrapper still carries the cfg.
build_case=$tmp/build
run "$build_case" env \
    CARGO_BUILD_RUSTFLAGS='-Cdebuginfo=2' \
    "$script" >/dev/null
build_env=$(cat "$build_case/0.env")
assert_has "$build_env" "CARGO_BUILD_RUSTFLAGS=-Cdebuginfo=2"
assert_has "$(script_flags "$build_case/0.env")" 'getrandom_backend="custom"'
assert_lacks_line "$build_env" "ENCODED="
assert_lacks_line "$build_env" "RUSTFLAGS="

# Encoded flags stay encoded. RUSTFLAGS and the target variable stay too.
# Cargo prefers the encoded source; the wrapper still adds the cfg.
encoded_case=$tmp/encoded
run "$encoded_case" env \
    CARGO_ENCODED_RUSTFLAGS=$'-Cdebuginfo=1' \
    RUSTFLAGS='-Cdebuginfo=0' \
    CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS='-Ctarget-cpu=generic' \
    "$script" >/dev/null
encoded_env=$(cat "$encoded_case/0.env")
assert_has "$encoded_env" "ENCODED=-Cdebuginfo=1"
assert_has "$encoded_env" "RUSTFLAGS=-Cdebuginfo=0"
assert_has "$encoded_env" "CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS=-Ctarget-cpu=generic"
assert_has "$(script_flags "$encoded_case/0.env")" 'getrandom_backend="custom"'
assert_lacks "$(script_flags "$encoded_case/0.env")" "debuginfo"

# A failing cargo stops the script on that call.
fail=$tmp/fail
if run "$fail" env FAIL_CARGO=1 "$script"; then
    echo "expected cargo failure" >&2
    exit 1
fi
fail_count=$(find "$fail" -name '*.args' | wc -l)
if [[ $fail_count -ne 1 ]]; then
    echo "cargo failure continued ($fail_count calls)" >&2
    exit 1
fi

# cargo tree's own failure is not swallowed by the assignment.
treefail=$tmp/treefail
if run "$treefail" env FAIL_TREE=3 "$script"; then
    echo "expected tree failure" >&2
    exit 1
fi

# aws-lc in the tree is an error.
aws=$tmp/aws
if run "$aws" env PRINT_AWS=1 "$script"; then
    echo "expected aws-lc dependency failure" >&2
    exit 1
fi

# Xtensa: three bare-metal targets, two clippy rows each, two ESP-IDF
# checks, one bench build. ESP-IDF keeps getrandom's own backend.
xtensa=$tmp/xtensa
if ! run "$xtensa" env RUSTFLAGS='-Cdebuginfo=0' "$script" xtensa; then
    echo "xtensa path failed" >&2
    exit 1
fi
xcount=$(find "$xtensa" -name '*.args' | wc -l)
if [[ $xcount -ne 9 ]]; then
    echo "xtensa path ran $xcount commands, want 9" >&2
    exit 1
fi
i=0
while [[ $i -lt 6 ]]; do
    args=$(args_of "$xtensa/$i.args")
    caller=$(flags_of "$xtensa/$i.env")
    added=$(script_flags "$xtensa/$i.env")
    assert_has "$args" "+esp"
    assert_has "$args" "clippy"
    profile_at=$(grep -n '^--profile$' <<<"$args" | head -1 | cut -d: -f1)
    dash_at=$(grep -n '^--$' <<<"$args" | head -1 | cut -d: -f1)
    if [[ -z $dash_at || $profile_at -gt $dash_at ]]; then
        echo "--profile follows -- in [$args]" >&2
        exit 1
    fi
    assert_has "$caller" "-Cdebuginfo=0"
    assert_lacks "$caller" "getrandom_backend"
    assert_has "$added" 'getrandom_backend="custom"'
    assert_lacks "$added" "curve25519_dalek_backend"
    assert_has "$(cat "$xtensa/$i.env")" "bare-metal-rustc"
    i=$((i + 1))
done
while [[ $i -lt 9 ]]; do
    args=$(args_of "$xtensa/$i.args")
    caller=$(flags_of "$xtensa/$i.env")
    added=$(script_flags "$xtensa/$i.env")
    assert_has "$args" "+esp"
    assert_has "$caller" "-Cdebuginfo=0"
    assert_lacks "$added" "getrandom_backend"
    i=$((i + 1))
done
if [[ $(target_dir_of "$xtensa/0.env") == "$(target_dir_of "$xtensa/6.env")" ]]; then
    echo "xtensa flag sets shared a target dir" >&2
    exit 1
fi
assert_has "$(args_of "$xtensa/0.args")" "-Zbuild-std=core,alloc"
assert_has "$(args_of "$xtensa/0.args")" "xtensa-esp32-none-elf"
assert_has "$(args_of "$xtensa/2.args")" "xtensa-esp32s2-none-elf"
assert_has "$(args_of "$xtensa/6.args")" "-Zbuild-std=std,panic_abort"
assert_has "$(args_of "$xtensa/6.args")" "xtensa-esp32s3-espidf"
assert_has "$(args_of "$xtensa/6.args")" "check"
bench=$(args_of "$xtensa/8.args")
assert_has "$bench" "--benches"
assert_lacks "$bench" "--no-default-features"
assert_has "$bench" "rind-bench"

# Quote characters stay in the token. rustc requires them, and the wrapper
# splits on spaces the same way.
quote=$tmp/quote
run "$quote" env RUSTFLAGS='--cfg getrandom_backend="custom"' "$script" >/dev/null
assert_has "$(flags_of "$quote/0.env")" '--cfg getrandom_backend="custom"'
assert_has "$(script_flags "$quote/0.env")" 'getrandom_backend="custom"'

wrapper=$root/sh/bare-metal-rustc
nul_fields() {
    local part
    while IFS= read -r -d '' part || [[ -n $part ]]; do
        printf '%s\n' "$part"
    done
}
host_fields=$(
    RIND_BARE_METAL_WRAPPER_DRY=1 \
        RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
        "$wrapper" rustc --crate-name probe | nul_fields
)
assert_lacks "$host_fields" "getrandom_backend"
target_fields=$(
    RIND_BARE_METAL_WRAPPER_DRY=1 \
        RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom" -C link-arg=-Wl,foo' \
        "$wrapper" rustc --target thumbv6m-none-eabi --crate-name probe | nul_fields
)
assert_has "$target_fields" 'getrandom_backend="custom"'
eq_fields=$(
    RIND_BARE_METAL_WRAPPER_DRY=1 \
        RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
        "$wrapper" rustc --target=thumbv6m-none-eabi | nul_fields
)
assert_has "$eq_fields" "--target=thumbv6m-none-eabi"
assert_has "$eq_fields" 'getrandom_backend="custom"'

# A caller-supplied RUSTC_WRAPPER stays in the chain. This script appends
# its flags, then that wrapper runs. Dry mode still only prints the argv.
caller=$tmp/caller-wrapper
cat >"$caller" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$RUSTC_WRAPPER" >"${CALLER_SEEN:?}"
printf '%s\0' "$@" >"${CALLER_ARGV:?}"
printf 'caller-ran\n' >>"${CALLER_LOG:?}"
exit 0
EOF
chmod +x "$caller"
direct=$tmp/direct-chain
mkdir -p "$direct"
CALLER_ARGV=$direct/argv CALLER_LOG=$direct/log CALLER_SEEN=$direct/seen \
    RIND_BARE_METAL_INNER_WRAPPER=$caller \
    RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
    "$wrapper" rustc --crate-name rind --target thumbv6m-none-eabi
assert_has "$(cat "$direct/log")" "caller-ran"
assert_has "$(cat "$direct/seen")" "$caller"
direct_fields=$(nul_fields <"$direct/argv")
assert_has "$direct_fields" "rustc"
assert_has "$direct_fields" "--target"
assert_has "$direct_fields" "thumbv6m-none-eabi"
assert_has "$direct_fields" 'getrandom_backend="custom"'
dry_log=$tmp/dry-skips-inner.log
dry_seen=$tmp/dry-skips-inner.seen
dry_fields=$(
    RIND_BARE_METAL_INNER_WRAPPER=$caller \
        RIND_BARE_METAL_WRAPPER_DRY=1 \
        RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
        CALLER_ARGV=$tmp/unused-argv CALLER_LOG=$dry_log CALLER_SEEN=$dry_seen \
        "$wrapper" rustc --target thumbv6m-none-eabi | nul_fields
)
assert_has "$dry_fields" 'getrandom_backend="custom"'
if [[ -e $dry_log || -e $dry_seen ]]; then
    echo "dry run called the inner wrapper" >&2
    exit 1
fi
chain=$tmp/chain
if ! run "$chain" env RUSTC_WRAPPER="$caller" "$script" >/dev/null; then
    echo "wrapper chain path failed" >&2
    exit 1
fi
chain_env=$(cat "$chain/0.env")
assert_has "$chain_env" "bare-metal-rustc"
assert_has "$chain_env" "INNER=$caller"
if ! grep -qx 'INNER=' "$default/0.env"; then
    echo "empty caller wrapper was recorded as [$(grep '^INNER=' "$default/0.env")]" >&2
    exit 1
fi

# Cargo's own config, including forms a hand parser drops, reaches the
# build. The wrapper's cfg is on top of whichever source Cargo chose.
# Skipped when this job has no cargo yet (the Xtensa workflow runs this
# before the toolchain action).
if command -v cargo >/dev/null && command -v rustc >/dev/null; then
    host=$(rustc -vV | awk '/^host: / { print $2 }')
    os=$(rustc --print cfg --target "$host" | sed -n 's/^target_os="\(.*\)"$/\1/p')
    arch=$(rustc --print cfg --target "$host" | sed -n 's/^target_arch="\(.*\)"$/\1/p')
    upper=$(printf '%s' "$host" | tr 'a-z.-' 'A-Z__')
    probe=$tmp/probe
    mkdir -p "$probe/src"
    cat >"$probe/Cargo.toml" <<'EOF'
[package]
name = "flagprobe"
version = "0.0.0"
edition = "2021"
EOF
    cat >"$probe/src/lib.rs" <<'EOF'
pub fn x() {}
EOF
    cat >"$probe/build.rs" <<'EOF'
fn show(name: &str) {
    match std::env::var(name) {
        Ok(value) => println!("cargo:warning=PROBE {name}={value}"),
        Err(_) => println!("cargo:warning=PROBE {name}=unset"),
    }
}
fn main() {
    show("CARGO_CFG_FROM_TRIPLE");
    show("CARGO_CFG_FROM_INLINE");
    show("CARGO_CFG_FROM_INCLUDE");
    show("CARGO_CFG_FROM_CFG");
    show("CARGO_CFG_BRACKET");
    show("CARGO_CFG_HASH");
    show("CARGO_CFG_SPACED");
    show("CARGO_CFG_GETRANDOM_BACKEND");
}
EOF
    mkdir -p "$probe/.cargo"
    cat >"$probe/.cargo/more.toml" <<'EOF'
[build]
rustflags = ["--cfg", 'from_include="1"']
EOF
    cat >"$probe/.cargo/config.toml" <<EOF
include = ["more.toml"]

[target.$host]
rustflags = [
    "--cfg", 'from_triple="1"',
    "--cfg", 'bracket="]"',
    "--cfg", 'hash="#"',
    "--cfg", 'spaced="a b"',
]
EOF
    log=$probe/triple.log
    (
        cd "$probe"
        env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            -u "CARGO_TARGET_${upper}_RUSTFLAGS" \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-triple" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            RIND_BARE_METAL_WRAPPER_LOG="$probe/wrap.log" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_TRIPLE=1"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_BRACKET=]"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_HASH=#"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"
    # A triple table replaces build.rustflags and cfg() tables.
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INCLUDE=unset"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_CFG=unset"
    wraplog=$(nul_fields <"$probe/wrap.log")
    assert_has "$wraplog" 'getrandom_backend="custom"'
    # A space inside one rustflags element stays one rustc argument.
    assert_has "$wraplog" 'spaced="a b"'
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_SPACED=a b"

    # An inline target table is config Cargo parses. The wrapper does not.
    cat >"$probe/.cargo/config.toml" <<EOF
target = { "$host" = { rustflags = ["--cfg", 'from_inline="1"'] } }
EOF
    log=$probe/inline.log
    (
        cd "$probe"
        env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            -u "CARGO_TARGET_${upper}_RUSTFLAGS" \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-inline" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INLINE=1"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"

    # A matching cfg() table is evaluated by rustc. It replaces
    # build.rustflags, the same way a triple table does.
    cat >"$probe/.cargo/config.toml" <<EOF
[target.'cfg(all(target_os = "$os", target_arch = "$arch"))']
rustflags = ["--cfg", 'from_cfg="1"']
EOF
    log=$probe/cfg.log
    (
        cd "$probe"
        env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            -u "CARGO_TARGET_${upper}_RUSTFLAGS" \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-cfg" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_CFG=1"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INCLUDE=unset"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"

    # An include supplies build.rustflags when no target table replaces it.
    cat >"$probe/.cargo/config.toml" <<'EOF'
include = ["more.toml"]
EOF
    log=$probe/include.log
    (
        cd "$probe"
        env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            -u "CARGO_TARGET_${upper}_RUSTFLAGS" \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-include" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INCLUDE=1"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"

    # RUSTFLAGS outranks config. The wrapper flag is still present.
    log=$probe/rustflags.log
    (
        cd "$probe"
        env -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            -u "CARGO_TARGET_${upper}_RUSTFLAGS" \
            RUSTFLAGS='-Cdebuginfo=0' \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-rustflags" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INCLUDE=unset"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"

    # Cargo treats an empty target variable as unset, so config still applies.
    # A non-empty one replaces config. The wrapper adds its cfg either way.
    log=$probe/empty.log
    (
        cd "$probe"
        env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            "CARGO_TARGET_${upper}_RUSTFLAGS=" \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-empty" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INCLUDE=1"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"
    log=$probe/targetvar.log
    (
        cd "$probe"
        env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS \
            "CARGO_TARGET_${upper}_RUSTFLAGS=-Cdebuginfo=1" \
            CARGO_HOME="$probe/empty-home" \
            CARGO_TARGET_DIR="$probe/target-var" \
            RIND_BARE_METAL_RUSTFLAGS='--cfg getrandom_backend="custom"' \
            RUSTC_WRAPPER="$wrapper" \
            cargo build --offline --lib --target "$host" >"$log" 2>&1
    ) || {
        echo "probe failed" >&2
        cat "$log" >&2
        exit 1
    }
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_FROM_INCLUDE=unset"
    assert_has "$(cat "$log")" "PROBE CARGO_CFG_GETRANDOM_BACKEND=custom"
fi

echo "bare-metal-test: ok"
