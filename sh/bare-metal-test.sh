#!/usr/bin/env bash
# Drive sh/bare-metal.sh with a fake cargo and check the command list, the
# rustflags merge, and failure propagation. No toolchain and no network.
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
exit 0
EOF
chmod +x "$tmp/cargo"

run() {
    local record=$1
    shift
    mkdir -p "$record"
    env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS \
        PATH="$tmp:$PATH" RECORD_DIR="$record" \
        "$@"
}

args_of() {
    python3 - "$1" <<'PY'
import pathlib, sys
data = pathlib.Path(sys.argv[1]).read_bytes().split(b"\0")
if data and data[-1] == b"":
    data = data[:-1]
sys.stdout.write("\n".join(part.decode() for part in data))
PY
}

# The rustflags Cargo will actually read, with unit separators as spaces.
flags_of() {
    python3 - "$1" <<'PY'
import pathlib, sys
text = pathlib.Path(sys.argv[1]).read_text().splitlines()
for prefix in ("ENCODED=", "RUSTFLAGS=", "CARGO_BUILD_RUSTFLAGS="):
    for line in text:
        if line.startswith(prefix):
            sys.stdout.write(line[len(prefix):].replace("\x1f", " "))
            raise SystemExit
for line in text:
    if line.startswith("CARGO_TARGET_") and "_RUSTFLAGS=" in line:
        sys.stdout.write(line.split("=", 1)[1])
        break
PY
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

# Default path: eight targets, four clippy rows each, then four assembly
# builds, then one tree check.
# RUSTFLAGS outranks a target-scoped flag, so the target cpu does not merge
# in. Only x86_64-unknown-none gains dalek's serial backend and SSE2.
default=$tmp/default
if ! run "$default" env \
    RUSTFLAGS='-Cdebuginfo=0' \
    CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS='-Ctarget-cpu=generic' \
    "$script"; then
    echo "default path failed" >&2
    exit 1
fi
count=$(find "$default" -name '*.args' | wc -l)
if [[ $count -ne 37 ]]; then
    echo "default path ran $count commands, want 37" >&2
    exit 1
fi
i=0
while [[ $i -lt 32 ]]; do
    args=$(args_of "$default/$i.args")
    envf=$(cat "$default/$i.env")
    flags=$(flags_of "$default/$i.env")
    assert_has "$args" "clippy"
    assert_lacks "$args" "+esp"
    assert_has "$flags" "-Cdebuginfo=0"
    assert_has "$flags" 'getrandom_backend="custom"'
    assert_lacks_line "$envf" "ENCODED="
    assert_lacks "$flags" "target-cpu=generic"
    if [[ $args == *x86_64-unknown-none* ]]; then
        assert_has "$flags" 'curve25519_dalek_backend="serial"'
        assert_has "$flags" "target-feature=+sse,+sse2,-soft-float"
    else
        assert_lacks "$flags" "curve25519_dalek_backend"
        assert_lacks "$flags" "soft-float"
    fi
    i=$((i + 1))
done
arm_a=$(args_of "$default/32.args")
arm_r=$(args_of "$default/33.args")
arm64=$(args_of "$default/34.args")
x86=$(args_of "$default/35.args")
assert_has "$arm_a" "build"
assert_has "$arm_a" "armv7a-none-eabi"
assert_has "$(flags_of "$default/32.env")" 'getrandom_backend="custom"'
assert_has "$arm_r" "build"
assert_has "$arm_r" "armv7r-none-eabihf"
assert_has "$arm64" "aarch64-unknown-none"
assert_has "$x86" "x86_64-unknown-none"
assert_has "$(flags_of "$default/35.env")" "target-feature=+sse,+sse2,-soft-float"
tree_args=$(args_of "$default/36.args")
assert_has "$tree_args" "tree"
assert_has "$tree_args" "thumbv7em-none-eabihf"

# With no higher source, the target variable is the one Cargo reads, and
# this script appends its cfg there.
target_case=$tmp/target
run "$target_case" env \
    CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS='-Ctarget-cpu=generic' \
    "$script" >/dev/null
target_flags=$(flags_of "$target_case/0.env")
assert_has "$target_flags" "-Ctarget-cpu=generic"
assert_has "$target_flags" 'getrandom_backend="custom"'

# CARGO_BUILD_RUSTFLAGS is the source when nothing above it is set.
build_case=$tmp/build
run "$build_case" env \
    CARGO_BUILD_RUSTFLAGS='-Cdebuginfo=2' \
    "$script" >/dev/null
build_env=$(cat "$build_case/0.env")
assert_has "$build_env" "CARGO_BUILD_RUSTFLAGS="
assert_has "$(flags_of "$build_case/0.env")" "-Cdebuginfo=2"
assert_has "$(flags_of "$build_case/0.env")" 'getrandom_backend="custom"'
assert_lacks_line "$build_env" "RUSTFLAGS="

# Encoded flags outrank RUSTFLAGS. Cargo reads only the encoded source.
encoded_case=$tmp/encoded
run "$encoded_case" env \
    CARGO_ENCODED_RUSTFLAGS=$'-Cdebuginfo=1' \
    RUSTFLAGS='-Cdebuginfo=0' \
    CARGO_TARGET_THUMBV6M_NONE_EABI_RUSTFLAGS='-Ctarget-cpu=generic' \
    "$script" >/dev/null
first=$(flags_of "$encoded_case/0.env")
encoded_env=$(cat "$encoded_case/0.env")
assert_has "$first" "-Cdebuginfo=1"
assert_lacks "$first" "-Cdebuginfo=0"
assert_lacks "$first" "target-cpu=generic"
assert_has "$first" 'getrandom_backend="custom"'
assert_lacks_line "$encoded_env" "RUSTFLAGS="

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

# Xtensa: three bare-metal targets, four clippy rows each, four ESP-IDF
# checks, one bench build. ESP-IDF keeps getrandom's own backend.
xtensa=$tmp/xtensa
if ! run "$xtensa" env RUSTFLAGS='-Cdebuginfo=0' "$script" xtensa; then
    echo "xtensa path failed" >&2
    exit 1
fi
xcount=$(find "$xtensa" -name '*.args' | wc -l)
if [[ $xcount -ne 17 ]]; then
    echo "xtensa path ran $xcount commands, want 17" >&2
    exit 1
fi
i=0
while [[ $i -lt 12 ]]; do
    args=$(args_of "$xtensa/$i.args")
    flags=$(flags_of "$xtensa/$i.env")
    assert_has "$args" "+esp"
    assert_has "$args" "clippy"
    assert_has "$flags" "-Cdebuginfo=0"
    assert_has "$flags" 'getrandom_backend="custom"'
    assert_lacks "$flags" "curve25519_dalek_backend"
    i=$((i + 1))
done
while [[ $i -lt 17 ]]; do
    args=$(args_of "$xtensa/$i.args")
    flags=$(flags_of "$xtensa/$i.env")
    assert_has "$args" "+esp"
    assert_has "$flags" "-Cdebuginfo=0"
    assert_lacks "$flags" "getrandom_backend"
    i=$((i + 1))
done
assert_has "$(args_of "$xtensa/0.args")" "-Zbuild-std=core,alloc"
assert_has "$(args_of "$xtensa/0.args")" "xtensa-esp32-none-elf"
assert_has "$(args_of "$xtensa/4.args")" "xtensa-esp32s2-none-elf"
assert_has "$(args_of "$xtensa/12.args")" "-Zbuild-std=std,panic_abort"
assert_has "$(args_of "$xtensa/12.args")" "xtensa-esp32s3-espidf"
assert_has "$(args_of "$xtensa/12.args")" "check"
bench=$(args_of "$xtensa/16.args")
assert_has "$bench" "--benches"
assert_lacks "$bench" "--no-default-features"
assert_has "$bench" "rind-bench"

# Cargo keeps the quote characters when it splits on spaces. rustc requires them.
quote=$tmp/quote
run "$quote" env RUSTFLAGS='--cfg getrandom_backend="custom"' "$script" >/dev/null
qflags=$(flags_of "$quote/0.env")
assert_has "$qflags" '--cfg getrandom_backend="custom"'

echo "bare-metal-test: ok"
