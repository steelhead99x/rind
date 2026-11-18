#!/usr/bin/env bash
# Fails unless `cargo fmt` and `cargo clippy` run the toolchain the shell's
# `rustc` comes from. Cargo looks up `cargo-<subcommand>` in $CARGO_HOME/bin
# before PATH unless that directory is on PATH, so rustup's shims there shadow
# the dev shell's rustfmt and clippy, and a check runs another toolchain than
# CI's (UPSTREAM.md, "Cargo runs $CARGO_HOME/bin's subcommands before PATH's").
# `--self-test` runs the check against stub tools.
set -euo pipefail

# The build a Rust tool's --version names: its commit's first seven hex digits
# and its date. rustc prints nine digits and rustfmt and clippy ten, so only
# the prefix compares; a source-built rustc's trailing note is ignored.
build() {
    local stamp
    stamp=$(grep -oE '\([0-9a-f]{7,} [0-9]{4}-[0-9]{2}-[0-9]{2}\)' <<<"$1" | head -n 1) || true
    [[ -n "$stamp" ]] || return 0
    stamp=${stamp#(}
    stamp=${stamp%)}
    echo "${stamp:0:7} ${stamp##* }"
}

check() {
    local rustc want got tool status=0
    if ! rustc=$(rustc --version 2>/dev/null); then
        echo "error: \`rustc --version\` failed" >&2
        return 1
    fi
    want=$(build "$rustc")
    if [[ -z "$want" ]]; then
        echo "error: cannot read the build \`rustc --version\` names: $rustc" >&2
        return 1
    fi
    for tool in fmt clippy; do
        got=$(cargo "$tool" --version 2>/dev/null) || got="nothing (it failed)"
        if [[ "$(build "$got")" != "$want" ]]; then
            echo "error: \`cargo $tool --version\` reports $got, not the shell's $rustc" >&2
            status=1
        fi
    done
    if ((status)); then
        echo "       Cargo runs cargo-<subcommand> from ${CARGO_HOME:-\$HOME/.cargo}/bin before PATH, so" >&2
        echo "       rustup's shims there shadow the dev shell's tools. Remove them, put that" >&2
        echo "       directory on PATH after the dev shell's, or point CARGO_HOME at a directory" >&2
        echo "       whose bin/ holds none, or set ALLOW_HOST_TOOLCHAIN=1 to check anyway." >&2
    fi
    return "$status"
}

self_test() {
    local stubs out
    stubs=$(mktemp -d)
    # shellcheck disable=SC2064 # expand now: $stubs is local
    trap "rm -rf '$stubs'" RETURN
    cat >"$stubs/rustc" <<'EOF'
#!/usr/bin/env bash
[[ -n "${STUB_RUSTC-}" ]] || exit 1
echo "$STUB_RUSTC"
EOF
    cat >"$stubs/cargo" <<'EOF'
#!/usr/bin/env bash
case "$1" in
    fmt) [[ -n "${STUB_FMT-}" ]] || exit 1; echo "$STUB_FMT" ;;
    clippy) [[ -n "${STUB_CLIPPY-}" ]] || exit 1; echo "$STUB_CLIPPY" ;;
    *) exit 2 ;;
esac
EOF
    chmod +x "$stubs/rustc" "$stubs/cargo"

    # expect STATUS PATTERN RUSTC FMT CLIPPY: the check's exit status, and a
        # pattern its stderr must match (empty: must be empty).
    expect() {
        local want=$1 pattern=$2 status=0
        out=$(PATH="$stubs:$PATH" STUB_RUSTC=$3 STUB_FMT=$4 STUB_CLIPPY=$5 check 2>&1) || status=$?
        if ((status != want)); then
            echo "toolchain: self-test: rustc '$3', fmt '$4', clippy '$5' exited $status, want $want" >&2
            echo "$out" >&2
            exit 1
        fi
        # `||` and `&&` share precedence and associate left, so an ungrouped
        # trailing `&&` also runs when the pattern is empty, and `grep` of an
        # empty pattern matches any output. Group it so a success that prints
        # fails the test.
        if [[ -z "$pattern" && -n "$out" ]] || { [[ -n "$pattern" ]] && ! grep -qE -- "$pattern" <<<"$out"; }; then
            echo "toolchain: self-test: rustc '$3', fmt '$4', clippy '$5' printed:" >&2
            echo "$out" >&2
            echo "want ${pattern:-nothing}" >&2
            exit 1
        fi
    }

    local rustc='rustc 1.98.1 (48a229cea 2026-09-01)'
    local fmt='rustfmt 1.9.0-stable (48a229ceae 2026-09-01)'
    local clippy='clippy 0.1.98 (48a229ceae 2026-09-01)'
    expect 0 '' "$rustc" "$fmt" "$clippy"
    expect 0 '' 'rustc 1.98.1 (48a229cea 2026-09-01) (built from a source tarball)' "$fmt" "$clippy"
    # The Alienware's case: rustup's stable rustfmt and clippy in $CARGO_HOME/bin.
    expect 1 'cargo fmt --version` reports rustfmt 1\.11\.0-stable' \
        "$rustc" 'rustfmt 1.11.0-stable (0ef1bc3860 2026-11-09)' "$clippy"
    expect 1 'cargo clippy --version` reports clippy 0\.1\.100' \
        "$rustc" "$fmt" 'clippy 0.1.100 (0ef1bc3860 2026-11-09)'
    expect 1 'CARGO_HOME' "$rustc" "$fmt" 'clippy 0.1.100 (0ef1bc3860 2026-11-09)'
    # Same commit prefix, another day: a different build.
    expect 1 'cargo fmt' "$rustc" 'rustfmt 1.9.0-stable (48a229ceae 2026-09-02)' "$clippy"
    expect 1 'cargo clippy --version` reports nothing' "$rustc" "$fmt" ''
    expect 1 'rustc --version` failed' '' "$fmt" "$clippy"
    expect 1 'cannot read the build' 'rustc 1.98.1' "$fmt" "$clippy"
    echo "toolchain: self-test ok"
}

case "${1:-}" in
    "") check ;;
    --self-test) self_test ;;
    *)
        echo "usage: sh/toolchain.sh [--self-test]" >&2
        exit 2
        ;;
esac
