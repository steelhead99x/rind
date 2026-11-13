#!/usr/bin/env bash
# Compare admin/bench-report (Python) with rind-bench-report on the same inputs.
#
# Usage: sh/bench-parity.sh [DIR]
#
# With no DIR, checks this checkout: both `render --check` runs, then both
# `gate` runs on the fixture from admin/bench-report-test. DIR may be a
# benchmarks/data directory, a collect output directory, or a nightly artifact
# directory that contains bench-*/bench-results.json. A difference in stdout,
# stderr, exit status, or rendered files fails the script.
#
# First it runs rind-bench-report's tests that compare it with Python, which
# are ignored by a plain `cargo test`, since they need python3 (3.11 or later,
# for `tomllib`) and admin/bench-report.
set -euo pipefail

root=$(git rev-parse --show-toplevel)
cd "$root"
dir=${1:-}

if ! python3 -c 'import sys; sys.exit(sys.version_info < (3, 11))' 2>/dev/null; then
    echo "bench-parity: needs python3 3.11 or later on PATH" >&2
    exit 1
fi

cargo test -p rind-bench-report --locked --quiet -- --ignored
cargo build -p rind-bench-report --locked --quiet
bin=$root/target/debug/rind-bench-report
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

compare_streams() {
    local name=$1 py_code=$2 rs_code=$3
    if [[ $py_code -ne $rs_code ]]; then
        echo "bench-parity: $name exit status python=$py_code rust=$rs_code" >&2
        echo "--- python stderr ---" >&2
        cat "$work/py.err" >&2
        echo "--- rust stderr ---" >&2
        cat "$work/rs.err" >&2
        exit 1
    fi
    if ! cmp -s "$work/py.out" "$work/rs.out"; then
        echo "bench-parity: $name stdout differs" >&2
        diff -u "$work/py.out" "$work/rs.out" >&2 || true
        exit 1
    fi
    if ! cmp -s "$work/py.err" "$work/rs.err"; then
        echo "bench-parity: $name stderr differs" >&2
        diff -u "$work/py.err" "$work/rs.err" >&2 || true
        exit 1
    fi
}

run_both_here() {
    local name=$1
    shift
    local py rs
    set +e
    python3 "$root/admin/bench-report" "$@" >"$work/py.out" 2>"$work/py.err"
    py=$?
    "$bin" "$@" >"$work/rs.out" 2>"$work/rs.err"
    rs=$?
    set -e
    compare_streams "$name" "$py" "$rs"
}

run_both_in() {
    local name=$1 tree=$2
    shift 2
    local py rs
    set +e
    (cd "$tree" && python3 admin/bench-report "$@") >"$work/py.out" 2>"$work/py.err"
    py=$?
    (cd "$tree" && "$bin" "$@") >"$work/rs.out" 2>"$work/rs.err"
    rs=$?
    set -e
    compare_streams "$name" "$py" "$rs"
}

stage_tree() {
    local dest=$1 data=$2
    mkdir -p "$dest/admin" "$dest/benchmarks/data" "$dest/quest"
    cp "$root/admin/bench-report" "$dest/admin/bench-report"
    cp "$root/benchmarks/verified.toml" "$root/benchmarks/gaps.toml" "$dest/benchmarks/"
    cp -a "$root/quest/." "$dest/quest/"
    local json
    while IFS= read -r -d '' json; do
        cp "$json" "$dest/benchmarks/data/$(basename "$json")"
    done < <(find "$data" -name '*.json' -print0)
}

checkout_mode=0
if [[ -z $dir || $dir == benchmarks/data || $dir == "$root/benchmarks/data" ]]; then
    checkout_mode=1
fi

if [[ $checkout_mode -eq 1 ]]; then
    run_both_here "render --check" render --check
    run_both_here "summary" summary "$root/benchmarks/data"
    fixture=$work/gate
    mkdir -p "$fixture/admin" "$fixture/benchmarks" "$fixture/now/bench-x" "$fixture/then/bench-x" "$fixture/quest"
    cp "$root/admin/bench-report" "$fixture/admin/bench-report"
    printf '%s\n' '[[gap]]' 'operations = ["sha256/*"]' 'on = ["x86_64"]' 'reason = "r"' >"$fixture/benchmarks/gaps.toml"
    python3 - "$fixture" <<'PY'
import json, os, sys
base = sys.argv[1]

def write(path, sha, chacha, avx):
    os.makedirs(path, exist_ok=True)
    saved = {
        "target": "x86_64-unknown-linux-gnu",
        "portable": False,
        "tier": "",
        "cpu": "c",
        "avx512": avx,
        "results": [
            {"id": "sha256/rind/64B", "ns": sha},
            {"id": "sha256/ring/64B", "ns": 80.0},
            {"id": "chacha20poly1305/rind/32B", "ns": chacha},
            {"id": "chacha20poly1305/aws-lc-rs/32B", "ns": 80.0},
            {"id": "x25519-ecdh/rind", "ns": 1.0},
        ],
    }
    with open(os.path.join(path, "bench-results.json"), "w") as handle:
        json.dump(saved, handle)

write(os.path.join(base, "now", "bench-x"), 100.0, 100.0, True)
write(os.path.join(base, "then", "bench-x"), 100.0, 80.0, False)
PY
    run_both_in "gate fixture" "$fixture" gate now --previous "then"
fi

if [[ $checkout_mode -eq 0 ]]; then
    py_tree=$work/py-tree
    rs_tree=$work/rs-tree
    stage_tree "$py_tree" "$dir"
    stage_tree "$rs_tree" "$dir"
    set +e
    (cd "$py_tree" && python3 admin/bench-report render) >"$work/py.out" 2>"$work/py.err"
    py=$?
    (cd "$rs_tree" && "$bin" render) >"$work/rs.out" 2>"$work/rs.err"
    rs=$?
    set -e
    compare_streams "render $dir" "$py" "$rs"
    run_both_here "summary $dir" summary "$dir"
    if [[ $py -eq 0 ]]; then
        if ! diff -rq "$py_tree/BENCHMARKS.md" "$rs_tree/BENCHMARKS.md" >"$work/diff" \
            || ! diff -rq "$py_tree/benchmarks" "$rs_tree/benchmarks" >>"$work/diff"; then
            echo "bench-parity: rendered files differ" >&2
            cat "$work/diff" >&2
            exit 1
        fi
    fi
    if find "$dir" -name bench-results.json -print -quit | grep -q .; then
        gate_tree=$work/gate-tree
        mkdir -p "$gate_tree/admin" "$gate_tree/benchmarks" "$gate_tree/quest"
        cp "$root/admin/bench-report" "$gate_tree/admin/bench-report"
        cp "$root/benchmarks/gaps.toml" "$gate_tree/benchmarks/gaps.toml"
        cp -a "$dir/." "$gate_tree/artifacts"
        run_both_in "gate $dir" "$gate_tree" gate artifacts
    fi
fi

echo "bench-parity: python and rust match"
