#!/usr/bin/env bash
# The matrix for mutants.yml.
#
# A pull request is split with cargo-mutants' `--shard k/n`, choosing n from
# `--list`'s count so each shard stays inside the 300-minute job. A nightly
# run mutates one day's changes and stays one job per architecture.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

# ML-DSA's pull request (moq-dev/rind#610) took 70 to 240 seconds a mutant
# on a hosted runner. Forty mutants at the slow end is 160 minutes, inside
# the 300-minute limit once the clean build and the unmutated baseline are
# counted. cargo-mutants' slice sharding gives each shard that many, and the
# last the remainder, with none empty (see shard_count).
per_shard=40
# A GitHub Actions matrix cannot hold more than 256 jobs.
max_jobs=256

usage() {
    echo "usage: sh/mutants-plan.sh nightly DIFF | pull-request DIFF | test" >&2
    exit 2
}

# diff: pass --in-diff. all: macOS DIT code, the whole files. skip: macOS
# diff does not touch that code, and the job exits before cargo-mutants.
scope_mode() {
    local diff=$1 name=$2
    if [ "$name" != macos ]; then
        echo diff
        return
    fi
    if grep -qE '^\+\+\+ b/rind/src/low/(aarch64/)?cpu\.rs$' "$diff"; then
        echo all
    else
        echo skip
    fi
}

shard_count() {
    local total=$1
    if [ "$total" -le "$per_shard" ]; then
        echo 1
        return
    fi
    echo $(( (total + per_shard - 1) / per_shard ))
}

arch_os() {
    case $1 in
        x86_64 | armv7) echo ubuntu-latest ;;
        aarch64) echo ubuntu-24.04-arm ;;
        macos) echo macos-latest ;;
        *) echo "sh/mutants-plan.sh: no arch $1" >&2; return 1 ;;
    esac
}

arch_shell() {
    case $1 in
        armv7) echo armv7 ;;
        *) echo default ;;
    esac
}

# Arguments the run passes to admin/mutants, ahead of --in-diff and --shard.
mutate_args() {
    case $1 in
        x86_64 | aarch64 | macos) echo --workspace ;;
        armv7) echo "--target armv7-unknown-linux-gnueabihf -p rind --features wipe" ;;
        *) echo "sh/mutants-plan.sh: no arch $1" >&2; return 1 ;;
    esac
}

count_mutants() {
    local name=$1 diff=$2 mode=$3
    if [ "$mode" = skip ]; then
        echo 0
        return
    fi
    local -a extra args
    read -ra extra <<<"$(mutate_args "$name")"
    # --campaign selects the same filters as --target or the host. Listing
    # does not need armv7's linker, which --target would ask for.
    args=(--campaign "$name")
    if [ "${extra[0]}" = --target ]; then
        args+=("${extra[@]:2}")
    else
        args+=("${extra[@]}")
    fi
    if [ "$mode" = diff ]; then
        args+=(--in-diff "$diff")
    fi
    args+=(--list)
    local bin out n
    bin=${MUTANTS_PLAN_ADMIN:-$root/admin/mutants}
    # Command substitution does not inherit `set -e`, and this function runs
    # inside one, so a failed listing must fail the function explicitly.
    # Counting the partial output would plan too few shards.
    if ! out=$("$bin" "${args[@]}"); then
        echo "sh/mutants-plan.sh: $bin --list failed for $name" >&2
        return 1
    fi
    n=$(printf '%s\n' "$out" | grep -cve '^$' || true)
    echo "$n"
}

# One JSON object per shard, then a single array on stdout.
emit() {
    local name=$1 os=$2 shell=$3 row_args=$4 shards=$5 in_diff=$6
    local k
    for ((k = 0; k < shards; k++)); do
        MUTANTS_ROW_NAME=$name \
            MUTANTS_ROW_OS=$os \
            MUTANTS_ROW_SHELL=$shell \
            MUTANTS_ROW_ARGS=$row_args \
            MUTANTS_ROW_SHARD=$k \
            MUTANTS_ROW_SHARDS=$shards \
            MUTANTS_ROW_IN_DIFF=$in_diff \
            python3 -c 'import json, os
print(json.dumps({
    "name": os.environ["MUTANTS_ROW_NAME"],
    "os": os.environ["MUTANTS_ROW_OS"],
    "shell": os.environ["MUTANTS_ROW_SHELL"],
    "args": os.environ["MUTANTS_ROW_ARGS"],
    "shard": int(os.environ["MUTANTS_ROW_SHARD"]),
    "shards": int(os.environ["MUTANTS_ROW_SHARDS"]),
    "in_diff": os.environ["MUTANTS_ROW_IN_DIFF"] == "true",
}))'
    done
}

matrix() {
    local diff=$1 list=$2
    local name mode count shards in_diff total=0 os shell args
    local -a rows=()
    for name in x86_64 aarch64 macos armv7; do
        mode=$(scope_mode "$diff" "$name")
        if [ "$list" = yes ] && [ "$mode" != skip ]; then
            # Checked explicitly: `set -e` is off when matrix runs as a
            # condition, and a nested substitution's status is dropped.
            count=$(count_mutants "$name" "$diff" "$mode") || return 1
            shards=$(shard_count "$count")
        else
            shards=1
        fi
        if [ "$mode" = diff ]; then
            in_diff=true
        else
            # `all` runs the macOS files whole. `skip` still takes a job,
            # which exits before cargo-mutants; in_diff tells it to.
            in_diff=true
            [ "$mode" != all ] || in_diff=false
        fi
        os=$(arch_os "$name")
        shell=$(arch_shell "$name")
        args=$(mutate_args "$name")
        total=$((total + shards))
        rows+=("$(emit "$name" "$os" "$shell" "$args" "$shards" "$in_diff")")
    done
    if [ "$total" -gt "$max_jobs" ]; then
        echo "sh/mutants-plan.sh: $total jobs exceeds GitHub's matrix limit of $max_jobs" >&2
        return 1
    fi
    printf '%s\n' "${rows[@]}" | python3 -c 'import json, sys
print(json.dumps([json.loads(line) for line in sys.stdin if line.strip()]))'
}

nightly() {
    matrix "$1" no
}

pull_request() {
    matrix "$1" yes
}

test_plan() {
    local tmp stub diff
    tmp=$(mktemp -d)
    stub=$tmp/admin
    cat >"$stub" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
campaign= in_diff=
while [ $# -gt 0 ]; do
    case "$1" in
        --campaign) campaign=$2; shift 2 ;;
        --in-diff) in_diff=yes; shift 2 ;;
        *) shift ;;
    esac
done
n=0
case "$campaign:$in_diff" in
    x86_64:yes) n=41 ;;
    aarch64:yes) n=80 ;;
    armv7:yes) n=1 ;;
    macos:) n=3 ;;
    *) n=0 ;;
esac
i=0
while [ "$i" -lt "$n" ]; do
    echo "mutant $campaign $i"
    i=$((i + 1))
done
EOF
    chmod +x "$stub"

    [ "$(shard_count 0)" = 1 ]
    [ "$(shard_count 40)" = 1 ]
    [ "$(shard_count 41)" = 2 ]
    [ "$(shard_count 1275)" = 32 ]
    [ "$(shard_count 1495)" = 38 ]

    diff=$tmp/empty.diff
    : >"$diff"
    [ "$(scope_mode "$diff" x86_64)" = diff ]
    [ "$(scope_mode "$diff" macos)" = skip ]
    printf '%s\n' '+++ b/rind/src/low/cpu.rs' >"$diff"
    [ "$(scope_mode "$diff" macos)" = all ]
    printf '%s\n' '+++ b/rind/src/low/aarch64/cpu.rs' >"$diff"
    [ "$(scope_mode "$diff" macos)" = all ]

    : >"$diff"
    MUTANTS_PLAN_ADMIN=$stub matrix "$diff" yes >"$tmp/pr.json"
    python3 - "$tmp/pr.json" <<'PY'
import json, sys
rows = json.load(open(sys.argv[1]))
by = {}
for row in rows:
    by.setdefault(row["name"], []).append(row)
assert [r["shard"] for r in by["x86_64"]] == [0, 1], by["x86_64"]
assert by["x86_64"][0]["shards"] == 2
assert by["x86_64"][0]["in_diff"] is True
assert by["x86_64"][0]["args"] == "--workspace"
assert [r["shard"] for r in by["aarch64"]] == [0, 1]
assert by["aarch64"][0]["os"] == "ubuntu-24.04-arm"
assert len(by["macos"]) == 1 and by["macos"][0]["in_diff"] is True
assert by["macos"][0]["shards"] == 1
assert len(by["armv7"]) == 1
assert by["armv7"][0]["shell"] == "armv7"
assert by["armv7"][0]["args"].startswith("--target armv7-")
assert "--features wipe" in by["armv7"][0]["args"]
print("pull-request matrix ok", len(rows))
PY

    printf '%s\n' '+++ b/rind/src/low/cpu.rs' >"$diff"
    MUTANTS_PLAN_ADMIN=$stub matrix "$diff" no >"$tmp/nightly.json"
    python3 - "$tmp/nightly.json" <<'PY'
import json, sys
rows = json.load(open(sys.argv[1]))
assert len(rows) == 4, rows
macos = [r for r in rows if r["name"] == "macos"][0]
assert macos["shards"] == 1 and macos["in_diff"] is False and macos["shard"] == 0
print("nightly matrix ok")
PY

    # One campaign of per_shard * max_jobs + 1 mutants needs max_jobs + 1
    # shards, which the matrix must refuse.
    cat >"$stub" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
campaign=
while [ $# -gt 0 ]; do
    case "$1" in
        --campaign) campaign=$2; shift 2 ;;
        *) shift ;;
    esac
done
if [ "$campaign" = x86_64 ]; then
    n=$((40 * 256 + 1))
    i=0
    while [ "$i" -lt "$n" ]; do
        echo m
        i=$((i + 1))
    done
fi
EOF
    chmod +x "$stub"
    : >"$diff"
    if MUTANTS_PLAN_ADMIN=$stub matrix "$diff" yes >/dev/null; then
        echo "sh/mutants-plan.sh: oversized matrix was accepted" >&2
        exit 1
    fi

    # A listing that fails, even after printing some mutants, must fail the
    # plan rather than fall back to one 300-minute shard.
    cat >"$stub" <<'EOF'
#!/usr/bin/env bash
campaign=
while [ $# -gt 0 ]; do
    case "$1" in
        --campaign) campaign=$2; shift 2 ;;
        *) shift ;;
    esac
done
echo m
if [ "$campaign" = aarch64 ]; then
    echo "admin/mutants: listing failed" >&2
    exit 1
fi
EOF
    chmod +x "$stub"
    : >"$diff"
    if MUTANTS_PLAN_ADMIN=$stub matrix "$diff" yes >/dev/null 2>&1; then
        echo "sh/mutants-plan.sh: failed listing was accepted" >&2
        exit 1
    fi
    if (MUTANTS_PLAN_ADMIN=$stub pull_request "$diff" >/dev/null 2>&1); then
        echo "sh/mutants-plan.sh: pull-request accepted a failed listing" >&2
        exit 1
    fi
    rm -rf "$tmp"
    echo "sh/mutants-plan.sh: tests passed"
}

case ${1:-} in
    nightly) [ $# -eq 2 ] || usage; nightly "$2" ;;
    pull-request) [ $# -eq 2 ] || usage; pull_request "$2" ;;
    test) [ $# -eq 1 ] || usage; test_plan ;;
    *) usage ;;
esac
