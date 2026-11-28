#!/usr/bin/env bash
# The Lean replays that block fork PRs, on a host that can fetch the pinned
# toolchain (cache.nixos.org and Mathlib's caches), which the cloud sessions
# cannot. claude/handoff-lean-prove.md in the rind project has the reasons.
#
#   HW_PR=323 (default): the upstream sync to eba4c466. Its merge adds
#     `sample_poly_cbd2_8x` in rind/src/mid/mlkem.rs (since removed), opaque in admin/prove
#     and declared in proofs/Rind/X86_64/FunsExternal.lean, so the Aeneas
#     translation and every Lean module must still check: `admin/prove lean`.
#   HW_PR=322: the smaller P-256 IFMA import into #246's branch:
#     `admin/prove lean`, then `admin/prove vg` in the `vg` shell when Intel
#     SDE is there (HW_SKIP_VG=1 skips it).
#   HW_PR=<n>, any other PR, such as an upstream sync whose merge touched
#     proofs: `admin/prove lean` alone.
#   HW_FULL=1 also runs `admin/prove` with no argument (HOL Light included;
#     hours).
#
# It checks out the PR's head in its own worktree, runs each command in the
# flake's dev shell, and writes summary.md, the comment for the PR: the
# host, the flake's revision, each command with its exit code and time, and
# the first error of each failure. It merges nothing.
#
# Host: Linux x86_64 with AVX2 (the Lean proofs test the intrinsic models
#   on it), Nix with flakes, 16 GB of RAM, and 40 GB free.
# Takes: about an hour the first time (the toolchain and Mathlib download),
#   then 20 to 40 minutes for `lean`.
# Writes: .tmp/hw/lean-replay-<time>/ with summary.md, one log per command,
#   and run.log.
# Exits: 0 when every command passed, 1 when one failed, after writing
#   summary.md either way. With HW_SKIP_VG=1, #322's summary lists the VG
#   check as skipped and reads "Partial", and the exit is 2: nothing failed,
#   but the run does not clear the gate.
#
# Usage: HW_PR=323 admin/hw/lean-replay.sh [--preflight]
# Pin the commit of an earlier run with HW_HEAD_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

pr=${HW_PR:-323}
[[ $pr =~ ^[1-9][0-9]*$ ]] || hw_die "HW_PR is a pull request number, not $pr"
[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] ||
    hw_refuse "the proofs run on Linux x86_64, not $(uname -s) $(uname -m)"
hw_has_flag avx2 || hw_refuse "$(hw_cpu_model) has no AVX2, which the Lean intrinsic-model tests need"
hw_need_tools git nix
nix flake --help >/dev/null 2>&1 || hw_refuse "nix has no flakes; enable experimental-features = nix-command flakes"
mem_kb=$(awk '/^MemTotal:/ { print $2 }' /proc/meminfo)
((mem_kb >= 15 * 1024 * 1024)) || hw_refuse "$((mem_kb / 1024 / 1024)) GB of RAM; the proofs need 16"
mkdir -p "$HW_ROOT/.tmp"
free_kb=$(df -Pk "$HW_ROOT/.tmp" | awk 'NR == 2 { print $4 }')
((free_kb >= 40 * 1024 * 1024)) || hw_refuse "$((free_kb / 1024 / 1024)) GB free under .tmp; the proofs need 40"
hw_preflight_done

hw_setup
head=$(hw_rev "refs/pull/$pr/head" "${HW_HEAD_REV:-}")
wt=$(hw_worktree "pr$pr" "$head")
hw_say "#$pr at $head"

commands=("prove|admin/prove lean")
failed=0
rows=()
# A check the gate needs but this run left out: its row says so, and the
# verdict is "Partial", never "Passed".
skipped=()
if [[ $pr == 322 ]]; then
    if [[ -z ${HW_SKIP_VG:-} ]]; then
        commands+=("vg|admin/prove vg")
    else
        skipped+=("| \`nix develop .#vg --command admin/prove vg\` | skipped | | HW_SKIP_VG=1: the VG machine-code and cosimulation check did not run |")
    fi
fi
[[ -z ${HW_FULL:-} ]] || commands+=("prove|admin/prove")
for entry in "${commands[@]}"; do
    shell=${entry%%|*}
    cmd=${entry#*|}
    log=$HW_RUN/$(echo "$shell-$cmd" | tr ' /' '__').log
    hw_say "nix develop .#$shell --command $cmd"
    start=$(date +%s)
    status=0
    # shellcheck disable=SC2086 # cmd is a fixed command line above.
    (cd "$wt" && nix develop ".#$shell" --command $cmd) >"$log" 2>&1 || status=$?
    minutes=$((($(date +%s) - start + 59) / 60))
    first_error=""
    if ((status != 0)); then
        failed=1
        first_error=$(grep -m1 -E '(^|[^a-z])error([:\[]| )' "$log" | cut -c1-300 || true)
        [[ -n $first_error ]] || first_error=$(tail -n1 "$log" | cut -c1-300)
        # A pipe or backtick would break the table cell.
        first_error=$(printf '%s' "$first_error" | tr '|`' "/'")
    fi
    rows+=("| \`nix develop .#$shell --command $cmd\` | $status | ${minutes} min | ${first_error:+\`$first_error\`} |")
done

flake_rev=$(git -C "$wt" rev-parse HEAD)
{
    echo "### Lean replay of #$pr"
    echo
    echo "Host $(hostname), $(hw_cpu_model), $((mem_kb / 1024 / 1024)) GB; nix $(nix --version | awk '{ print $NF }'); flake at \`$flake_rev\` (the PR's head); $(date -u +%Y-%m-%dT%H:%MZ)."
    echo
    echo "| Command | Exit | Time | First error |"
    echo "|---|---|---|---|"
    printf '%s\n' "${rows[@]}"
    ((${#skipped[@]} == 0)) || printf '%s\n' "${skipped[@]}"
    echo
    if ((failed)); then
        echo "**Failed.** The logs are under \`$HW_RUN\`."
    elif ((${#skipped[@]})); then
        echo "**Partial:** every command that ran passed, but a check this PR needs was skipped (above). This does not clear the replay."
    else
        echo "**Passed.**"
    fi
} >"$HW_RUN/summary.md"
cat "$HW_RUN/summary.md"
hw_follow_up "$pr" "$HW_RUN/summary.md"
if ((failed)); then
    echo "lean-replay: a proof command failed; summary.md says which" >&2
    exit 1
fi
if ((${#skipped[@]})); then
    echo "lean-replay: partial run (a required check was skipped); summary.md says which" >&2
    exit 2
fi
if [[ $pr == 323 && ${#skipped[@]} == 0 ]]; then
    cat <<'EOF'

The owner has approved merging #323 once `admin/prove lean` passes; that
merge (a merge commit) is a separate step, not this script's.
EOF
fi
