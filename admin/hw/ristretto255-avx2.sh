#!/usr/bin/env bash
# steelhead99x/rind#256: ristretto255's constant-time multiplication on
# curve25519-dalek's AVX2 formulas, timed on a CPU that really lacks ADX.
# Every earlier run only denied ADX on a CPU that has it.
#
# Host: an idle Linux x86_64 machine with AVX2 and without ADX, which is
#   Haswell (the OVH VPSes, `ovh-iad` and `ovh-sea`, qualify; their lease is
#   held for the run). A VM is accepted, since no dedicated Haswell is left.
# Takes: about 40 minutes (two builds of rind-bench's oprf target, then 5 to
#   12 interleaved rounds of about two minutes).
# Writes: .tmp/hw/ristretto255-avx2-<time>/ with ab.md (the comment for
#   #256), ab.json, rounds.json, meta.json, run.log, raw/, and
#   variants/<name>/<host>.json.
#
# Variants, interleaved with their order rotated each round:
#   base  the PR's base branch, claude/base-upstream-main-q-ristretto255-avx2
#   head  the PR's head
#   ctl   base's binary run again: a round is clean for a row when ctl / base
#         is within 1.02 and the host stayed idle (the A/B control rule);
#         the run needs 5 clean rounds of every row
# Rows: oprf-ristretto255-{blind,evaluate,finalize}, rind, with `voprf`
# (curve25519-dalek, the `rustcrypto` row) beside it for reference.
#
# Usage: admin/hw/ristretto255-avx2.sh [--preflight]
# Pin the commits of an earlier run with HW_BASE_REV and HW_HEAD_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

hw_require_linux_x86_64
hw_has_flag avx2 || hw_refuse "$(hw_cpu_model) has no AVX2"
if hw_has_flag adx; then
    hw_refuse "$(hw_cpu_model) has ADX, which keeps s2n-bignum's path; this needs a CPU without it (Haswell)"
fi
hw_pick_pin
hw_lease
hw_check_idle
hw_preflight_done

hw_setup
base=$(hw_rev refs/heads/claude/base-upstream-main-q-ristretto255-avx2 "${HW_BASE_REV:-}")
head=$(hw_rev refs/pull/256/head "${HW_HEAD_REV:-}")
hw_say "base $base, head $head, pinned to CPU $HW_PIN"
wt_base=$(hw_worktree base "$base")
wt_head=$(hw_worktree head "$head")

hw_rind_cpuid "$wt_head" "$head" "" avx2=1 adx=0
bins_base=$(hw_build_benches base "$wt_base" "$base" "" oprf)
bins_head=$(hw_build_benches head "$wt_head" "$head" "" oprf)
mkdir -p "$HW_RUN/bin/ctl"
cp "$HW_RUN"/bin/base/* "$HW_RUN/bin/ctl/"
bins_ctl=${bins_base//\/bin\/base\//\/bin\/ctl\/}

hw_check_idle
"$HW_AB" rounds --out "$HW_RUN" --pin "$HW_PIN" \
    --label "steelhead99x/rind#256: ristretto255 AVX2 multiplication without ADX" \
    --variant base "$base" "$wt_base/rind-bench" "$bins_base" \
    --variant head "$head" "$wt_head/rind-bench" "$bins_head" \
    --variant ctl "$base" "$wt_base/rind-bench" "$bins_ctl" \
    --filter '^oprf-ristretto255-(blind|evaluate|finalize)/(rind|rustcrypto)$' \
    --compare head:rind/base:rind --compare head:rind/head:rustcrypto \
    --control-variant ctl=base

cat <<'EOF'

head / base below 1 on blind and evaluate is the speed claim the PR makes;
head:rind / head:rustcrypto is rind against voprf on this CPU.
EOF
hw_follow_up 256 "$HW_RUN/ab.md"
