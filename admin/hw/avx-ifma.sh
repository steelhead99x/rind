#!/usr/bin/env bash
# steelhead99x/rind#178: X25519 and Ed25519 verification on AVX-IFMA without
# AVX-512, timed against aws-lc-rs on the CPU the tier is for.
#
# Host: an idle, dedicated Linux x86_64 machine whose CPU has AVX-IFMA and no
#   AVX-512 (Arrow Lake, Lunar Lake, Sierra Forest), pinned to a P-core.
# Takes: about 45 minutes (three builds of two rind-bench targets, then 5 to
#   12 interleaved rounds of about two minutes).
# Writes: .tmp/hw/avx-ifma-<time>/ with ab.md (the comment for #178), ab.json,
#   rounds.json, meta.json, run.log, raw/ (criterion's estimates per round),
#   and variants/<name>/<host>.json (bench-report's shape).
#
# Variants, interleaved with their order rotated each round:
#   main    the fork's main
#   pr      the PR's head
#   pr-off  the PR's head with the tier denied (built with --cfg
#           rind_cpu_disable, run with RIND_CPU_DISABLE_avxifma=1), which
#           isolates the tier from main's other changes since the PR's base
# Rows: x25519-ecdh, x25519-ecdh-stored, and ed25519-verify, rind against
# aws-lc-rs in the same process. A round is clean for a row when aws-lc-rs's
# row moves at most 1.02 between the two variants and the host stayed idle;
# the run needs 5 clean rounds of every row.
#
# Usage: admin/hw/avx-ifma.sh [--preflight]
# Pin the commits of an earlier run with HW_MAIN_REV and HW_PR_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

hw_require_linux_x86_64
hw_refuse_vm
hw_has_flag avx_ifma || hw_refuse "$(hw_cpu_model) has no AVX-IFMA (or this kernel does not report avx_ifma)"
if hw_has_flag avx512ifma || hw_has_flag avx512f; then
    hw_refuse "$(hw_cpu_model) has AVX-512, which takes rind's AVX-512 IFMA tier instead"
fi
p_cores=
if [[ -r /sys/devices/cpu_core/cpus ]]; then
    p_cores=$(cat /sys/devices/cpu_core/cpus)
fi
hw_pick_pin "$p_cores"
if [[ -n $p_cores ]] && ! hw_expand "$p_cores" | grep -qx "$HW_PIN"; then
    hw_refuse "CPU $HW_PIN is an E-core; the P-cores are $p_cores"
fi
hw_lease
hw_check_idle
hw_preflight_done

hw_setup
main=$(hw_rev refs/heads/main "${HW_MAIN_REV:-}")
pr=$(hw_rev refs/pull/178/head "${HW_PR_REV:-}")
hw_say "main $main, PR $pr, pinned to CPU $HW_PIN"
wt_main=$(hw_worktree main "$main")
wt_pr=$(hw_worktree pr "$pr")
off_flags='--cfg rind_cpu_disable'

hw_rind_cpuid "$wt_pr" "$pr" "" avxifma=1 avx512ifma=0
bins_main=$(hw_build_benches main "$wt_main" "$main" "" x25519 ed25519)
bins_pr=$(hw_build_benches pr "$wt_pr" "$pr" "" x25519 ed25519)
bins_off=$(hw_build_benches pr-off "$wt_pr" "$pr" "$off_flags" x25519 ed25519)

hw_check_idle
"$HW_AB" rounds --out "$HW_RUN" --pin "$HW_PIN" \
    --label "steelhead99x/rind#178: AVX-IFMA X25519 and Ed25519 verification" \
    --variant main "$main" "$wt_main/rind-bench" "$bins_main" \
    --variant pr "$pr" "$wt_pr/rind-bench" "$bins_pr" \
    --variant pr-off "$pr" "$wt_pr/rind-bench" "$bins_off" \
    --env pr-off RIND_CPU_DISABLE_avxifma=1 \
    --filter '^(x25519-ecdh|x25519-ecdh-stored|ed25519-verify)/(rind|aws-lc-rs)$' \
    --compare pr:rind/main:rind --compare pr:rind/pr-off:rind \
    --control-lib aws-lc-rs

cat <<'EOF'

How the owner's decision (2026-11-25) reads this: the tier is accepted if
pr / main and pr / pr-off are below 1 on every row with 5 clean rounds. If
ed25519-verify's pr / pr-off is above 0.95 (under a 5% gain), the PR body
says to dispatch the tier for X25519 only. The Windows run is
admin/hw/avx-ifma-windows.sh.
EOF
hw_follow_up 178 "$HW_RUN/ab.md"
