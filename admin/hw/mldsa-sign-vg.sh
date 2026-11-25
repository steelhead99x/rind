#!/usr/bin/env bash
# ML-DSA signing on x86_64 without AVX2: rind against pyca/verified-garbage
# (VG), the measurement that would reopen steelhead99x/rind#315 (closed; its
# branch claude/q-mldsa-sign-vg keeps the vendoring). Upstream switches only
# if VG wins at every size, against rind after kixel-ai/rind#863.
#
# Host: an idle, dedicated Linux x86_64 machine with AVX2, which this denies
#   as the weekly bench's no-AVX2 tier does (bench.yml's x86_64 portable row).
# Takes: about 35 minutes (one build of rind-bench's mldsa target, then 5 to
#   12 interleaved rounds of about two minutes).
# Writes: .tmp/hw/mldsa-sign-vg-<time>/ with ab.md (the comment for #315),
#   ab.json, rounds.json, meta.json, run.log, raw/, and
#   variants/<name>/<host>.json.
#
# One binary of rind-bench's mldsa target at the fork's main (which has
# kixel-ai/rind#863), built with --cfg rind_cpu_disable and run with the
# tier's denials: RIND_CPU_DISABLE_{avx2,adx,bmi2,sha}=1, OPENSSL_ia32cap
# for aws-lc, and VG_CPU_FEATURES for VG. Two variants, interleaved with their
# order rotated each round:
#   rind  the rind and aws-lc-rs rows
#   vg    the verified-garbage and aws-lc-rs rows
# Rows: ML-DSA-44, -65 and -87 keygen, sign and verify. A round is clean for a
# row when aws-lc-rs's row moves at most 1.02 between the two processes and
# the host stayed idle; the run needs 5 clean rounds of every row.
#
# Usage: admin/hw/mldsa-sign-vg.sh [--preflight]
# Pin the commit of an earlier run with HW_MAIN_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

hw_require_linux_x86_64
hw_refuse_vm
hw_has_flag avx2 || hw_refuse "$(hw_cpu_model) has no AVX2, so denying it would not reproduce the weekly tier"
hw_pick_pin
hw_lease
hw_check_idle
hw_preflight_done

hw_setup
main=$(hw_rev refs/heads/main "${HW_MAIN_REV:-}")
git -C "$HW_ROOT" merge-base --is-ancestor c851e38f9 "$main" ||
    hw_die "$main does not have kixel-ai/rind#863 (c851e38f9)"
hw_say "main $main, pinned to CPU $HW_PIN"
wt=$(hw_worktree main "$main")
flags='--cfg rind_cpu_disable'
bins=$(hw_build_benches main "$wt" "$main" "$flags" mldsa)

# VG may use the features this CPU has, less those the tier denies, by VG's
# names (bench.yml's vg_deny, with the x86_64 tier's list).
denied=" avx2 bmi1 bmi2 adx sha sha512 avx512f avx512ifma avx512vl avx512bw avx512fp16 vaes vpclmulqdq "
allowed=()
for name in ssse3 sha:sha_ni aes pclmulqdq avx avx2 bmi1 bmi2 avx512f sha512 adx avx512ifma avx512vl vaes vpclmulqdq avx512bw avx512fp16:avx512_fp16; do
    flag=${name#*:} name=${name%%:*}
    if [[ $denied != *" $name "* ]] && hw_has_flag "$flag"; then
        allowed+=("$name")
    fi
done
vg_features=$(
    IFS=,
    echo "${allowed[*]:-none}"
)
tier=(RIND_CPU_DISABLE_adx=1 RIND_CPU_DISABLE_avx2=1 RIND_CPU_DISABLE_bmi2=1 RIND_CPU_DISABLE_sha=1
    OPENSSL_ia32cap='~0x0:~0x5e42f02b0128' VG_CPU_FEATURES="$vg_features")
envs=()
for v in rind vg; do
    for e in "${tier[@]}"; do
        envs+=(--env "$v" "$e")
    done
done

hw_check_idle
"$HW_AB" rounds --out "$HW_RUN" --pin "$HW_PIN" \
    --label "ML-DSA without AVX2: verified-garbage against rind (steelhead99x/rind#315)" \
    --variant rind "$main" "$wt/rind-bench" "$bins" \
    --variant vg "$main" "$wt/rind-bench" "$bins" \
    "${envs[@]}" \
    --filter-of rind '^mldsa(44|65|87)-(keygen|sign|verify)/(rind|aws-lc-rs)$' \
    --filter-of vg '^mldsa(44|65|87)-(keygen|sign|verify)/(verified-garbage|aws-lc-rs)$' \
    --compare vg:verified-garbage/rind:rind \
    --control-lib aws-lc-rs

cat <<'EOF'

The quest's rule: switch signing to VG only for the sets where
mldsa*-sign's vg / rind is below 1 with 5 clean rounds, at all three sizes.
EOF
hw_follow_up 315 "$HW_RUN/ab.md"
