#!/usr/bin/env bash
# steelhead99x/rind#178: the Windows run of the AVX-IFMA tier, whose ladder
# allocates a 96-byte stack frame because Windows has no red zone. CI's
# Windows runners may lack AVX-IFMA, where the tier's tests return early, so
# this runs rind's tests on a CPU that takes the tier.
#
# Host: Windows on an x86_64 CPU with AVX-IFMA and no AVX-512 (Arrow Lake,
#   Lunar Lake), in Git Bash, with rustup's MSVC toolchain and what CI's
#   Windows job needs to build rind's aws-lc-rs dev-dependency.
# Takes: about 20 minutes (debug and release builds of rind's tests).
# Writes: .tmp/hw/avx-ifma-windows-<time>/ with run.log, rind-cpuid.json,
#   tests-debug.log, tests-release.log, and summary.md (the comment for #178).
#
# It checks with rind-cpuid at the PR's head that rind detects avxifma and
# not avx512ifma, then runs `cargo test -p rind` in debug and release, as
# build.yml's Windows job does. Nothing is timed.
#
# Usage: admin/hw/avx-ifma-windows.sh [--preflight]
# Pin the commit of an earlier run with HW_PR_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

case $(uname -s) in
    MINGW* | MSYS* | CYGWIN*) ;;
    *) hw_refuse "this is the Windows run; $(uname -s) is not Windows (Git Bash)" ;;
esac
[[ $(uname -m) == x86_64 ]] || hw_refuse "this run needs an x86_64 CPU, not $(uname -m)"
hw_need_tools git cargo

# Windows has no /proc/cpuinfo, so rind-cpuid, built at the PR's head, is the
# check; it reports avxifma only from that revision on.
HW_RUN=$HW_ROOT/.tmp/hw/avx-ifma-windows-$(date -u +%Y%m%dT%H%M%SZ)
mkdir -p "$HW_RUN/src"
trap hw_cleanup EXIT
pr=$(hw_rev refs/pull/178/head "${HW_PR_REV:-}")
wt=$(hw_worktree pr "$pr")
target=$(hw_target "$pr" "")
cpuid=$(cd "$wt" && CARGO_TARGET_DIR=$target cargo run -q --release -p rind-cpuid) || hw_die "rind-cpuid failed"
echo "$cpuid" >"$HW_RUN/rind-cpuid.json"
[[ $cpuid == *'"avxifma": 1'* ]] || hw_refuse "rind detects no AVX-IFMA on this CPU: $cpuid"
[[ $cpuid == *'"avx512ifma": 0'* ]] || hw_refuse "this CPU has AVX-512 IFMA, which takes the AVX-512 tier instead"
if ((HW_PREFLIGHT)); then
    echo "preflight passed: this host can run $(basename "$0")" >&2
    exit 0
fi
exec > >(tee -a "$HW_RUN/run.log") 2>&1
hw_say "PR $pr; results in $HW_RUN"

status=0
declare -A result
for profile in debug release; do
    flag=()
    [[ $profile == debug ]] || flag=(--release)
    hw_say "cargo test -p rind ${flag[*]}"
    if (cd "$wt" && CARGO_TARGET_DIR=$target cargo test -p rind "${flag[@]}" 2>&1) >"$HW_RUN/tests-$profile.log"; then
        result[$profile]=passed
    else
        result[$profile]="FAILED (exit $?)"
        status=1
    fi
done
log=$HW_RUN/tests-release.log

{
    echo "### steelhead99x/rind#178: Windows run on an AVX-IFMA CPU"
    echo
    echo "- Head \`$pr\`, $(cmd //c ver 2>/dev/null | tr -d '\r' | grep -v '^$' || uname -sr)"
    echo "- \`$(rustc -V)\`"
    echo "- rind-cpuid: avxifma 1, avx512ifma 0 (\`rind-cpuid.json\`)"
    for profile in debug release; do
        f=$HW_RUN/tests-$profile.log
        echo "- \`cargo test -p rind\` ($profile): ${result[$profile]}; $(grep -cE '^test .* ok$' "$f") tests ok, $(grep -cE '^test .* FAILED$' "$f") failed"
    done
    echo "- The tier's tests, which return early without the tier: $(grep -E '^test .*(avx_ifma|x25519_matches_s2n_bignum).* ok$' "$log" | sed 's/^test //; s/ \.\.\. ok$//' | paste -sd, -)"
} >"$HW_RUN/summary.md"
cat "$HW_RUN/summary.md"
hw_follow_up 178 "$HW_RUN/summary.md"
exit "$status"
