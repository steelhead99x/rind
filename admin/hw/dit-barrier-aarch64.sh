#!/usr/bin/env bash
# steelhead99x/rind#325: the barrier after `msr DIT, #1`, picked from
# MIDR_EL1 off Apple's targets. The checks this workspace could not run,
# since it has no aarch64 target:
#
#   1. The host's part: MIDR_EL1 from sysfs, its implementer, and whether
#      the kernel reports DIT and SB. On implementer 0x61 (Apple silicon
#      under Linux) the barrier must be picked; elsewhere it must not.
#   2. rind's aarch64 cpu and entry unit tests at the PR's head, debug:
#      `midr_fixture_selects_the_schedule` (every RIND_TEST_MIDR fixture,
#      `apple` included), `midr_selects_apple_cores_for_the_dit_barrier`,
#      `detected_value_matches_midr` (the cached pick against this host's
#      register), `abi`, and the DIT entry checks.
#   3. With HW_FULL=1, the whole `cargo test -p rind --lib` as well.
#   4. admin/dit-disasm, where the host has llvm-objdump (rustup's
#      llvm-tools) and the aarch64-apple-darwin standard library: every
#      `msr DIT, #1` on Linux reaches sb or dsb nsh; isb on some path.
#
# Host: Linux aarch64. Run it twice if you can: on the Pi 5 (Cortex-A76,
#   implementer 0x41, which has no DIT, so step 1 expects no barrier and the
#   tests cover the fixtures), and in a Linux VM on an Apple-silicon Mac
#   (OrbStack, UTM, or Lima), where step 1 expects the barrier and
#   `detected_value_matches_midr` checks it on a real Apple core. The VM's
#   MIDR_EL1 is whatever Hypervisor.framework presents; step 1 prints it.
# Takes: about 15 minutes on a Pi 5 (one debug test build), 40 with HW_FULL=1.
# Writes: .tmp/hw/dit-barrier-aarch64-<time>/ with summary.md (the comment
#   for #325), tests.log, dit-disasm.log, and run.log.
# Exits: 0 when every check that ran passed (dit-disasm may be skipped for
#   missing tools), 1 when a check failed, after writing summary.md either
#   way.
#
# Usage: admin/hw/dit-barrier-aarch64.sh [--preflight]
# Pin the commit of an earlier run with HW_HEAD_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

[[ $(uname -s) == Linux ]] || hw_refuse "this check runs on Linux, not $(uname -s)"
[[ $(uname -m) == aarch64 ]] || hw_refuse "this check needs an aarch64 CPU, not $(uname -m)"
hw_need_tools git cargo python3
midr_file=/sys/devices/system/cpu/cpu0/regs/identification/midr_el1
[[ -r $midr_file ]] || hw_refuse "$midr_file is missing: the kernel lists no ID registers"
hw_preflight_done

hw_setup
head=$(hw_rev refs/pull/325/head "${HW_HEAD_REV:-}")
wt=$(hw_worktree head "$head")
target=$(hw_target "$head" "")
hw_say "head $head"

# Step 1.
midr=$(<"$midr_file")
implementer=$(printf '0x%02x' $(((midr >> 24) & 0xff)))
part=$(printf '0x%03x' $(((midr >> 4) & 0xfff)))
flags=$(awk -F': ' '/^Features/ { print $2; exit }' /proc/cpuinfo)
has() { [[ " $flags " == *" $1 "* ]] && echo yes || echo no; }
dit=$(has dit)
sb=$(has sb)
if [[ $implementer == 0x61 ]]; then
    expect="Apple's barrier ($([[ $sb == yes ]] && echo sb || echo 'dsb nsh; isb sy'))"
else
    expect="no barrier"
fi
hw_say "MIDR_EL1 $midr: implementer $implementer, part $part; DIT $dit, SB $sb; expect $expect"

# Step 2, and 3 with HW_FULL=1.
filter=(low::aarch64::cpu low::entry)
[[ -z ${HW_FULL:-} ]] || filter=()
failed=0
tests=pass
(cd "$wt" && CARGO_TARGET_DIR=$target hw_gate cargo test -p rind --lib -- "${filter[@]}") \
    >"$HW_RUN/tests.log" 2>&1 || {
    tests="FAIL (tests.log)"
    failed=1
}
results=$(grep -E '^test result:' "$HW_RUN/tests.log" | tail -1 || true)

# Step 4, where the tools are present.
disasm="skipped: no llvm-objdump or aarch64-apple-darwin std (rustup component add llvm-tools; rustup target add aarch64-apple-darwin)"
sysroot=$(rustc --print sysroot)
host=$(rustc -vV | awk '/^host:/ { print $2 }')
if [[ -x $sysroot/lib/rustlib/$host/bin/llvm-objdump && -d $sysroot/lib/rustlib/aarch64-apple-darwin ]]; then
    if (cd "$wt" && CARGO_TARGET_DIR=$HW_TARGET_ROOT/dit-disasm-${head:0:12} python3 admin/dit-disasm) \
        >"$HW_RUN/dit-disasm.log" 2>&1; then
        disasm="pass: $(grep -c '^dit-disasm: .*: ok$' "$HW_RUN/dit-disasm.log") builds ok"
    else
        disasm="FAIL (dit-disasm.log)"
        failed=1
    fi
fi

{
    echo "### #325 on $(hostname): DIT barrier by part"
    echo
    echo "head \`$head\`, $(date -u +%Y-%m-%dT%H:%MZ)."
    echo
    echo "- MIDR_EL1 \`$midr\`: implementer \`$implementer\`, part \`$part\`; kernel reports DIT $dit, SB $sb. Expected pick: $expect."
    echo "- \`cargo test -p rind --lib${filter[*]:+ -- ${filter[*]}}\` (debug): $tests. $results"
    echo "- \`admin/dit-disasm\`: $disasm"
    if [[ $implementer == 0x61 ]]; then
        echo
        echo "On this Apple core \`detected_value_matches_midr\` asserts the cached pick is the barrier."
    fi
} >"$HW_RUN/summary.md"
cat "$HW_RUN/summary.md"
hw_follow_up 325 "$HW_RUN/summary.md"
if ((failed)); then
    echo "dit-barrier-aarch64: a check failed; summary.md says which" >&2
    exit 1
fi
