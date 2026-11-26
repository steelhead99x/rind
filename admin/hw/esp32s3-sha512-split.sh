#!/usr/bin/env bash
# steelhead99x/rind#326: SHA-512 on the ESP32-S3 with its sums split into
# u32 lanes (`generic::sum64`), so no `bltu`/`bgeu` branches on a carry.
# The checks the PR still owes from quest/m2/speed/xtensa-carry-branches.md,
# on the PR's base and head, in this order:
#
#   1. admin/esp32s3-sha512-layout at each revision: section placement, no
#      call and no flash load from the IRAM body, the IRAM ceiling at
#      opt-level 3, s, and z, and the "abc" block under QEMU's esp32s3 CPU.
#   2. The branch count: every register-register `bltu`/`bgeu` in the
#      compressor objects step 1 built (rolled and unrolled, ESP-IDF and
#      none-elf), for base and head, with each one listed. A count, not a
#      pass: loop bounds on public counters may stay. Head should have none
#      left in the round and schedule code.
#   3. The board A/B is not run here: the last lines name the two commits
#      to build harness firmware from and how to interleave the images with
#      run-board.sh, as #296's board runs did.
#
# Host: Linux x86_64 with the espup toolchain the board uses (rustc
#   1.97.0.0, 8ea53bcd7) and the xtensa-esp-elf binutils under
#   $HOME/.espressif (admin/esp32s3-toolchain.sh has the paths and the
#   RIND_ESP_* overrides), plus qemu-system-xtensa for step 1, network for
#   its pinned header, and a host C compiler. The board itself only for
#   step 3, on the machine with run-board.sh.
# Takes: about 15 minutes (two layout runs of eighteen probe builds each).
# Writes: .tmp/hw/esp32s3-sha512-split-<time>/ with summary.md (the comment
#   for #326), layout-{base,head}.log, branches-{base,head}.txt, run.log,
#   and obj-{base,head}/.
#
# Usage: admin/hw/esp32s3-sha512-split.sh [--preflight]
# Pin the commits of an earlier run with HW_BASE_REV and HW_HEAD_REV.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] ||
    hw_refuse "the espup toolchain here is Linux x86_64, not $(uname -s) $(uname -m)"
hw_need_tools git python3
# shellcheck source=admin/esp32s3-toolchain.sh
. "$HW_ROOT/admin/esp32s3-toolchain.sh"
for tool in "$rustc" "$cargo" "$objdump"; do
    [[ -x $tool ]] || hw_refuse "$tool is missing; install the espup toolchain (admin/esp32s3-toolchain.sh)"
done
hw_preflight_done

hw_setup
base=$(hw_rev refs/heads/main "${HW_BASE_REV:-}")
head=$(hw_rev refs/pull/326/head "${HW_HEAD_REV:-}")
hw_say "base $base, head $head"

# Step 1, and the objects step 2 reads.
layout_ok=()
for name in base head; do
    sha=${!name}
    wt=$(hw_worktree "$name" "$sha")
    hw_say "layout check at $name ($sha)"
    script=$wt/admin/esp32s3-sha512-layout
    # A revision before RIND_SHA512_LAYOUT_KEEP runs its own script with only
    # its exit trap changed to copy the objects out, beside the original so
    # it finds the same root.
    if ! grep -q RIND_SHA512_LAYOUT_KEEP "$script"; then
        sed "s|^trap 'rm -rf \"\$work\"' EXIT\$|trap 'mkdir -p \"\$RIND_SHA512_LAYOUT_KEEP\"; cp \"\$work\"/obj/*.o \"\$RIND_SHA512_LAYOUT_KEEP\"/ 2>/dev/null; rm -rf \"\$work\"' EXIT|" \
            "$script" >"$script-keep"
        grep -q RIND_SHA512_LAYOUT_KEEP "$script-keep" || hw_die "cannot add the object copy to $name's layout script"
        script=$script-keep
    fi
    if RIND_SHA512_LAYOUT_KEEP=$HW_RUN/obj-$name hw_gate sh "$script" >"$HW_RUN/layout-$name.log" 2>&1; then
        layout_ok+=("$name: pass")
    else
        layout_ok+=("$name: FAIL (layout-$name.log)")
    fi
    [[ -d $HW_RUN/obj-$name ]] || hw_die "no compressor objects from $name; see layout-$name.log"
done

# Step 2: register-register bltu/bgeu in the compressor functions.
count_branches() {
    local dir=$1 out=$2 obj
    : >"$out"
    for obj in "$dir"/*.o; do
        [[ -e $obj ]] || continue
        "$objdump" -d --no-show-raw-insn "$obj" | awk -v obj="$(basename "$obj")" '
            /^[0-9a-f]+ <.*>:$/ { fn = $2; next }
            fn ~ /sha512/ && $2 ~ /^(bltu|bgeu)$/ && $3 ~ /^a[0-9]+,$/ && $4 ~ /^a[0-9]+,/ {
                print obj "\t" fn "\t" $0
            }' >>"$out"
    done
}
for name in base head; do
    count_branches "$HW_RUN/obj-$name" "$HW_RUN/branches-$name.txt"
done
per_object() {
    awk -F'\t' '{ n[$1]++ } END { for (o in n) print o, n[o] }' "$1" | sort
}

# Step 3: the board images are built by the harness; name the commits.
{
    echo "### #326 on hardware: layout, branch count"
    echo
    echo "base \`$base\` (main), head \`$head\`; $(hostname), $(date -u +%Y-%m-%dT%H:%MZ)."
    echo
    echo "**admin/esp32s3-sha512-layout:** ${layout_ok[*]}"
    echo
    echo "**Register-register \`bltu\`/\`bgeu\` in sha512 symbols** (a count, not a pass):"
    echo
    echo "| Object | base | head |"
    echo "|---|---|---|"
    join -a1 -a2 -e0 -o 0,1.2,2.2 <(per_object "$HW_RUN/branches-base.txt") \
        <(per_object "$HW_RUN/branches-head.txt") | awk '{ printf "| %s | %s | %s |\n", $1, $2, $3 }'
    echo
    echo "Totals: base $(wc -l <"$HW_RUN/branches-base.txt"), head $(wc -l <"$HW_RUN/branches-head.txt")."
    echo "Each head branch is listed in branches-head.txt; any left should be a loop bound on a public counter."
    echo
    echo "**Board A/B:** pending (see below)."
} >"$HW_RUN/summary.md"
cat "$HW_RUN/summary.md"

cat <<EOF

Step 3, on the machine with the S3 harness: build the firmware once at base
($base) and once at head ($head), then flash them interleaved, control first
and between every variant image (base, head, base, head, base, ...: at least
five head images), with run-board.sh at 80 MHz, then once more at 240 MHz.
Every capture's KAT lines must read PASS before its timing counts. Add the
SHA-512 rows (16 B, 243 B, 1500 B, many-block) as medians per image to
$HW_RUN/summary.md.
EOF
hw_follow_up 326 "$HW_RUN/summary.md"
