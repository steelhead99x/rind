#!/usr/bin/env bash
# steelhead99x/rind#277: the A/B/C/D DIT and SHA-3 matrix on the iPads
# (rind-devbench/README.md at the PR's head): four builds of RindBench All,
# each a fresh launch, read against each other.
#
# Host: a Mac with Xcode in /Applications/Xcode.app, xcodegen, ncat, and
#   rustup's 1.98.1 toolchain with the aarch64-apple-ios target, on the same
#   network as the iPads; and the iPads (the M4 on port 9101, the A17 Pro on
#   9102), each reporting FEAT_DIT and FEAT_SHA3. Signing and installing each
#   IPA is yours (your Apple developer account), so the script waits for you.
# Takes: about 30 minutes of builds, then five Full runs per iPad, each 20 to
#   40 minutes with the sections below; the two iPads run at the same time.
# Writes: .tmp/hw/ipad-dit-matrix-<time>/ with ipa/ (the eight unsigned
#   IPAs), capture/ (the collector's files), and
#   devbench-ipad-dit-matrix-<date>/<device>/ in rind-results' diag layout:
#   each run's report (.json) and every line it sent (.jsonl), and
#   matrix.md, the comparison for #277 and the PRs its rows answer.
#
# Launch order per iPad: A, B, C, D, then A again as the control. A round of
# the matrix is clean when the second A's rows of the other libraries match
# the first A's within 1.02 (median), which no deny changes.
#   A  default: DIT toggled per call, SHA-3 instructions used
#   B  RIND_DEVBENCH_DENY=sha3
#   C  RIND_DEVBENCH_DENY=dit
#   D  RIND_DEVBENCH_DENY=sha3,dit
# In every run: Full, the same libraries, and the sections Hashes, MACs and
# KDFs, AEADs, PAKE, Signatures, KEMs, plus "More: dit_toggle".
#
# Usage: HW_COLLECTOR_HOST=<this Mac's LAN address> admin/hw/ipad-dit-matrix.sh [--preflight]
# HW_DEVICES="m4" or "a17" runs one iPad; HW_PR_REV pins an earlier head.
set -euo pipefail
# shellcheck source=admin/hw/lib.sh
source "$(dirname "$0")/lib.sh"
hw_args "$@"

[[ $(uname -s) == Darwin ]] || hw_refuse "the iPad builds need a Mac with Xcode, not $(uname -s)"
[[ -d /Applications/Xcode.app ]] || hw_refuse "Xcode is not in /Applications/Xcode.app"
hw_need_tools git python3 rustup cargo xcodegen ncat zip
rustup +1.98.1 target list --installed 2>/dev/null | grep -qx aarch64-apple-ios ||
    hw_refuse "rustup's 1.98.1 toolchain has no aarch64-apple-ios target (rustup +1.98.1 target add aarch64-apple-ios)"
# macOS's /bin/bash is 3.2, so no associative arrays.
port_of() {
    case $1 in
        m4) echo 9101 ;;
        a17) echo 9102 ;;
        *) hw_die "HW_DEVICES names $1; the devices are m4 and a17" ;;
    esac
}
read -ra devices <<<"${HW_DEVICES:-m4 a17}"
for d in "${devices[@]}"; do
    if pgrep -f "ncat -l -k $(port_of "$d")\$" >/dev/null; then
        hw_refuse "a collector already listens on $(port_of "$d"), so this run's capture would miss its lines: stop it first"
    fi
done
host=${HW_COLLECTOR_HOST:-}
[[ -n $host ]] || hw_refuse "set HW_COLLECTOR_HOST to this Mac's LAN address, which the IPAs report to"
hw_preflight_done

hw_setup
pr=$(hw_rev refs/pull/277/head "${HW_PR_REV:-}")
wt=$(hw_worktree pr "$pr")
hw_say "PR $pr; collector $host"
labels=(A B C D)
deny_of() {
    case $1 in
        A) echo "" ;;
        B) echo sha3 ;;
        C) echo dit ;;
        D) echo sha3,dit ;;
    esac
}
mkdir -p "$HW_RUN/ipa" "$HW_RUN/capture"
for label in "${labels[@]}"; do
    ids=$(deny_of "$label")
    tag=${ids:+-deny-${ids//,/_}}
    for d in "${devices[@]}"; do
        hw_say "building $label (${ids:-no deny}) for $d"
        (cd "$wt/rind-devbench" && RIND_DEVBENCH_DENY=$ids hw_gate ios/build-ipa.sh "$(port_of "$d")" "$host") ||
            hw_die "the $label build for $d failed"
        cp "$wt/rind-devbench/ios/out/RindBenchAll-v14.1-$(port_of "$d")$tag.ipa" "$HW_RUN/ipa/$d-$label.ipa"
    done
done

"$wt/rind-devbench/tools/listen-devbench.sh" "$HW_RUN/capture"
# shellcheck disable=SC2329 # the EXIT trap calls it
stop_collectors() {
    for d in "${devices[@]}"; do
        pkill -f "ncat -l -k $(port_of "$d")\$" || true
    done
    hw_cleanup
}
trap stop_collectors EXIT

order=(A B C D A)
denies=(A= B=sha3 C=dit D=sha3+dit)
cat <<EOF

Now, on each iPad in turn, for each IPA in $HW_RUN/ipa/ in the order
${order[*]} (the last A is the same IPA again):
  sign and install <device>-<label>.ipa, open RindBench All, pick Full, the
  same libraries every time, sections Hashes, MACs and KDFs, AEADs, PAKE,
  Signatures, KEMs and "More: dit_toggle", agree, and Start. Keep the iPad
  plugged in and awake. The script tells you when each run has arrived.
EOF
# listen-devbench.sh's file for each port.
capture_of() {
    case $1 in
        m4) echo "$HW_RUN/capture/devbench-m4.jsonl" ;;
        a17) echo "$HW_RUN/capture/devbench-a17.jsonl" ;;
    esac
}
seen=()
while :; do
    left=0
    for i in "${!devices[@]}"; do
        d=${devices[i]} file=$(capture_of "${devices[i]}") n=0
        [[ ! -s $file ]] || n=$("$HW_AB" devbench "$file" --device "$d" --order A,B,C,D,A --denies "${denies[@]}" --wait-for 0)
        if [[ $n != "${seen[i]:-}" ]]; then
            seen[i]=$n
            if ((n < ${#order[@]})); then
                hw_say "$d: $n of ${#order[@]} runs in; next install $d-${order[n]}.ipa and run it"
            else
                hw_say "$d: all ${#order[@]} runs in"
            fi
        fi
        ((n >= ${#order[@]})) || left=1
    done
    ((left)) || break
    sleep 30
done

out=$HW_RUN/devbench-ipad-dit-matrix-$(date -u +%Y-%m-%d)
status=0
for d in "${devices[@]}"; do
    "$HW_AB" devbench "$(capture_of "$d")" --device "$d" --order A,B,C,D,A \
        --denies "${denies[@]}" --out "$out/$d" || status=$?
done
cat "$out"/*/matrix.md >"$out/matrix.md"
cat <<EOF

Next steps:
  1. Post $out/matrix.md on steelhead99x/rind#277:
       gh api repos/steelhead99x/rind/issues/277/comments -F body=@$out/matrix.md
     and the rows each PR asks for on #259, #264, #265 and #266.
  2. Copy $out into a rind-results checkout as results/diag/$(basename "$out")/,
     add a README.md as results/diag/devbench-v14.1-ipad-full-2026-11-22/ has,
     run cargo xtask ci there, and open the pull request.
EOF
exit "$status"
