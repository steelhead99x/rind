#!/usr/bin/env bash
# Pushes ./pkg to /data/local/tmp/rind-armv7 on one adb device, runs the named benches
# single-threaded and pinned to one core, pulls the logs into ./out, and removes the push.
# Usage: SERIAL=<adb serial> CPU_MASK=8 admin/handoff-firetv-armv7/scripts/run-on-tv.sh bench[:regex] ...
#   e.g. run-on-tv.sh chacha20poly1305:'^chacha20poly1305/(rind|aws-lc-rs|openssl)/(32B|1350B|16KB)$'
set -euo pipefail
S="${SERIAL:-$(adb devices | awk 'NR==2{print $1}')}"; MASK="${CPU_MASK:-8}"; D=/data/local/tmp/rind-armv7
adb() { command adb -s "$S" "$@"; }
mkdir -p out
adb shell "rm -rf $D; mkdir -p $D"
adb push pkg "$D/" >/dev/null
adb shell "chmod 755 $D/pkg/*; $D/pkg/rind-cpuid" | tee out/cpuid.json
{ adb shell getprop ro.product.model; adb shell getprop ro.build.version.security_patch; adb shell uname -a; } > out/device.txt
for spec in "$@"; do
  b="${spec%%:*}"; re=""; [ "$spec" = "$b" ] || re="${spec#*:}"
  # Single-quote the regex for the device shell, escaping any single quote in it.
  re_q="'${re//\'/\'\\\'\'}'"
  adb shell "cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_cur_freq" > "out/$b.freq-before" || true
  # toybox taskset takes a hex mask, not -c.
  adb shell "cd $D; taskset $MASK pkg/$b --bench --noplot --warm-up-time 1 --measurement-time 3 $re_q > $b.log 2>&1; echo $b rc=\$?"
  adb pull "$D/$b.log" "out/$b.log" >/dev/null
done
adb shell "rm -rf $D"
