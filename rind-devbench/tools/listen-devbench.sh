#!/bin/bash
# Collector for RindBench All (v14) on the computer the devices report to: one ncat per device port. Appends JSON lines.
# 9101 = iPad Pro M4, 9102 = iPad mini A17 Pro, 9103 = Android (v13 keeps 9099/9100).
# Android over USB: also `adb reverse tcp:9103 tcp:9103` so the app finds 127.0.0.1:9103 by itself.
# Starts only the listeners not already running. usage: listen-devbench.sh [DIR]
D=${1:-.}
for pf in 9101:devbench-m4 9102:devbench-a17 9103:devbench-android; do
  p=${pf%%:*} f=${pf#*:}
  if pgrep -f "ncat -l -k $p\$" >/dev/null; then echo "$p already listening"; continue; fi
  nohup ncat -l -k $p >> "$D/$f.jsonl" 2>/dev/null &
  echo "listening on $p -> $D/$f.jsonl"
done
ADB=$(command -v adb || echo $HOME/.local/bin/adb)
for s in $($ADB devices 2>/dev/null | awk 'NR>1 && $2=="device"{print $1}'); do
  $ADB -s $s shell pm path io.github.steelhead99x.rindbench >/dev/null 2>&1 && $ADB -s $s reverse tcp:9103 tcp:9103 && echo "adb reverse 9103 on $s"
done
