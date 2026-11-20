#!/bin/bash
# Collector for RindBench All (v14) on the Alienware: one ncat per iPad port.
# 9101 = iPad Pro M4, 9102 = iPad mini A17 Pro (v13 keeps 9099/9100). Appends JSON lines.
# usage: listen-devbench.sh [DIR]   then: tools/import-device.py DIR/devbench-m4.jsonl --out DIR/import
D=${1:-$HOME/ipad-tools}
nohup ncat -l -k 9101 >> "$D/devbench-m4.jsonl" 2>/dev/null &
nohup ncat -l -k 9102 >> "$D/devbench-a17.jsonl" 2>/dev/null &
echo "listening on 9101 -> $D/devbench-m4.jsonl, 9102 -> $D/devbench-a17.jsonl"
