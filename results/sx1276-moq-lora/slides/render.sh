#!/bin/bash
cd /workspace/slides/sx1276-moq
names=(01-title 02-hardware 03-before-after 04-overnight-soak 05-why-quic-1200 06-video-pipeline 07-rind-on-off 08-latency-cpu 09-rules-caveats 10-try-it)
for n in $(seq 1 10); do
  google-chrome --headless=new --no-sandbox --disable-gpu --hide-scrollbars --force-device-scale-factor=1 \
    --window-size=1920,1080 --virtual-time-budget=2000 \
    --screenshot="renders/${names[$((n-1))]}.png" "file://$PWD/deck.html?render#$n" 2>/dev/null
done
ls renders
