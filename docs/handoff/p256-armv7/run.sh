#!/bin/bash
# Interleaved A/B on the Pi 2B, core 3. rind2 is the control: the same binary as rind.
B=${1:-ab-p256-main}; R=${2:-7}
ssh pi2b 'for c in 0 1 2 3; do echo performance | sudo tee /sys/devices/system/cpu/cpu$c/cpufreq/scaling_governor >/dev/null; done; vcgencmd measure_clock arm; vcgencmd measure_temp; vcgencmd get_throttled'
libs=(rind awslc ring openssl)
for r in $(seq $R); do
  for op in keygen ecdh ecdsakeygen sign verify; do
    for i in 0 1 2 3; do l=${libs[$(( (i + r) % 4 ))]}
      echo -n "r$r "; ssh pi2b "taskset -c 3 /lib/ld-linux-armhf.so.3 ./$B $l $op"
    done
  done
  ssh pi2b 'echo "r'$r' temp $(vcgencmd measure_temp) $(vcgencmd get_throttled) $(vcgencmd measure_clock arm)"'
done
ssh pi2b 'for c in 0 1 2 3; do echo ondemand | sudo tee /sys/devices/system/cpu/cpu$c/cpufreq/scaling_governor >/dev/null; done; vcgencmd get_throttled; cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor'
