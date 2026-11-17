# results/video: rind off/on benchmark, 2026-11-17

Eight 330 s runs, 10:43-11:32 PT, back to back, in this order: f300_off, f300_on, r300_off,
r300_on, f350_off, f350_on, r350_off, r350_on. `f` = Pi 2 -> CatWAN/Mac, `r` = Mac -> CatWAN -> Pi 2.

Fixed settings: 915.0 MHz, +5 dBm, 320x240, 15 fps, GOP 15, x264 ultrafast/zerolatency at 180 kbit/s,
FEC k=8, 96 B minimum frame, max object age 1000 ms. CatWAN firmware v5
(`firmware/catwan-fw-v5.uf2`, sha256 fe86cc05...). rind main d2dc35bd796aaadc42df56aee0f1526cdee94b66,
ChaCha20-Poly1305. Antennas ~1 m apart, indoors.

## Exact commands

Key (once): `( umask 077; openssl rand -hex 32 > ~/sx1276-link/moq-lora-key.hex )`, copied to the Pi as
`~/moq-lora-key.hex`.

Pi -> Mac (`scripts/run2.sh NAME PROFILE 330 ...`), e.g. f300_on:

```sh
# Mac: clock offset, then receiver
moq-lora-recv --clock-check pi-host-a                         # -> remote_minus_local_ms = OFF
moq-lora-recv --port /dev/cu.usbmodem21301 --profile 300000:100000:6 --secs 340 --out runs/f300_on \
    --play --decode --raw-log --clock-offset-ms=$OFF --key-file ~/sx1276-link/moq-lora-key.hex
# Pi (3 s later)
./moq-lora-send --profile 300000:100000:6 --secs 330 --log /tmp/f300_on_send.jsonl --i-have-an-antenna \
    --fec-k 8 --key-file ~/moq-lora-key.hex
```

Mac -> Pi (`scripts/rev.sh`), e.g. r350_off (12 B preamble at 300k, 14 B at 350k):

```sh
moq-lora-recv --clock-check pi-host-a                         # X = Pi minus Mac; the Pi receiver gets -X
ssh pi-host-a "cd ~/moq-lora && ./moq-lora-recv --radio --profile 350000:100000:14:x --secs 340 \
    --out /tmp/r350_off --decode --raw-log --clock-offset-ms=-$X"
moq-lora-send --catwan /dev/cu.usbmodem21301 --profile 350000:100000:14:x --secs 330 \
    --log runs/r350_off.send.jsonl --i-have-an-antenna --fec-k 8
```

Forward profiles: `300000:100000:6`, `350000:100000:6:x`. A clock check ran every 5 s throughout
(`scripts/clocklog.sh` -> `clock_log.jsonl`).

Table:

```sh
cargo run --release -p moq-lora-report -- --clock-log clock_log.jsonl \
    f300_off f300_on f350_off f350_on r300_off r300_on r350_off r350_on > table.md
```

## Files per run

| file | what |
|---|---|
| `summary.json` | receiver summary (loss, latency with the start offset, stalls, rind, CPU on the Pi for `r` runs) |
| `send_summary.json` | sender summary (video bitrate, frames, airtime, overhead per object, seal time, CPU on the Pi for `f` runs) |
| `objects.jsonl.gz` | one line per object received: time, group, object, frame, size, FEC repairs, gate decision, latency |
| `decoded.jsonl.gz` | one line per decoded frame: time, barcode capture time, glass-to-glass latency |
| `send.jsonl.gz` | one line per object sent: enqueue time, capture time, encoder delay, frames |
| `serial.log.gz` | every receiver radio line (`R` frames in hex, `X` errors), timestamped |
| `clock_start.txt`, `clock_end.json` | offsets before and after the run |
| `recv_stderr.txt`, `send_stderr.txt` | tool output |

`table.md` recomputes latency with the 5 s clock log and drops the frame the ffmpeg CLI decoder flushes
when its input closes at the end of a run (it shows up ~9 s late in the raw `summary.json` as one
decoded "stall" and the g2g max). Not committed: the `rec.h264` recordings (7 MB each).
