# Live encrypted video over an old SX1276 radio on a Pi 2

*Draft for kixel-ai/rind-results. Status: soak numbers final (54 blocks); rind on/off numbers final (8 runs, 10:43–11:32 AM PT, Nov 17, 2026).*

## Summary

Old SX1276 LoRa/FSK radio chips and a Raspberry Pi 2 can carry live, encrypted H.264 video once the software is rewritten in Rust. With the stock Python driver the link moved 3.8 kbit/s. With a Rust SX1276 driver on the Pi and Rust firmware on a CatWAN RP2040 stick, the same class of radio moves 242 kbit/s with 63 B frames and about 280 kbit/s with 255 B frames at FSK 300 kbit/s. An overnight soak delivered QUIC-sized 1,200 B datagrams with 0.01–0.02% loss in both directions. On top of that link, a 320×240, 15 fps video stream, sealed per frame with rind (ChaCha20-Poly1305), arrives at 171–173 kbit/s of video Pi → Mac and 155–166 kbit/s Mac → Pi. Encryption adds 20 B per frame and 0–1 point of one Pi core; latency moves 1–3 ms and loss stays within run-to-run noise.

## Hardware

| End | Hardware | Role |
|---|---|---|
| Camera / sender | Raspberry Pi 2 Model B (BCM2836, 4× Cortex-A7 at 900 MHz, 1 GB, armv7) with a Dragino LoRa/GPS HAT v1.4 (HopeRF RFM95W = Semtech SX1276; GPS unused) | Runs ffmpeg, the Rust sender and the Rust SX1276 driver |
| Viewer / receiver | Electronic Cats CatWAN USB Stick RP2040 (RP2040 + RFM95W, an SX1276-class radio) plugged into a Mac | Runs Rust firmware `catwan-fw` v5; the Mac runs the Rust receiver and ffplay |

The antennas were the HAT's SMA whip and the stick's whip, about 1 m apart on the bench. All transmissions were on 915.0 MHz at +5 dBm.

## Results

### 1. Before and after the Rust rewrite

| Stack | Throughput |
|---|---|
| Stock Python driver | 3.8 kbit/s |
| Rust driver + Rust CatWAN firmware, 63 B frames | 242 kbit/s |
| Rust driver + Rust CatWAN firmware, 255 B frames, FSK 300k | about 280 kbit/s |

Same radios before and after. The Rust driver runs on the Pi and the Rust firmware on the CatWAN.

### 2. Overnight soak (final, 54 blocks)

| Payload · mode | Pi → CatWAN | CatWAN → Pi |
|---|---|---|
| 1,200 B QUIC-sized datagrams, FSK 300k | 280.4 kbit/s, 134,971 / 135,000 frames, 0.02% loss | 277.0 kbit/s, 134,984 / 135,000 frames, 0.01% loss |
| 255 B frames, FSK 300k | 284.1 kbit/s, 0.01% loss | 280.6 kbit/s, 0.03% loss |
| 63 B frames | 242.3 kbit/s | 220.6 kbit/s |
| Stress: FSK 350k | 329.6 kbit/s, 0.37% loss | 321.6 kbit/s, 1.04% loss |
| LoRa SF6 / 500 kHz | 35.2 kbit/s | 35.5 kbit/s |

Reading the table:

- **QUIC-sized datagrams work.** 1,200 B is the floor QUIC sets for client Initial datagrams (RFC 9000 §14.1), derived from the IPv6 minimum MTU of 1,280 B (RFC 8200 §5) less 40 B IPv6 and 8 B UDP headers, with 32 B of headroom. With 255 B FSK frames a 1,200 B datagram fits in 5 fragments; with 63 B frames and a 16-fragment cap it did not (about 976 B max). Overnight, 29 of 135,000 frames were lost Pi → CatWAN and 16 of 135,000 CatWAN → Pi.
- **FSK 350k** moved 329.6 / 321.6 kbit/s with 0.37% / 1.04% loss. 350k is outside the SX1276 datasheet's checked settings (the tools need an explicit `:x` flag for it).
- **LoRa SF6 / 500 kHz** is roughly an eighth of FSK 300k: 35.2 / 35.5 kbit/s.

### 3. Video: rind on vs off (final, 8 runs)

**Settings for every run:** 915.0 MHz, +5 dBm, 320×240 at 15 fps, FEC on (k=8), 330 s per run, run between 10:43 and 11:32 AM PT on Nov 17, 2026. rind main `d2dc35bd`, ChaCha20-Poly1305. Latency is clock-corrected (offset checked every 5 s). **(x)** marks 350k, which is outside the SX1276 datasheet's checked settings.

| run | direction | rind | video kbit/s | goodput kbit/s | radio frame loss | video frame loss | net lat p50/p95 ms | glass p50/p95 ms | stalls | Pi CPU % | bytes/frame (total) | enc/dec µs |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| f300_off | Pi→Mac 300k | off | 171.2 | 222.7 | 0.51% | 4.52% | 70/170 | 139/239 | 20 | 108 | 361 | – |
| f300_on | Pi→Mac 300k | on | 171.8 | 225.6 | 0.57% | 4.58% | 71/172 | 138/241 | 20 | 109 | 382 | 95/5.5 |
| f350_off | Pi→Mac 350k (x) | off | 172.2 | 222.6 | 0.39% | 4.01% | 62/143 | 131/212 | 17 | 100 | 361 | – |
| f350_on | Pi→Mac 350k (x) | on | 173.0 | 225.2 | 0.39% | 3.52% | 63/145 | 132/214 | 17 | 101 | 383 | 96/17 |
| r300_off | Mac→Pi 300k | off | 161.9 | 219.3 | 1.46% | 10.3% | 49/148 | 123/227 | 44 | 111 | 361 | – |
| r300_on | Mac→Pi 300k | on | 165.5 | 222.1 | 1.56% | 8.5% | 51/153 | 126/229 | 37 | 111 | 382 | 18/78 |
| r350_off | Mac→Pi 350k (x) | off | 154.6 | 217.2 | 2.55% | 14.9% | 43/125 | 117/207 | 64 | 110 | 360 | – |
| r350_on | Mac→Pi 350k (x) | on | 154.9 | 218.6 | 2.94% | 14.9% | 44/128 | 118/207 | 59 | 110 | 382 | 20/76 |

Notes on the columns:

- **Pi CPU** is % of one core. In Pi→Mac runs it is the sender + x264 on the Pi. In Mac→Pi runs it is the receiver + decoder on the Pi.
- **enc/dec** is the per-frame seal time on the sending side and the open time on the receiving side. Pi→Mac: seal on the Pi, open on the Mac. Mac→Pi: seal on the Mac, open on the Pi.
- **bytes/frame** is the total on-air overhead per video frame (headers, padding, FEC parity, and the AEAD fields when rind is on).

What the table shows:

- **Overhead:** rind adds 20 B per frame (4 B session id + 16 B tag). The measured total moved from 360–361 B to 382–383 B, so 21–22 B. The extra ~1 B (2 B in two of the four pairs) is not yet explained.
- **CPU:** rind on vs off is 0–1 point of one Pi core in every pair (108→109, 100→101, 111→111, 110→110).
- **Encryption time:** sealing on the Pi 2 takes 95–96 µs per frame; opening on the Pi takes 76–78 µs. On the Mac, sealing takes 18–20 µs and opening 5.5–17 µs.
- **Latency:** rind on adds 1–3 ms at p50 and p95 network latency, and −1 to +3 ms glass-to-glass.
- **Loss:** off/on differences (e.g. 0.51% vs 0.57%, 2.55% vs 2.94%, video frame loss 10.3% vs 8.5%) go both ways and are within run-to-run variation.
- **Takeaway:** rind costs about 1% CPU and 20 B per frame, with no measurable change in loss or latency.
- **Reverse-direction loss is higher** (1.46–2.94% radio frame loss and 8.5–14.9% video frame loss Mac→Pi, vs 0.39–0.57% and 3.5–4.6% Pi→Mac) because the Pi's HAT must be read by constant polling, which uses a full core and misses frames. Stalls follow the same pattern: 17–20 per run Pi→Mac, 37–64 Mac→Pi.
- **Loss varies between runs.** An earlier pair of the same configuration lost 0 frames. Compare off vs on within the same pass, not one pass against another.
- **350k (x)** gave lower latency Pi→Mac (glass-to-glass 131/212 ms vs 139/239 ms at 300k, rind off) with similar or lower loss in this pass. Mac→Pi it lost more than 300k.

### 4. Reading latency and CPU

- **Glass-to-glass includes about one frame (~67 ms) held back by the decoder.** The receiver measures glass-to-glass by reading a timestamp barcode out of the decoded picture, and the ffmpeg CLI decoder holds one frame before it outputs it. At 15 fps that is ~67 ms. At 300k Pi→Mac (rind off), network latency is 70 ms p50 and glass-to-glass 139 ms, so about 69 ms sits between reassembly and display, which includes the ~67 ms decoder hold. At 350k the same split is 62 ms + 69 ms = 131 ms.
- **350k gave lower latency:** 131 vs 139 ms p50 and 212 vs 239 ms p95 glass-to-glass, Pi→Mac, rind off.
- **CPU is shown as % of one core.** The Pi 2 has four cores, so 100–111% of one core is about a quarter of the chip. At f300_on the 109% splits into sender 64% + x264 46%, each rounded (from the earlier status log).

## Method

### Pipeline

On the Pi:

1. **ffmpeg** encodes H.264 at 320×240, 15 fps (x264 `ultrafast`/`zerolatency`; the source is ffmpeg's `testsrc2` pattern with a burned-in clock and a 40-bit timestamp barcode).
2. A **Rust packetizer** wraps the video in MoQ-style objects: track = the stream, **one group per GOP** (starting at an IDR keyframe), one object per encoded frame, with a 17 B object header (frame number, capture time, encoder delay, key flag).
3. **rind per-frame AEAD** seals each object: ChaCha20-Poly1305 by default, AES-128-GCM or AES-256-GCM optional. On the air an object becomes `session u32 | ciphertext | tag 16`, so **+20 B per frame**. The nonce is `session | group | object`; the session id is random per run and redrawn when the 16-bit group id wraps, so no (key, nonce) pair is reused in a run. Group and object ids are bound as associated data.
4. Objects are cut into **255 B FSK frames** (10 B frame header, up to 243 B payload, CRC-16) and protected by **FEC**: XOR parity, one repair frame per k data frames (k = 8 in the benchmark), repairing any single lost fragment per block.
5. The Rust SX1276 driver sends the frames at FSK 300 kbit/s, ±100 kHz deviation.

Over the air, then on the Mac: the **CatWAN** stick receives the frames and passes them over USB serial; the **Rust receiver** repairs with FEC, reassembles, decrypts, and applies the MoQ group gate (an unrecoverable object cuts its group, and delivery resumes at the next keyframe so the decoder never sees a broken reference chain); **ffplay** shows the live picture, and the stream is also recorded and decoded for latency measurement.

**Video also works in reverse, Mac → Pi:** the sender transmits through the CatWAN stick and the receiver runs on the Pi's HAT. The reverse direction needs a longer preamble (12 bytes at 300k, 14 at 350k) because the Pi polls the radio FIFO from userspace.

### What is measured

- **Delivered video:** H.264 bytes handed to the player per second, after the group gate.
- **Radio goodput:** frame bytes the receiver accepted per second, including headers, padding and parity.
- **Radio frame loss:** frames missing by sequence number. CRC-rejected frames are counted separately.
- **Video frames lost:** objects that never reached the player, either lost or cut with their group.
- **Network latency:** capture (Pi clock) → object reassembled (Mac clock), offset-corrected.
- **Glass-to-glass:** capture → frame decoded on the receiver, read back from the barcode in the picture. It includes encode, airtime, reassembly and decode.
- **Stalls:** gaps over 250 ms between consecutive delivered objects or decoded frames.
- **CPU:** getrusage of the Rust process and of its ffmpeg children over the run on the Pi, in % of one core (sender + x264 for Pi→Mac; receiver + decoder for Mac→Pi).

### Stall detection note

A stall is any gap of more than 250 ms between consecutive delivered objects or decoded frames. In the final bench it was the same with rind off and on Pi→Mac (20/20 at 300k, 17/17 at 350k) and lower with rind on Mac→Pi (44→37, 64→59).

### Clock-drift correction

Latency needs the Pi and Mac clocks compared. `moq-lora-recv --clock-check` runs an ssh ping-pong and reports the Pi-minus-Mac offset. The two clocks drifted 20–40 ms between runs, and during one run the Pi's timesyncd stepped its clock by about 50 ms. The harness therefore logs the offset every 5 s alongside each run, and `moq-lora-report --clock-log` re-bases every latency sample on that log instead of a single start-of-run offset. All latency figures in the final table are corrected this way (offset checked every 5 s). The first readout of the f300 pair, which used only the start-of-run offset, was 2–3 ms lower (e.g. 67/168 vs 70/170 ms network latency for f300_off).

### Benchmark harness

`scripts/bench.sh` runs the matched matrix with FEC k=8 and 330 s per run: `f300_off`, `f300_on`, `r300_off`, `r300_on`, `f350_off`, `f350_on`, `r350_off`, `r350_on` (f = Pi → Mac, r = Mac → Pi), with the clock log every 5 s. The final pass ran from 10:43 to 11:32 AM PT on Nov 17, 2026. `moq-lora-report` turns the run directories into the markdown table.

## Software and commits

- **rind:** kixel-ai/rind main at **`d2dc35bd796aaadc42df56aee0f1526cdee94b66`**, pinned as a git dependency.
- **moq-lora:** github.com/steelhead99x/moq-lora, branch `video-demo` (private for now), commit **`97f34b7`**. Crates: `moq-lora-wire` (framing, FEC, reassembly, AEAD, barcode), `moq-lora-send` (Pi, static armv7 musl binary), `moq-lora-recv` (Mac), `moq-lora-report`, and a vendored no_std `sx1276` driver.
- **CatWAN firmware v5** (`firmware/catwan-fw-v5.uf2`): fixes reverse streams that died after 60 seconds. In v4 the transmit timeout was measured from the start of a burst instead of per packet, so after 60 s of continuous transmit traffic the stick started each packet on top of the previous one, and the Pi received short, corrupt frames. Only the reverse direction (stick transmitting) was affected. (v4 had already replaced the frame formatter with a lookup table, because at 300 kbit/s the old formatter was slow enough to miss the start of the next back-to-back frame.)

## Rules and caveats

- **Radio settings:** 915.0 MHz, +5 dBm, single channel in the US 902–928 MHz ISM band. The tools refuse more than +5 dBm and anything outside the band, and nothing transmits without an explicit antenna flag.
- **FCC 15.247:** the 6 dB bandwidth of the 300 kbit/s, ±100 kHz FSK signal is not yet measured. Under 47 CFR §15.247 a digital-modulation system in this band without hopping needs a 6 dB bandwidth of at least 500 kHz; this link may fall short of that.
- **Duty-cycle limits not applied in testing.**
- **Not proven: range.** All results are at bench distance (about 1 m).
- **Not proven: the antenna asymmetry.** It is not yet characterized.
- **Reverse direction:** Mac→Pi loses more frames because the Pi's HAT has no DIO1 wired and must be read by constant polling, which uses a full core and misses frames.
- **350k is outside the datasheet's checked settings** (marked (x)); it worked on these units.
- **Known issue:** after a CRC failure the Pi's long-frame FIFO poll can splice two frames; the end-to-end CRC-16 catches these.
- Check your own rules (FCC, ISED, ETSI, ...) before transmitting. Outside the Americas 915 MHz may not be an ISM band.

## Try it yourself

Repo: github.com/steelhead99x/moq-lora (private for now), branch `video-demo`. At commit `97f34b7`, `HOWTO.md` walks from a bare Pi 2 and a CatWAN stick to a live picture in ffplay: hardware and pinout, build, firmware flash, first light, measurement, rind, and RF notes.

## Sources

- Project measurements: overnight soak (final, 54 blocks); moq-lora `STATUS.md`, `README.md`, `HOWTO.md` on branch `video-demo`.
- RFC 9000 §14.1 and §8.1: https://www.rfc-editor.org/rfc/rfc9000#section-14.1
- RFC 8200 §5: https://www.rfc-editor.org/rfc/rfc8200#section-5
- 47 CFR §15.247: https://www.ecfr.gov/current/title-47/chapter-I/subchapter-A/part-15/subpart-C/section-15.247
- rind: https://github.com/kixel-ai/rind (commit d2dc35bd796aaadc42df56aee0f1526cdee94b66)
