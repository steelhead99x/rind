# Live H.264 video over SX1276 FSK, encrypted with rind

Results from streaming live H.264 (320x240, 15 fps) from a Raspberry Pi 2 with a Dragino SX1276 HAT to a CatWAN RP2040 stick, over SX1276 FSK at 300k and 350k, with and without rind per-frame AEAD (rind main `d2dc35bd796aaadc42df56aee0f1526cdee94b66`).

- `slides/`: the HTML deck (`deck.html`), rendered slides, and `WRITEUP.md` with the full table.
- `video/`: raw logs and summaries for all 8 runs (330 s each), plus `table.md` and the exact commands in `video/README.md`.
- `media/`: a 60-second received clip and frame grabs from the f350 run with rind on.

Headline: about 172 kbit/s of video, about 95% of frames delivered Pi to CatWAN, glass-to-glass 131 to 139 ms p50. rind adds 20 B per frame and about 1% CPU, with no measurable change in loss or latency.
