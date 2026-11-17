| run | dir | FSK | rind | video kbit/s | radio goodput kbit/s | radio frame loss | obj lost | video frame loss | obj lat p50/p95 ms | g2g p50/p95 ms | stalls >250 ms | Pi CPU % | bytes/obj: AEAD / total air overhead | seal / open µs |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| f300_off | Pi→Mac | 300k | none | 171.2 | 222.7 | 0.510% | 21 | 4.52% | 70 / 170 | 139 / 239 | 20 obj, 20 dec (worst 1207 ms) | 108 (tx 62 + enc 46) | 0 / 361 | 0.0 / 0.0 |
| f300_on | Pi→Mac | 300k | chacha20poly1305 | 171.8 | 225.6 | 0.568% | 27 | 4.58% | 71 / 172 | 138 / 241 | 20 obj, 20 dec (worst 1198 ms) | 109 (tx 64 + enc 46) | 20 / 382 | 94.9 / 5.5 |
| f350_off | Pi→Mac | 350k (x) | none | 172.2 | 222.6 | 0.386% | 20 | 4.01% | 62 / 143 | 131 / 212 | 17 obj, 17 dec (worst 1178 ms) | 100 (tx 54 + enc 46) | 0 / 361 | 0.0 / 0.0 |
| f350_on | Pi→Mac | 350k (x) | chacha20poly1305 | 173.0 | 225.2 | 0.392% | 18 | 3.52% | 63 / 145 | 132 / 214 | 17 obj, 17 dec (worst 1192 ms) | 101 (tx 55 + enc 46) | 20 / 383 | 95.8 / 17.3 |
| r300_off | Mac→Pi | 300k | none | 161.9 | 219.3 | 1.464% | 50 | 10.34% | 49 / 148 | 123 / 227 | 44 obj, 44 dec (worst 1680 ms) | 111 (rx 97 + dec 14) | 0 / 361 | 0.0 / 0.0 |
| r300_on | Mac→Pi | 300k | chacha20poly1305 | 165.5 | 222.1 | 1.563% | 44 | 8.46% | 51 / 153 | 126 / 229 | 37 obj, 36 dec (worst 1959 ms) | 111 (rx 97 + dec 14) | 20 / 382 | 17.9 / 77.6 |
| r350_off | Mac→Pi | 350k (x) | none | 154.6 | 217.2 | 2.553% | 74 | 14.85% | 43 / 125 | 117 / 207 | 64 obj, 64 dec (worst 2000 ms) | 110 (rx 97 + dec 13) | 0 / 360 | 0.0 / 0.0 |
| r350_on | Mac→Pi | 350k (x) | chacha20poly1305 | 154.9 | 218.6 | 2.937% | 77 | 14.89% | 44 / 128 | 118 / 207 | 59 obj, 59 dec (worst 2000 ms) | 110 (rx 97 + dec 13) | 20 / 382 | 20.0 / 75.8 |
