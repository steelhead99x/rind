# [M] Poly1305 runs a vectorized SSE2 path on x86_64 CPUs without SSE4.1

## Goal

On x86_64 CPUs without SSE4.1 (the weekly bench's "no AES-NI" and "SSE2" tiers), ChaCha20-Poly1305 and XChaCha20-Poly1305 at 16 KB, seal and open, take no more than aws-lc-rs's time, closing the 1.11 to 1.18× gap that `benchmarks/gaps.toml`'s entry records.

## Plan

Planned 2026-11-27 (owner: close the top five benchmark gaps, overriding the entry's reason not to port BoringSSL's SSE2 `poly1305_vec.c` for CPUs older than Westmere).

- Today, without SSE4.1, rind runs Graviola's scalar Poly1305. Port BoringSSL's `poly1305_vec.c` (SSE2, two blocks per pass with 26-bit limbs), or an equivalent SSE2 schedule, behind the SSE2-only tier, and keep the faster existing paths on every CPU that has them.
- Poly1305 handles a secret key: the port must stay constant time. Add a ctgrind test on the new path, run it under the repo's CPU-forcing mechanism so it runs on a host with newer features, and differential-test it against the scalar path and RFC 8439 vectors at every length up to several blocks past each lane boundary.
- Measure the SSE2 tier by forcing it on any x86_64 host; the finishing PR removes the gap's entry with the numbers.
- Done in [steelhead99x/rind#355](https://github.com/steelhead99x/rind/pull/355): `low/x86_64/poly1305_sse2.rs` ports aws-lc's `poly1305_vec.c`, two lanes of 26-bit limbs, four blocks a pass, for runs of eight blocks or more on CPUs without SSE4.1. A 16 KB seal takes 3.8 instructions a byte against aws-lc's 4.7 and the scalar path's 3.9. On a shared 2-core Xeon VM, forcing each tier, rind's 16 KB seal took 17.0 to 20.3 µs against 20.7 to 23.4 µs before without AES-NI (aws-lc-rs 17.6 to 18.7), and 33.1 to 35.3 µs against 35.8 to 39.2 on SSE2 (aws-lc-rs 30.5 to 34.9).
- What remains (owner, 2026-11-28: keep the gap's entry until weekly data, as with portable SHA-1): the weekly bench's "no AES-NI" and "SSE2" tiers re-measure the entry's rows. If both hold at or under 1.0× aws-lc-rs, the report refresh removes the entry and this quest. If the SSE2 tier still trails, as the VM's numbers suggest it may, the next step goes here.
- Untimed: the eight-block threshold between 128 B and 1350 B (aws-lc starts its lanes at 33 B); sweep it on a report host if the 1350 B rows move.
