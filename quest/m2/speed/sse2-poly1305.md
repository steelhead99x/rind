# [M] Poly1305 runs a vectorized SSE2 path on x86_64 CPUs without SSE4.1

## Goal

On x86_64 CPUs without SSE4.1 (the weekly bench's "no AES-NI" and "SSE2" tiers), ChaCha20-Poly1305 and XChaCha20-Poly1305 at 16 KB, seal and open, take no more than aws-lc-rs's time, closing the 1.11 to 1.18× gap that `benchmarks/gaps.toml`'s entry records.

## Plan

Planned 2026-11-27 (owner: close the top five benchmark gaps, overriding the entry's reason not to port BoringSSL's SSE2 `poly1305_vec.c` for CPUs older than Westmere).

- Today, without SSE4.1, rind runs Graviola's scalar Poly1305. Port BoringSSL's `poly1305_vec.c` (SSE2, two blocks per pass with 26-bit limbs), or an equivalent SSE2 schedule, behind the SSE2-only tier, and keep the faster existing paths on every CPU that has them.
- Poly1305 handles a secret key: the port must stay constant time. Add a ctgrind test on the new path, run it under the repo's CPU-forcing mechanism so it runs on a host with newer features, and differential-test it against the scalar path and RFC 8439 vectors at every length up to several blocks past each lane boundary.
- Measure the SSE2 tier by forcing it on any x86_64 host; the finishing PR removes the gap's entry with the numbers.
