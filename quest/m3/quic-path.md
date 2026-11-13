# [XS] AMD CPUs without VAES run their fastest AES-GCM tier

## Goal

x86_64 CPUs with AVX and MOVBE but no VAES, such as Zen 2, run whichever of Vale's AES-GCM and rind's SSE `by8` loop is faster at QUIC packet sizes, decided from a Zen 2 measurement. This is what remains of the investigation into MoQ's QUIC packet path.

## Plan

Moved from m1 with the maintainer on 2026-11-09: ✅ m3, with the other outside waits (rejected: stay in m1, where it kept the milestone open after MoQ's switch finished).

Since 0.1.13 ([kixel-ai/rind#329](https://github.com/kixel-ai/rind/pull/329)), these CPUs run Vale's kernel at every length, but seals under 129 B, which run `by8` since [kixel-ai/rind#436](https://github.com/kixel-ai/rind/pull/436) from a Coffee Lake measurement. Forced onto this tier there, Zen 3 sealed faster on `by8` up to 272 B and opened faster on Vale at most lengths. Forcing tiers with `--cfg rind_cpu_disable` on newer cores ([kixel-ai/rind#387](https://github.com/kixel-ai/rind/pull/387)) shows `by8` 3-8% ahead of Vale at 1200-1452 B on Zen 3, 4, and 5, and Vale 15-49% ahead on Arrow Lake. zshenker's numbers on [moq-dev/moq#7873](https://github.com/moq-dev/moq/pull/7873#issuecomment-6670951461) predate 0.1.13. Bulk encryption takes the fastest source outright, so if Zen 2 runs `by8` faster, route AMD CPUs without VAES to it; otherwise delete this quest.

Decided with the maintainer on 2026-11-05, from #387's findings (✅ chosen):
- Route AES-GCM opens under 256 B to Vale on VAES and AVX-512 CPUs: approve ✅ / drop. Done in [kixel-ai/rind#391](https://github.com/kixel-ai/rind/pull/391).
- Call the hardware AES block directly for header protection: approve ✅ / drop. Done in [kixel-ai/rind#392](https://github.com/kixel-ai/rind/pull/392).
- DIT on aarch64: keep toggling it per call, once per batch where an API processes one ✅ / never set it, as aws-lc-rs / leave it set once a thread enters rind. Narrowed with the maintainer on 2026-11-08 to Apple's platforms, since Arm says DIT changes nothing on its current cores.
- One-pass short-message AES-GCM on aarch64, with DIT kept per call: approve ✅ / drop. Done in [kixel-ai/rind#393](https://github.com/kixel-ai/rind/pull/393).
- Ask zshenker for a Zen 2 rerun on 0.1.13: ask ✅ / skip.
- New public QUIC API (a key that seals and applies header protection in one call, or a GSO batch seal): none ✅ / add. Neither measured an end-to-end win: header protection and dispatch are 3.6% of moq's CPU in `echo_quic`, rustls exposes no QUIC secrets for a fused key, and batching 1200 B packets amortizes only a few ns of about 100-270 ns per call.
- moq-quic: no quest, so nothing goes to moq-dev/moq's perf epic.

## Waiting

- zshenker: rerun moq-dev/moq#7873's bench on the Zen 2 EPYC 7662 with rind 0.1.13 or later, pinned, reporting AES-128-GCM seal and open at 64 B and 1200 B against aws-lc-rs. His 0.1.12 numbers ran `by8`, so the two compare the tiers. Check for the reply on [moq-dev/moq#7873](https://github.com/moq-dev/moq/pull/7873).
