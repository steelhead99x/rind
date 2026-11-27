# [XS] Record the weekly bench's first RustCrypto-baseline gaps

## Goal

`benchmarks/data/tiers.json` holds a scheduled weekly run that times RustCrypto for Argon2id, SLH-DSA, and the protocols, and `benchmarks/gaps.toml` holds a decision for every gap that run shows, before the second such scheduled run's `gate` job would fail on them.

## Plan

[kixel-ai/rind#964](https://github.com/kixel-ai/rind/pull/964) made RustCrypto a weekly baseline where aws-lc-rs and ring offer nothing. `admin/bench-report render` refuses a `gaps.toml` entry for a gap the saved weekly data does not show, so that PR could not record the armv7 gaps its dispatched [run 44996218659](https://github.com/kixel-ai/rind/actions/runs/44996218659) found. The first scheduled run after it lands reports them as new, and the next one fails its `gate` job unless they have decisions.

- Start once a scheduled `bench` run on `main` has the RustCrypto rows: `admin/bench-report weekly`, then `admin/bench-report render`, which names each gap without a decision.
- Expected, from the dispatched run: `blind-rsa2048-blind/*` on armv7 (1.60×), which [kixel-ai/rind#1007](https://github.com/kixel-ai/rind/pull/1007) closes (0.15× in its dispatched [run 45447290902](https://github.com/kixel-ai/rind/actions/runs/45447290902)), so a scheduled run from before it lands records it as closed after the run. That run also had `oprf-ristretto255-blind/*` and `oprf-ristretto255-evaluate/*` on armv7 at 1.07 and 1.16×, but only because its `voprf` rows skipped the point encoding and decoding rind's rows pay; [kixel-ai/rind#1009](https://github.com/kixel-ai/rind/pull/1009) made the rows symmetric, so a gap there now is new. Triage any other new gap the same way, into a speed quest or a recorded reason.
- Re-measure the x86_64 `oprf-ristretto255-*` gap, whose `gaps.toml` entry points at [the AVX2 quest](/quest/m2/speed/ristretto255-avx2.md): it was measured with the same lopsided rows, so with symmetric ones it should shrink. Resize that quest to what remains and say so on its PR, [kixel-ai/rind#943](https://github.com/kixel-ai/rind/pull/943), or delete the entry if the gap is gone (decided in kixel-ai/rind#1009).

## Scheduled

- 2026-11-28 - the weekly `bench` runs Saturdays at 12:23 UTC, so the first run after kixel-ai/rind#964 lands is the 28th at the earliest
