# Speed regressions are caught the night they land

## Goal

The nightly bench fails on any gap nobody decided, on every tier and at every size people run: it ranks every benchmark it times, and it times the tiers and AEAD sizes no host or row covers today.

## Plan

Decided with the maintainer on 2026-11-09, after an audit of the whole tree: ✅ plan speed measurement and portable speed (rejected: correctness tooling only, or measurement without portable speed work). Measurement joins m2 with the other tooling; the cold tiers' speed work is [m3's](/quest/m3/cold-speed/README.md).

The audit found rind level or ahead in every ranked cell on mainline x86_64, aarch64, and armv7 with the crypto extension. What it could not vouch for is what nothing measures: the nightly prints a summary and never fails, about a third of its benchmark IDs are unranked, and no host or forced tier times aarch64 with the crypto extension but without SHA-3, which is Graviton 2, the Raspberry Pi 5, and most phones.

All three have landed since: the nightly fails on a gap nobody decided once the run before it showed the same gap, so one noisy night does not fail it and a real gap fails on its second ([kixel-ai/rind#560](https://github.com/kixel-ai/rind/pull/560); `admin/bench-report gate --previous`, `.github/workflows/bench.yml:363`), it has rows for the tiers nothing timed ([kixel-ai/rind#556](https://github.com/kixel-ai/rind/pull/556)) and for the AEADs at 128, 256, and 512 B ([kixel-ai/rind#559](https://github.com/kixel-ai/rind/pull/559)), and `admin/bench-report` refuses a benchmark ID no decision lists.

[The benchmark report refresh](/quest/m2/bench/report-refresh.md) keeps the report on the dedicated hosts. This epic makes the nightly catch what lands between refreshes.

Decided 2026-11-12 (maintainer, /quest-audit), after an audit of what the benchmarks still cannot see:

- Hosts: `fedora` joins the report as its AVX-512 host ✅ (rejected: ad hoc runs only; leave the host list alone). This reopens the 2026-11-03 host list: no report host has AVX-512, so no host table shows the AVX-512 AES-GCM kernel, the IFMA RSA routines, or ML-KEM's 8-way sampler against every library. The CPU tier table does time them nightly, on GitHub's EPYC runners against aws-lc-rs and ring, which the interview missed; told so, the maintainer confirmed [the quest](/quest/m2/bench/fedora.md) the same day. `nixos2` is dead and leaves the report in [the refresh](/quest/m2/bench/report-refresh.md).
- Rows: HPKE, the VRF, and blind RSA, which landed without one, and rind-rustls handshakes across threads, get rows.
- Left out: binary size per target, which `admin/build-cost` already reports in BENCHMARKS.md, and a wasm row, which no consumer has asked for.
