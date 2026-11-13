# [M] rind-bench times pyca/verified-garbage on every host and tier

## Goal

rind-bench, the benchmark report, and the nightly tier bench time VG beside the other libraries, and every cell where VG is at least as fast as rind at every size has a quest that switches rind to it.

## Plan

- VG is not on crates.io. Pin it in `rind-bench` as a git dependency by commit. Its generated assembly is checked in, so no Lean build is needed.
- Time the same work as rind's rows. Known differences:
  - VG's ECDSA signs deterministically.
  - VG's RSA takes key components and a digest rather than DER and a message, and imports keys slowly.
  - VG's ML-KEM key generation is from a seed.
  - Its ML-DSA has pre-expanded keys.
- Add VG to the report's library list (`BENCHMARKS.md`, `admin/bench-report`) and to the nightly's forced tiers (`bench.yml`). Force VG's dispatcher to the same tier with its `VG_CPU_FEATURES` override, so a denied feature is denied to both.
- Time VG on every nightly tier and on the report's six hosts, at the sizes [the report refresh's bar](/quest/m2/bench/report-refresh.md) sets. The nightly's AVX-512 runners cover the tier the hosts lack. The epic's Zen 5 numbers are a starting point, not a result.
- Triage each primitive and tier where VG is as fast at every size. For each, add as follow-ups:
  - a switch quest that lands the code (the first one adds `admin/import-vg`);
  - a ✓ quest that imports the theorem, requiring [cosimulation](/quest/m2/verified-garbage/cosim.md).
  Record each cell VG loses, with its ratio, in this epic's README.
- For each of the nine m4 quests that require this one: delete it when a switch replaces the code it would prove, or rewrite it to what remains, and otherwise drop this link.
