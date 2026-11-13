# ring and aws-lc-rs parity

## Goal

A project on ring or aws-lc-rs can move to rind: rind covers ring's
algorithms with its own API, `rind-ring` offers ring's API for a drop-in
swap, rind-rustls matches aws-lc-rs's rustls provider, and a migration guide
maps each ring and aws-lc-rs item to rind's. aws-lc-rs-only algorithms are
listed and start only when a consumer asks.

## Plan

Decided by the maintainer on 2026-10-30:

- m3: no named consumer yet beyond anyone who wants to switch.
- rind keeps its own API, designed against misuse rather than shaped after
  aws-lc-rs (maintainer, 2026-10-31, in the API audit); the migration guide,
  `MIGRATING.md`, maps each ring and aws-lc-rs item to rind's name, the
  quest that adds it, or why rind refuses it, and each child updates its
  rows as it lands. Exact name-for-name compatibility lives only in
  `rind-ring`, which panics wherever ring panics so its signatures match
  ring's (maintainer, 2026-10-31); rind itself never panics on caller input.
- ring's algorithm set first. aws-lc-rs's extras wait for a consumer.
- ML-KEM-1024 and ML-DSA are the exception (maintainer, 2026-11-09): ✅ they
  moved here from m4's post-quantum epic (rejected: into m2, or pushing rustls
  parity back to m4). rustls's aws-lc-rs provider ships both, so rind-rustls
  is their consumer, and m3 could not finish while they sat in m4.
- An OpenSSL provider, once out of reach, is planned in
  [m4](/quest/m4/README.md), and FIPS validation scoped there (maintainer,
  2026-11-04).
- Each new primitive follows `AGENTS.md`: the fastest permissively licensed
  source, a verified one only where it measures as fast at every size,
  Wycheproof vectors, differential tests against aws-lc-rs, ctgrind, and a
  benchmark, on every backend.
