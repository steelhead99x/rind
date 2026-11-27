# [XS] Ask pyca/verified-garbage for looped variants of its largest x86_64 routines

## Goal

pyca/verified-garbage has an issue from rind asking for looped (smaller) variants of the unrolled routines that make up most of what an x86_64 `rustls + rind-rustls` client still carries over `aws-lc-rs`'s, with the sizes that motivate it.

## Plan

Decided 2026-11-24 (maintainer, [kixel-ai/rind#1008](https://github.com/kixel-ai/rind/pull/1008#issuecomment-7140848735)): ✅ ask upstream for looped variants (rejected: dropping an x86_64 tier's RSA or P-256 routine for a lower tier's; swapping `VG_P384_COMB` for rind's smaller table, or benchmarking that swap now).

- The stripped client is 5.29 MB in a default release against 4.11 MB over `aws-lc-rs`, and rind's part is 3.86 MB in the one-codegen-unit build `admin/binary-size.txt` records. Measure with `nm -S --size-sort -C target/binary-size/x86_64-unknown-linux-gnu/release/build-cost-rustls` after `admin/binary-size`.
- What to ask about, by size: the IFMA RSA routines, 380 KB in three (`vg_rsa_public_precomputed_checked_ifma`, `vg_rsa_private_crt_precomputed_ifma`, and its `ifma512` twin); P-256 ECDSA verification, 136 KB with IFMA and 98 KB with ADX. Each is one unrolled routine, so only upstream can shrink it without rind leaving a tier. Say that rind takes a variant only where it measures as fast, so a loop that costs speed does not help.
- Not asked: `VG_P384_COMB`, 338 KB, since a smaller table is a speed trade upstream already made.
- Search pyca/verified-garbage's issues for an existing request first.
- What upstream ships arrives through [the upstream run](/quest/m2/upstream-updates.md)'s re-pin, whose diff of `admin/binary-size.txt` shows the gain; this quest finishes once the issue is filed, and that run's baseline links it.

## Waiting

- Maintainer: approve the issue's draft before it is posted, since pyca/verified-garbage is outside the orgs agents may post in. Recommended: approve; the project is written by LLMs and has taken rind's reports before ([pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321)). Clear it by approving the draft in this quest's PR.

## Related

- [Take what rind's upstreams changed since their pins](/quest/m2/upstream-updates.md)
