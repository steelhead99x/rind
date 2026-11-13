# [M] Re-audit what's left to prove, end of m3

## Goal

At the end of m3, a report lists every operation, backend, and CPU tier still without a ✓, including every algorithm the [post-quantum](/quest/m4/pq/README.md) and [protocols](/quest/m4/protocols/README.md) epics have landed by then. For each, it gives the code it runs, what is already proven, and the cheapest route to a proof of that same fast code, with an effort estimate. The PR plans the gaps as children of the [verified epic](/quest/m4/verified/README.md) and puts the report in its body.

## Plan

Decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448): re-run the audit at the end of each milestone, so new algorithms are covered as they land, rather than having each algorithm's quest state its own proof route.

- Recurring. This run lives in m4 and requires m3, so it is ready once m3's work is done. The PR that finishes it deletes this file and creates the next run at `/quest/m5/verified/re-audit.md`, creating m5 and an m5 verified epic if needed. That run's `Required` links `/quest/m4/README.md`, and its epic's `Required` links it. The recurrence ends only when a run finds no gap and the maintainer agrees to stop.
- Method, as [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448) ran it: start from `benchmarks/verified.toml`, ALGORITHMS.md's tables and Sources, `proofs/README.md`, and the last audit's report; re-check dispatch in `rind/src` where those are not specific; survey upstream at each project's head (s2n-bignum, aws-lc-verification, HACL\* and Vale, mlkem-native and mldsa-native, libcrux, fiat-crypto, curve25519-dalek's Lean proofs, Aeneas and Charon, SymCrypt's verified branch).
- Gaps already planned as children keep their quests: update a child whose route the survey changes, plan only new gaps, and delete a child whose gap a landed proof closed.
- Each route proves the code rind runs; a proven switch is a route only if it measures as fast. Settled choices hold: Aeneas to Lean and the m3 composition rule, rind's HOL Light in `proofs/hol-light/`, pins of unmerged upstream specs noted on the ✓, and no standing approval to post outside the moq-dev and kixelated orgs.
- Check first, from #448's survey: whether [awslabs/s2n-bignum#415](https://github.com/awslabs/s2n-bignum/pull/415), [#420](https://github.com/awslabs/s2n-bignum/pull/420), and [#450](https://github.com/awslabs/s2n-bignum/pull/450) merged (the SHA-2 children then move off their pins); whether s2n-bignum proves its aarch64 AES-GCM kernels in place or adds EVEX decoding ([#462](https://github.com/awslabs/s2n-bignum/pull/462)); whether Aeneas translates `&dyn` method calls ([AeneasVerif/aeneas#1500](https://github.com/AeneasVerif/aeneas/issues/1500)); and ML-DSA, which has landed in rind (by 2026-11-12), since s2n-bignum and mldsa-native already prove its polynomial routines on both architectures.
- Once [#420](https://github.com/awslabs/s2n-bignum/pull/420)'s spec merges, offer awslabs/s2n-bignum rind's aarch64 SHA-512 proof, `proofs/hol-light/aarch64/sha512_block_data_order_hw.ml`, together with its SHA-256 proof from [kixel-ai/rind#552](https://github.com/kixel-ai/rind/pull/552) (maintainer, 2026-11-12, on [kixel-ai/rind#661](https://github.com/kixel-ai/rind/pull/661): ✅ offer both once #420 merges (rejected: offer now)).
- Findings that need their own work are follow-ups for `/quest-plan`.

## Required

- [m3: deferred](/quest/m3/README.md) - the milestone this run closes
