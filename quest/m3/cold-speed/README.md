# The cold tiers are fast

## Goal

The portable backend and armv7 without the crypto extension run the fastest permissively licensed source for each primitive, as the hot tiers do, measured on the nightly's rows for them.

## Plan

Decided with the maintainer on 2026-11-09, after an audit of the whole tree: ✅ portable speed is planned (rejected: leave it a non-goal until a consumer measures a problem, as the targets epic had it before it closed), in ✅ m3 (rejected: m2 beside the targets, m4). The goal is everything fast and proven, the most important architectures first, and the m2 target quests land these architectures before their speed matters.

The audit's evidence is the nightly's portable row, which no gate reads: RSA, P-521, and AES-GCM run several times slower than aws-lc's C there. Each child states its own numbers and what must be measured first.

wasm32 runs this backend too, so it gains what these quests gain: wide arithmetic for the bignums where the host has it, and nothing rind-specific.
