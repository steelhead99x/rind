# [M] The portable backend's Keccak-f is proven or replaced

## Goal

The portable backend's Keccak-f permutation (`rind/src/low/portable/keccak.rs`, hand-ported) is either proven against a Keccak-f[1600] spec, or replaced by a verified implementation (such as libcrux/HACL*'s) that measures as fast at every size, so no portable path runs an unverified Keccak-f under SHA-3 and ML-KEM.

## Plan

Moved from m3 with the maintainer on 2026-11-09: ✅ m4, beside [the SHA-3 sponge](/quest/m4/verified/sha3-sponge.md) it composes with and [the rest of the portable backend's proofs](/quest/m4/verified/portable.md) (rejected: m5 with the cold tiers' hand-written proofs, since this one is the cheap kind; staying in m3).

Planned with the maintainer on 2026-11-07, a follow-up of [moq-dev/rind#458](https://github.com/moq-dev/rind/pull/458), which added the portable backend and left this the only unverified Keccak-f on a portable path.

- Speed rule (maintainer, 2026-11-09): ✅ run the fastest permissively licensed source, take a verified one only where it measures as fast at every size, and otherwise run the fastest and plan its proof (rejected: verified code within about 10% on cold tiers only; or everywhere, as `AGENTS.md` said). This replaces the 10% allowance this quest was planned under.
- Measure the candidates on the portable backend first (forced on x86_64 and on an aarch64 runner), at every size the SHA-3 and ML-KEM benchmarks time. Replace the hand port only with a verified Keccak-f that is as fast at each.
- If the hand port stays, because it is the fastest, prove it with Aeneas against the same spec [the SHA-3 sponge quest](/quest/m4/verified/sha3-sponge.md) uses, so the two compose.
