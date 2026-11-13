# [L] Spike: one patch line moves a RustCrypto tree to rind

## Goal

The maintainer has a report, from a spike, on whether a binary can move every crate in its tree from RustCrypto's `sha2` and `aes-gcm` to rind with one `[patch.crates-io]` entry each, as `rind-patch` does for ring: for two or three popular open-source dependency trees, how much builds, how much of each project's own test suite passes, what speed changes, and what blocks the rest. It ends with a recommendation to build the shims as a product or drop them.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ spike it. This is the bold one: if it works, any Rust binary tries rind without touching a line of its dependencies' code, and if it does not, the report says why and nobody wonders again.

- How ring's works today, to copy: an unpublished crate named `ring`, in its own repository, re-exports rind-ring at version `0.17.999`, and a binary adds `[patch.crates-io] ring = { git = ... }` (MIGRATING.md's ring section, and `patch/fixture` with `sh/patch.sh`, which test it).
- Start with `sha2`, the most-downloaded concrete crate, and `aes-gcm`, where [adoption](/quest/m2/adoption/README.md) has rind about twice as fast. They are the two ends of the difficulty. `sha2` 0.11's public API is a few types and their trait impls. `aes-gcm` is generic over a block cipher and nonce size (`AesGcm<Aes, NonceSize, TagSize>`), and a shim can back only the instantiations rind has.
- The hard parts to report on, not to solve in full: a tree can hold several majors of `sha2` at once, 0.10 and 0.11 both being in wide use, and each needs its own shim at its own version; a shim must satisfy every trait bound downstream code names, including `digest`'s internal block-level traits that some crates use directly; and features and `no_std` must match, since `[patch]` cannot change what a dependent asks for.
- A `sha2` 0.10 shim implements `digest` 0.10's traits, and [the trait adapter](/quest/m2/rustcrypto/traits.md) plans only each trait crate's current release, `digest` 0.11. The spike writes what a 0.10 shim needs itself, as throwaway code beside the shim, or tests only trees already on `sha2` 0.11. Either way the report says how many of the trees it looked at still hold 0.10, since that decides whether the product needs both.
- Pick the trees by who uses these crates heavily and has a test suite that runs offline. Use open-source projects only, and name them in the report with the commit tested.
- Keep the shims unpublished and out of the release, in this workspace beside `patch/fixture` for the spike. Where they would live as a product is part of the recommendation.
- The result is the report in the PR and a short section in this file's place: what built, what passed, the measured speed on each project's own benchmarks if it has any, and the recommendation. The maintainer decides; plan the product with `/quest-plan` if the answer is yes.

## Required

- [rind implements RustCrypto's traits](/quest/m2/rustcrypto/traits.md) - the current-release trait implementations a shim re-exports
