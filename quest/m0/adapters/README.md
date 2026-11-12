# [XS] Adapters offer exactly their upstream's API

## Goal

Each published `rind-<consumer>` adapter offers exactly the API of the provider its upstream ships, so swapping one for the other changes no other code. Each README lists only what rind cannot back.

## Plan

A 2026-11-08 comparison of each adapter's rustdoc surface against its upstream found additions, changed signatures, and renamed items. Decided with the maintainer on 2026-11-08:

- Adapters must have identical APIs, with no exceptions ✅ (rejected: a carve-out for additions that replace what upstream's built-in provider does implicitly). A divergence is a bug: fix it in a patch release with the version set by hand, and yank the divergent releases if needed. AGENTS.md and CONTRIBUTING.md now say so.
- Milestone: now, m0 ✅ (rejected: m2 beside the API epic, m3 beside the parity epic).
- Every adapter's `MissingFeature`, and the `Result` it puts on `default_provider()` and its kin, diverges from upstream. Each child removes it from its adapters by no longer calling `rind::cpu::check()`, which can't fail on any target rind builds for. rind's own `check()` goes in [rind needs no runtime CPU check](/quest/m2/api/cpu-check.md). Until it lands, a debug or `--cfg rind_cpu_disable` aarch64 build run with `RIND_CPU_DISABLE_neon` panics in `verify_cpu_features` on the first operation instead of erroring at `default_provider()`; that test-only toggle needs no handling here, and that quest deletes both.
- rind-object-store and rind-instant-acme have no upstream provider shape to copy: object_store's are `pub(crate)`, and instant-acme's are associated functions. rind-object-store keeps its `default_provider()`, which MoQ's moq-cli uses; rind-instant-acme was deleted in [moq-dev/rind#510](https://github.com/moq-dev/rind/pull/510), since it had no consumer.
- Behavior that isn't API stays where rind has a reason, documented in each README: rind-rustls and rind-dimpl put ChaCha20-Poly1305 first on CPUs without AES instructions, and rind-rustls lists AES-128-GCM before AES-256-GCM, for speed.
- Each child ends with its adapter's README and MIGRATING.md section listing only the remaining omissions.

Decided with the maintainer on 2026-11-09:

- Releases: one rind 0.4 that carries all three breaking changes, and a MoQ-side PR ready before the adapter patch releases publish ✅ (rejected: the 0.4 quest alone, accepting that MoQ's build breaks until fixed; leaving both to release-plz). rind 0.4 is in [rind 0.4 ships once](/quest/m2/api/release-0.4.md).
- The children change calls MoQ's `main` makes: `default_provider()` in rind-rustls, rind-jsonwebtoken, and rind-object-store, and `KeyPair::generate` and `to_pkcs8` in rind-rcgen. MoQ requires those adapters by caret (moq-dev/moq's `Cargo.toml:218-221`), so its first lockfile update after the patch releases stops building until its calls change. No crate MoQ has published names a rind adapter yet, so only `main` and its next cut are exposed.
- The adapter patch releases therefore publish only once MoQ's PR adapting those calls is ready to merge. Publishing happens only when a release PR merges (`CONTRIBUTING.md:138`), so the maintainer leaves the release PR that carries them unmerged until then, and MoQ's PR merges the day they publish. That PR is a quest in moq-dev/moq's own tree.
- Since rind 0.4 is pending on `main` ([moq-dev/rind#548](https://github.com/moq-dev/rind/pull/548) leaves release-plz to propose it), these fixes publish in the same release as rind 0.4, each adapter requiring it, so MoQ's PR moves to both at once.
