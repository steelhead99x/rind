# [S] rind builds on every target ring or aws-lc-rs supports

## Goal

rind and rind-rustls build and run on every architecture that ring 0.17 or aws-lc-rs supports, and the rind library compiles for wasm32, so a library can depend on rind alone without dropping targets its users build. Architectures with no assembly in rind get one portable Rust backend. Each one's CI runs the tests under qemu.

Non-goals: the adapters on wasm (browsers bring their own TLS). Speed on the new architectures is [m3's](/quest/m3/cold-speed/README.md), not this epic's.

## Plan

Decided with the maintainer on 2026-11-06, in moq-dev/web-transport's planning interview ([moq-dev/web-transport#478](https://github.com/moq-dev/web-transport/pull/478)) (✅ chosen):

- Goal: ✅ ring ∪ aws-lc-rs, minus wasm / only web-transport's CI targets / skip wasm32 only.
- Backend: ✅ a portable fallback generalized from armv7's libcrux path / per-arch assembly.
- Placement: ✅ m2 adoption / m1 / m3 parity.
- Split: ✅ epic, one child per architecture family / one [XL] quest.
- wasm (2026-11-09, landing [moq-dev/rind#543](https://github.com/moq-dev/rind/pull/543)): ✅ compile-only, checked on every PR, since an outside user needs it (rejected: nightly best-effort; stay a non-goal). This replaces the 2026-11-06 "minus wasm".
- Consumer: moq-dev/web-transport goes rind-only now on its x86_64/aarch64/armv7 release targets. Its library users on other architectures are the reason for this epic.

wasm tests (maintainer, 2026-11-09, in the quest audit, reconciling the compile-only answer above with one given the same day): ✅ both, the compile gate now and vector tests under wasmtime after it (rejected: compile-only, with tests a non-goal).

Speed (maintainer, 2026-11-09, after an audit of the whole tree): ✅ planned, in m3 (rejected: a non-goal until a consumer measures a problem; m2 beside these targets; m4).

The union of ring 0.17's and aws-lc-rs's CI and build scripts, listed on 2026-11-06, adds armv6, which both test. It drops i586, which ring refuses for lacking SSE2 and aws-lc-rs doesn't test. riscv32 and sparc64 are compile-only in both, as loongarch64 is, so they wait for a consumer. aarch64_be and armeb, which ring compiles and aws-lc refuses, compile the portable backend, untested.

"Exactly one backend compiles per architecture" still holds: the portable backend is each new architecture's only backend, not a fallback for a missing CPU feature. The s390x quest checked byte order: rind's tests pass on big-endian s390x and 32-bit powerpc, so big-endian targets need only their CI.

The epic's own work, once every child has merged:

- Rewrite [MIGRATE.md](/MIGRATE.md)'s rule that a library keeps its old backend as the default: a library whose targets rind covers may go rind-only.
- Update [PLATFORMS.md](/PLATFORMS.md) and the README's Limitations.
