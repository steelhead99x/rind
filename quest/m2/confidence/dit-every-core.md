# [S] rind sets DIT on every aarch64 core that has it

## Goal

On every aarch64 CPU with FEAT_DIT, not only Apple's, each rind call that handles a secret sets PSTATE.DIT at entry and restores it on return, or holds it across a batch under `rind::cpu::Dit::hold()`. The docs cite Arm's own guidance for why.

## Plan

Decided 2026-11-21 (maintainer, /quest-plan): ✅ set DIT on every core with FEAT_DIT (rejected: keep Apple-only and reword the docs; skip only Neoverse V1 by MIDR). This reverses the 2026-11-08 narrowing recorded in [the QUIC path quest](/quest/m3/quic-path.md) and made in [moq-dev/rind#503](https://github.com/moq-dev/rind/pull/503).

- The narrowing rested on a comment on [openssl/openssl#28764](https://github.com/openssl/openssl/pull/28764) (2025-11-25), "the DIT setting will have no effect on any current Arm hardware", from an account that states no employer. Arm's own [KA005181](https://developer.arm.com/documentation/ka005181/1-0/) says less. Arm is aware of no timing variation in the covered instructions on cores from before FEAT_DIT. It vouches only for "some" cores that have FEAT_DIT, naming Neoverse V1, and "strongly recommends" that software set PSTATE.DIT. On the same PR, Arm's Tom Cosgrove wrote on 2026-11-16 that without DIT "we do not have a guarantee of constant-time processing … from the CPU". No source covers custom cores such as AmpereOne, Qualcomm Oryon, or Fujitsu's, or Arm's cores after KA005181's list.
- The cost is the `mrs` and `msr` of PSTATE.DIT at each call's entry and exit, not slower crypto: about 1.6 ns a call on Neoverse N2, 11% of a header-protection call ([moq-dev/rind#503](https://github.com/moq-dev/rind/pull/503)). Re-measure on the weekly bench's aarch64 runners with and without `Dit::hold()`, and record the per-call cost in BENCHMARKS.md as the Apple rows do.
- Drop the `target_vendor = "apple"` gate on DIT in `low/aarch64/cpu.rs`, `enter_cpu_state` and `leave_cpu_state`, keeping detection as is: a core without FEAT_DIT runs without it, as the M1 and M2 do on Apple. Decide in the PR whether the speculation barrier after setting DIT, which Apple asks for, stays Apple-only. Arm asks for none in KA005181, so keep it Apple-only unless Arm's documentation of FEAT_DIT says otherwise. Run the DIT tests (`enables_dit_whenever_the_cpu_has_it`, `dit_hold_keeps_dit_on_across_calls`) on every aarch64 target.
- Where rind's own adapters process a batch, such as rind-rustls's QUIC packet and header protection, take `Dit::hold()` around it if the measurement shows the toggle costs more than a few percent there.
- Reword PLATFORMS.md's aarch64 entry and its `Dit::hold()` note, README.md's Data-independent timing section, AUDIT.md's speculation barrier note, and [the QUIC path quest](/quest/m3/quic-path.md)'s DIT decision, citing KA005181. Keep the README's point that aws-lc-rs and ring never set DIT: aws-lc's `ENABLE_DATA_INDEPENDENT_TIMING` defaults to off, and aws-lc-sys does not turn it on.
