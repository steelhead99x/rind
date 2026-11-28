# Barrier after `msr DIT, #1` on Apple aarch64: sources and options

Research date: 2026-11-22, for fork issues #259 to #266 and PR #292's measuring cfgs. Scope: what rind's `barrier_after_set` (rind/src/low/aarch64/cpu.rs) should emit after `msr DIT, #1` on Apple targets. "Verified" means I read the quoted text in the primary source myself. Anything marked **UNVERIFIED** I could not confirm from a primary source.

## Decision (project owner, 2026-11-23)

1. **Non-Apple aarch64: no barrier after `msr DIT, #1`.** This follows the Arm ARM (DDI 0487 M.d), which requires none: C5.1.3.3 ("Writes to PSTATE occur in program order without the need for additional synchronization") and B1.5.6 (instructions speculatively executed after the 0 to 1 change are part of the data-independent-time sequence). On those cores the guarantee rests on that architectural rule alone. It has not been tested on any non-Apple hardware by us. Since upstream's #1005 (2026-11-24) rind sets DIT on every aarch64 core whose OS reports it, so this is the shipped default off Apple.
2. **Apple targets keep Apple's documented sequence:** `sb` where the core has FEAT_SB (detected at run time, as before), else `dsb nsh; isb sy`. Detection of Apple is at compile time (`target_vendor = "apple"`).
3. **The FIPS module keeps Apple's sequence on every target**, and still refuses `--cfg rind_dit_barrier="isb"` and `"none"` at compile time. Since upstream's #1005 the module sets DIT on its glibc Linux aarch64 cores, so this sequence runs there.
4. **Key wipes on drop stay outside DIT** (benchmarks/apple-dit-coverage.md, "Wipes on drop run outside DIT"): a wipe stores zeros and loads none of the secret.
5. **Autohold (`--cfg rind_dit_autohold`, fork PR #302) stays a measuring prototype only.** The supported way to coalesce toggles is the guard API: `Dit::hold`, `Dit::with`, `Dit::batch`.

Implemented in `rind/src/low/aarch64/cpu.rs`, `dit::barrier_after_set` and `dit::apple_barrier`. The measuring cfgs remain for the owner's A/B, on any target: `rind_dit_barrier="apple"` (Apple's sequence), `"isb"` (`isb sy` alone), `"none"` (no barrier). `admin/dit-disasm` (dispatch module `ditbarrier`) builds the release rlib and checks every path from each `msr DIT, #1`: on `aarch64-apple-darwin` each ends in `sb` or `dsb nsh; isb` and both appear; on `aarch64-unknown-linux-gnu` none reaches a barrier; and with `rind_dit_barrier="apple"` on Linux both appear again, so the scan is shown to see a barrier when one is there.

No speed is claimed for the change: nothing here ran on Apple hardware. On Apple targets the emitted code is the same sequence as before the decision.

## TL;DR

- **Arm architecture:** no barrier is needed for program-order correctness. PSTATE writes "occur in program order without the need for additional synchronization". Instructions speculatively executed after the DIT 0 to 1 change are architecturally part of the data-independent-time sequence.
- **Apple:** Apple explicitly asks for a speculation barrier (`sb`, else `dsb nsh; isb sy`) after setting DIT, and gives no rationale. Apple's own libplatform and corecrypto use `sb`, else `dsb sy; isb sy` (note **`sy`, not `nsh`**).
- **Other libraries:** as of November 2026, Go, aws-lc and BoringSSL all add the barrier **on Apple only**, and skip it when DIT was already on. graviola and the Linux kernel use no barrier.
- **rind's doc comment was stale in two places** (fixed with the decision above). aws-lc's `armv8_set_dit` is no longer a bare `msr` on Apple. Also, `cc_timing_safe.c` uses `dsb sy`, not `dsb nsh`; rind's `dsb nsh; isb sy` comes from Apple's developer page, as Go's, aws-lc's and BoringSSL's do.

## 1. Arm Architecture Reference Manual (DDI 0487 M.d, published 2026-09-29)

Source PDF: [DDI0487M_d_a-profile_architecture_reference_manual.pdf](https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1?token=), from [developer.arm.com/documentation/ddi0487/latest](https://developer.arm.com/documentation/ddi0487/latest). All quotes below are verified against that PDF.

**PSTATE writes via MSR (immediate).** Section C5.1.3.3, "Instructions for accessing the PSTATE fields" (page C5-933/934), lists `MSR UAO`, `MSR PAN`, `MSR DIT`, `MSR SSBS`, `MSR TCO` (among others), then says:

> "Writes to PSTATE occur in program order without the need for additional synchronization."

**DIT as a Special-purpose register (MSR register form, as used by BoringSSL and XNU).** Section C5.1.5.1, "Instructions for accessing Special-purpose registers" (page C5-948):

> "All direct and indirect reads and writes to Special-purpose registers appear to occur in program order relative to other instructions."

D2.11 (Software Step exceptions) also has a note: "A direct write to a Special-purpose register does not require explicit synchronization."

**MSR (immediate) is not a Context synchronization event.** The Glossary entry "Context Synchronization event" lists only ISB, exception entry and return (conditional on FEAT_ExS / SCTLR_ELx.EIS), exit from Debug state, DCPS and DRPS. MSR is not on the list. Go's commit [fa8595702eba](https://github.com/golang/go/commit/fa8595702eba16f757860705157f17f8054a92df) says Arm "explicitly states that MSR of a PSTATE bit is a context synchronization event". That misreads Arm's wording: Arm says such writes are ordered, not that they are a CSE.

**FEAT_DIT definition.** Section A2.2 "Armv8-A architecture extensions", "FEAT_DIT, Data Independent Timing instructions":

> "FEAT_DIT is OPTIONAL from Armv8.3. FEAT_DIT is mandatory from Armv8.4."

C5.2.4 "DIT, Data Independent Timing" defines bit 24. With 0b1: "The architecture requires that the execution time of a data-independent-time sequence of code must be independent of all data-independent-time values."

**DIT and speculation.** Section B1.5.6 "About PSTATE.DIT" (page B1-243):

> "A data-independent-time sequence of code is the sequence of instructions executed from the first instruction executed after a change of PSTATE.DIT from 0 to 1 through the last instruction executed before a change of PSTATE.DIT from 1 to 0, inclusive. Instructions speculatively executed between the change of PSTATE.DIT from 0 to 1 and the change of PSTATE.DIT from 1 to 0 are considered part of the data-independent-time sequence of code."

The same section counts speculative and prefetch reads as data-independent-time values. The list includes "Any given value (V) speculatively read from memory at a Location (L) as the result of executing a data-independent-time sequence of code ... Examples of this include: ... Hardware-generated prefetches." That clause is the architectural hook for data memory-dependent prefetchers (DMPs, the GoFetch case).

One caveat matters for code ordering. Per the B1.5.6 note, execution time may still vary with the value in L if L is accessed "Outside the data-independent-time sequence of code, either architecturally or speculatively." So DIT must be on **before** secrets are loaded. A barrier after the `msr` does not help with loads placed before it. That ordering is a compiler and program-order concern (`asm volatile` plus a memory clobber).

**SB versus ISB versus DSB.**
- B2.6.3 "Speculation Barrier": "An SB instruction is a memory barrier that prevents speculative execution of instructions until after the barrier has completed when those instructions could be observed through side-channels." SB completes when the barrier "is known that it is not speculative" (with exception-related carve-outs) and "All the data values generated by instructions appearing in program order before the SB instruction are architecturally resolved". FEAT_SB is "OPTIONAL from Armv8.0" and "mandatory from Armv8.5" (A2.2).
- B2.6.1 "Instruction Synchronization Barrier": "An ISB instruction ensures that all instructions that come after the ISB instruction in program order are fetched from the cache or memory after the ISB instruction has completed." From the Glossary on Context synchronization events: "No instructions appearing in program order after an instruction that causes a Context synchronization event will have performed any part of their functionality until the Context synchronization event has occurred."
- B2.6.2 (DMB) and the DSB text order memory effects. They make no statement about stopping speculative execution. The manual does not, as far as I found, define `dsb; isb` as an SB substitute. Linux uses `dsb nsh; isb` as its SB fallback ([barrier.h `spec_bar()`](https://github.com/torvalds/linux/blob/b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f/arch/arm64/include/asm/barrier.h#L43)).

**Exceptions and context switch.** B1.5.6 (page B1-245):

> "On an exception that is taken from AArch64 state to AArch64 state, PSTATE.DIT is copied to SPSR_ELx.DIT." and "On an exception return from AArch64 state: SPSR_ELx.DIT is copied to PSTATE.DIT, when the target Exception level is in AArch64 state."

SPSR_EL1 (C5.2.21) repeats this. Exception entry does not modify PSTATE.DIT. In the pseudocode, DIT is written only by MSR, by exception return and at reset, unlike SSBS, which is loaded from SCTLR_ELx.DSSBS. So DIT is per-thread state that the OS saves through SPSR, and it survives preemption and migration.

## 2. Arm guidance on DIT

- [Arm KA005181, "How is instruction timing affected by the FEAT_DIT architectural feature?"](https://developer.arm.com/documentation/ka005181/1-0/) (2024-02-14), verified: "Arm is not aware of any Arm processor implementations from before the introduction of FEAT_DIT that exhibit data value timing variation for the instructions covered by FEAT_DIT". "Some Arm processor implementations which implement FEAT_DIT (such as the Neoverse-V1) do not exhibit data value timing variation ... irrespective of the PSTATE.DIT setting. This being said, Arm strongly recommends that software transitions to adopting the correct usage". Also, "software should transiently set PSTATE.DIT". It says nothing about barriers.
- [Arm "Learn the architecture: ARMv8-A memory systems", Barriers (100941/0101)](https://developer.arm.com/documentation/100941/0101/Barriers), verified: "This does not mean that an ISB is required after each instruction that modifies a processor register. For example, reads or writes to PSTATE fields, ELRs, SPs, and SPSRs always occur in program order relative to other instructions."
- **UNVERIFIED:** any separate Arm "DOIT" note or "Arm CPU Security update" page on DIT. I did not locate one.

## 3. Apple

**Developer page.** [Writing ARM64 code for Apple platforms, "Enable DIT for constant-time cryptographic operations"](https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms#Enable-DIT-for-constant-time-cryptographic-operations), read through the page's DocC JSON. Verified quotes:
- "To ensure that subsequent instruction timing reflects the updated DIT processor state, add a speculation barrier after turning on DIT. Use the `sb` instruction to add a speculation barrier". The sample is `msr dit, #1` followed by `sb` with a `"memory"` clobber.
- "When speculation barriers aren't supported, use:" `dsb nsh` then `isb sy`, each with a `"memory"` clobber.
- `timingsafe_enable_if_supported` (iOS 18.2 / macOS 15.2 and later) "uses safeguards adequate for the device CPU to limit the speculative computation; for example, speculation barriers (SB)."
- On DIT state: "you can turn DIT on or off separately on different threads". DIT should be on "before loading cryptographic key material".
- The restore sample (`msr dit, #0`) has no barrier. Apple gives no rationale for the enable barrier.

**libplatform (the shipped `timingsafe_enable_if_supported`).** [src/timingsafe/arm64/timingsafe.c](https://github.com/apple-oss-distributions/libplatform/blob/2512ffd8bb5c6caff3c8ea83331ab8a0adc820c3/src/timingsafe/arm64/timingsafe.c), verified:
- `speculation_barrier()` emits `sb` if `kHasFeatSB`, else `__builtin_arm_dsb(BARRIER_SY); __builtin_arm_isb(BARRIER_SY)` with `#define BARRIER_SY (0xf)`. That is `dsb sy; isb sy`.
- The barrier is called even when DIT is unsupported or already on.
- Restore has no barrier.

**corecrypto.** [cc/src/cc_timing_safe.c](https://github.com/apple/corecrypto/blob/9612a959abb6eac0aac3ee6a7245c46365c9d81b/cc/src/cc_timing_safe.c), verified: the same code, `sb` if `CC_HAS_SB() && CC_INTERNAL_SDK`, else `dsb sy; isb sy` (`BARRIER_SY 0xf`). **This contradicts rind's comment that it models `dsb nsh` on this file.**

corecrypto also keeps a legacy path in [cc_internal.h](https://github.com/apple/corecrypto/blob/9612a959abb6eac0aac3ee6a7245c46365c9d81b/cc/corecrypto/cc_internal.h): `cc_enable_dit()` emits `.long 0xd503415f` (`msr dit, #1`) with no barrier. Per [cc_config.h](https://github.com/apple/corecrypto/blob/9612a959abb6eac0aac3ee6a7245c46365c9d81b/cc/corecrypto/cc_config.h), the barrier path (`CC_DIT_WITH_SB_MAYBE_SUPPORTED`) is disabled for `CC_USE_L4`, `CC_USE_SEPROM`, `CC_IBOOT` and `CC_TXM` builds.

**Apple Platform Security guide: UNVERIFIED.** A search snippet attributes DIT wording to it, but I did not open the guide and confirm.

## 4. GoFetch (Chen et al., USENIX Security 2024)

[gofetch.fail](https://gofetch.fail/) and the [paper PDF](https://gofetch.fail/files/gofetch.pdf), verified. Footnote 22: "We observe that setting the data independent timing (DIT) [1] bit disables the DMP behavior on M3, which is not the case with M1 and M2." The site's mitigation text says developers "can ... set the DOIT bit and DIT bit bits, which disable the DMP on some CPUs."

The paper does not discuss barriers or the timing of enabling DIT. The claim "DIT is needed only while secrets are loaded" is **not stated by GoFetch** (UNVERIFIED there). The closest primary text is Arm B1.5.6, quoted above: values accessed outside the DIT sequence, even speculatively, are not covered. M4 and A17 Pro DMP behaviour under DIT: **UNVERIFIED** (no primary source found).

## 5. What other code does after setting DIT

| Project | After `msr DIT, #1` | Source (verified) |
|---|---|---|
| Go 1.26+ runtime (`crypto/subtle.WithDataIndependentTiming`) | darwin only: `SB` if `HasSB`, else `DSB $7` (nsh) + `ISB $15` (sy). Skipped if DIT was already on. Other OSes: none. | [dit_arm64.s](https://github.com/golang/go/blob/4f55df07b9744679e23218b5b277f6de9cb4bed7/src/internal/runtime/sys/dit_arm64.s); barrier added in [2244bd7](https://github.com/golang/go/commit/2244bd7eeb17cb3d361908d3a441ecfc2c4a82b5) (CL 726980, "The Arm documentation for DIT doesn't tell you to do this, but it seems prudent"), limited to darwin in [fa85957](https://github.com/golang/go/commit/fa8595702eba16f757860705157f17f8054a92df) ([go.dev/issue/77776](https://go.dev/issue/77776)) |
| aws-lc `armv8_set_dit` | `OPENSSL_APPLE` only: `sb` (encoded `0xd50330ff`) if SB, else `dsb nsh; isb sy`. Skipped if DIT already on. | [cpu_aarch64.c](https://github.com/aws/aws-lc/blob/8ebd7a8191c9895c96d144ca969412a23aec4a8b/crypto/fipsmodule/cpucap/cpu_aarch64.c), added 2026-11-17 in [#3751](https://github.com/aws/aws-lc/commit/410f7bab88c1d28523e1cabffc29627582a45a7f). **rind's "bare msr" note is now stale.** |
| BoringSSL `ConstTimeGuard` | Uses MSR register form (`msr S3_3_C4_C2_5, Xt`). `OPENSSL_APPLE` only: `sb`, else `dsb nsh; isb sy`. Only when DIT was off. | [crypto/crypto.cc](https://github.com/google/boringssl/blob/289645a450721a7210bf9c69d42bf40a0f1ee730/crypto/crypto.cc) (DIT support relanded 2026-11-16) |
| graviola | `msr DIT, #1`, no barrier | [graviola/src/low/aarch64/cpu.rs](https://github.com/ctz/graviola/blob/246ae105d8015dccdefc360eaa912a157e068695/graviola/src/low/aarch64/cpu.rs) |
| OpenSSL | No DIT support found | GitHub code search for `msr dit` and `0xd503415f` in openssl/openssl returned nothing (**UNVERIFIED** as an absence) |
| Linux kernel | `alternative_insn nop, SET_PSTATE_DIT(1)` at `kernel_entry` from EL0, no barrier | [01ab991fc0ee](https://github.com/torvalds/linux/commit/01ab991fc0ee5019aecc4ca461311fc8aa75ece5), "arm64: Enable data independent timing (DIT) in the kernel" |
| XNU | Saves and restores kernel DIT per thread with `mrs/msr DIT, x`, no barrier | [osfmk/arm64/cswitch.s](https://github.com/apple-oss-distributions/xnu/blob/f6217f891ac0bb64f3d375211650a4c1ff8ca1ea/osfmk/arm64/cswitch.s) |

**Linux notes.** The "2022 RFC" was merged: commit 01ab991fc0ee (Nov 2022) went into Linux 6.2 per [oss-security 2023/01/25/3](https://www.openwall.com/lists/oss-security/2023/01/25/3); I verified the commit, and the version comes from that post. The commit message says "The DIT bit is part of PSTATE, and is therefore context switched as usual, given that it becomes part of the saved program state (SPSR) when taking an exception". I found no 2024 or 2025 follow-up DIT series (**UNVERIFIED** absence).

**Linux signal delivery.** In [signal.c](https://github.com/torvalds/linux/blob/b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f/arch/arm64/kernel/signal.c#L1495-L1511), `setup_return` changes only BTYPE and "TCO (Tag Check Override) always cleared for signal handlers". DIT is not touched, so a handler inherits the interrupted DIT state. On sigreturn, `pstate` is restored from `uc_mcontext`, and [`valid_native_regs`](https://github.com/torvalds/linux/blob/b6a9fa34ce4187cb69d3c588a4bbffc31ce5db8f/arch/arm64/kernel/ptrace.c#L2514-L2550) clears only RES0 bits, which do not include bit 24.

**XNU signal delivery (my reading of source, not tested).** [`sendsig_set_thread_state64`](https://github.com/apple-oss-distributions/xnu/blob/f6217f891ac0bb64f3d375211650a4c1ff8ca1ea/bsd/dev/arm/unix_signal.c#L172-L189) passes `cpsr = PSR64_USER64_DEFAULT` to `thread_setstatus`. [`thread_state64_to_saved_state`](https://github.com/apple-oss-distributions/xnu/blob/f6217f891ac0bb64f3d375211650a4c1ff8ca1ea/osfmk/arm64/status.c#L118-L160) documents: "ts64->cpsr.{N,Z,C,V} are copied as-is ... All other saved_state->cpsr bits are preserved as-is". So the handler appears to inherit DIT. A handler that clears DIT without restoring it might leave it cleared after sigreturn. **UNVERIFIED** by experiment.

## 6. Analysis and recommendation

**What is architecturally required.** Nothing. The Arm ARM (C5.1.3.3, C5.1.5.1) puts the DIT write in program order. B1.5.6 covers instructions speculatively executed after the 0 to 1 change. On a conforming core, `none` is correct. The real hazard is ordering secret loads after the `msr` in program order. `asm volatile` with a memory clobber, without `nomem`, handles that, and no barrier fixes it if it is wrong.

**What speculation could do in the window.**
- If an implementation applied the new DIT value only at some later pipeline point, younger instructions already in flight could execute with DIT-off timing or DMP behaviour. The Arm text forbids this for conforming cores.
- Apple's insistence on a barrier suggests, but does not prove, that Apple cores may not guarantee this. Apple publishes no rationale (**UNVERIFIED** motive).
- SB is the instruction Arm defines to stop side-channel-observable speculation of younger instructions (B2.6.3).
- ISB alone guarantees later instructions are refetched and do not "perform any part of their functionality" before it (Glossary, CSE). That is plausibly sufficient for this window, but no source (Apple, Arm, or any library) prescribes `isb` alone for this purpose. Its adequacy on Apple cores is **UNVERIFIED**.

**What Apple asks.** `sb`, else `dsb nsh; isb sy` (developer page). Apple's own shipping code uses `dsb sy; isb sy` as the fallback. `dsb nsh` versus `dsb sy` only changes the shareability domain of the completion wait. For a local speculation fence, `nsh` matches both Apple's public doc and Linux `spec_bar()`. Whether the difference matters on Apple cores is **UNVERIFIED**.

**What is cheapest.** `none`, by construction. I make no claims about the relative cost of `sb`, `isb sy` and `dsb nsh; isb sy` on any Apple core: no measurements were taken.

**Ecosystem consensus (Nov 2026).** Go, aws-lc and BoringSSL settled on the same rule: barrier on Apple only (`sb`, else `dsb nsh; isb sy`), skipped when DIT was already set, no barrier on disable. That matches rind's current default, with the nesting skip as a possible refinement.

**Suggested next steps (for the owner, not applied):**
1. Fix the doc comment in `barrier_after_set`:
   - Cite libplatform/corecrypto accurately (`dsb sy; isb sy`), or cite the Apple developer page as the source of `dsb nsh; isb sy`.
   - Update the aws-lc note (#3751) and add Go (go.dev/issue/77776) and BoringSSL.
   - Note that the Linux patch was merged in 6.2.
2. Skipping the `msr` and barrier when DIT is already on, as Go, aws-lc and BoringSSL do: rind already does this. `dit::maybe_enable` reads PSTATE.DIT first and writes (and runs the barrier) only when it finds it clear, and a nested `Entry` or guard finds it set (checked by `a_caller_set_dit_survives_every_call_and_guard` in `rind/src/low/entry/tests.rs` on the audit branch).
3. Keep the `isb sy` and `none` cfgs as measurement aids only. On the evidence above, `none` is architecturally sound and `sb` (else `dsb nsh; isb sy`) is what Apple asks for. `isb`-only has no source behind it.

## Measurements still wanted (the decision above is made; these inform any later change on Apple)

The Apple default (`sb` when FEAT_SB, else `dsb nsh; isb sy`) is unchanged by the decision. Measurements of the barrier variants (`sb`, `dsb nsh; isb sy`, `isb sy`, none) would still inform the owner, on:
- M1 (no FEAT_SB, per the task brief; I did not verify M1's FEAT_SB status from a primary source)
- iPad with M4
- iPad (or device) with A17 Pro

Measure both raw cost per enable and end-to-end cost for rind's real call sites.

## Verification summary

**Verified from primary sources:**
- Arm ARM M.d quotes (C5.1.3.3, C5.1.5.1, D2.11 note, Glossary CSE, B1.5.6, C5.2.4, B2.6.1, B2.6.3, A2.2 FEAT_DIT/FEAT_SB)
- Arm KA005181 and the 100941 Barriers page
- Apple developer page text
- libplatform, corecrypto, XNU, Go, aws-lc, BoringSSL, graviola and Linux source and commits as linked
- GoFetch footnote 22

**UNVERIFIED:**
- Apple's rationale for the barrier
- Apple Platform Security guide wording
- Any Arm "DOIT" or security-update note
- Adequacy of `isb` alone on Apple cores
- Whether `dsb nsh` versus `dsb sy` matters
- DMP behaviour under DIT on M4 / A17 Pro
- M1 lacking FEAT_SB
- OpenSSL having no DIT support
- No later Linux DIT series
- XNU signal DIT inheritance (source reading only)
- All performance questions
