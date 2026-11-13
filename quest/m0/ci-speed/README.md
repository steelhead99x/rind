# CI stops making PRs wait

## Goal

rind's PRs and merge queue wait on machines only for real work: PR checks get a GitHub-hosted runner without queueing behind nightly and dispatched jobs, the merge queue loses its fixed overhead, and the heavy suites run at a cadence the hosted runners absorb. Once every child lands, re-measure the way this epic was planned and record the before and after in the last child's PR.

## Plan

Planned with the maintainer on 2026-11-12 from 14 days of Actions data (Oct 29 to Nov 12) and the agent transcripts on fedora, nixos, and desktop.

- moq-dev/rind is public, so hosted minutes are free; the cost is the org's cap of 60 concurrent hosted jobs. PR jobs waited p50 0.1 min but p90 37 min and p99 116 min for `ubuntu-latest`. About 4,050 hosted machine-hours ran in 14 days: dispatched `bench` 1,123 h, `mutants` on PRs about 700 h in two days (gone since [moq-dev/rind#668](https://github.com/moq-dev/rind/pull/668)), x86-cpu under SDE 239 h, `miri` on PRs 240 h with 0 of 34 runs finishing inside the 6 h timeout.
- The merge queue build itself is fast (median 2.5 min, runner idle 89%); its overhead is around it.
- ✅ Cut waste first, buy no hardware (rejected: a dedicated Ryzen 9950X or Threadripper runner; old Intel boxes for native SDE tiers; an Ampere Altra for native armv7). The Mac mini [already planned](/quest/m0/mac-mini-runner.md) is the only new machine.
- ✅ Heavy x86 suites stay on hosted runners at a weekly cadence (rejected: self-hosted on nixos, which also runs the queue).
- ✅ armv7 runs natively on GitHub's `ubuntu-24.04-arm` wherever CI still runs it under qemu on x86 (rejected: buying ARM hardware). ctgrind's `armv7-qemu` stays on qemu: Valgrind hides the crypto extension it checks.
- ✅ SDE keeps every CPU tier, weekly; PRs run only the tiers their diff can reach (rejected: buying the old CPUs to run them natively). Native masking with `rind_cpu_disable` picks a tier's paths but does not fault on an instruction the tier lacks, which is what SDE is for.
- ✅ These quests sit in m0, whose goal covers hosted CI that blocks every PR (rejected: m2).
- Re-measure with the Actions REST API: per-label wait from a job's `created_at` to `started_at`, merge-group build time, and machine-hours per workflow over the 14 days after the last child lands.

## Related

- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - adds the Mac mini as a second queue runner, which the queue overhead quest must not slow
- [Apple-silicon nightlies run on the Mac mini](/quest/m2/confidence/apple-nightlies.md) - takes the aarch64 and macOS heavy jobs off hosted runners
