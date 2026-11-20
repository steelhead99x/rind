# CI stops making PRs wait

## Goal

rind's PRs and merge queue wait on machines only for real work: PR checks get a GitHub-hosted runner without queueing behind nightly and dispatched jobs, the merge queue loses its fixed overhead, the heavy suites run at a cadence the hosted runners absorb, and hosted runners spend little on results no one reads: a draft's, a superseded push's, or one that arrives after its PR merged. Once every child lands, re-measure the way this epic was planned and record the before and after in this epic's PR.

## Plan

Planned with the maintainer on 2026-11-12 from 14 days of Actions data (Oct 29 to Nov 12) and the agent transcripts on fedora, nixos, and desktop.

- moq-dev/rind is public, so hosted minutes are free; the cost is the org's cap of 60 concurrent hosted jobs. PR jobs waited p50 0.1 min but p90 37 min and p99 116 min for `ubuntu-latest`. About 4,050 hosted machine-hours ran in 14 days: dispatched `bench` 1,123 h, `mutants` on PRs about 700 h in two days (gone since [moq-dev/rind#668](https://github.com/moq-dev/rind/pull/668)), x86-cpu under SDE 239 h, `miri` on PRs 240 h with 0 of 34 runs finishing inside the 6 h timeout.
- The merge queue build itself is fast (median 2.5 min, runner idle 89%); its overhead is around it.
- ✅ Cut waste first, buy no hardware (rejected: a dedicated Ryzen 9950X or Threadripper runner; old Intel boxes for native SDE tiers; an Ampere Altra for native armv7). The Mac mini [already planned](/quest/m0/mac-mini-runner.md) is the only new machine.
- ✅ Heavy x86 suites stay on hosted runners at a weekly cadence (rejected: self-hosted on nixos, which also runs the queue).
- ✅ armv7 runs natively on GitHub's `ubuntu-24.04-arm` wherever CI still runs it under qemu on x86 (rejected: buying ARM hardware). ctgrind's `armv7-qemu` stays on qemu: Valgrind hides the crypto extension it checks.
- ✅ Of `sh/armv7.sh`'s tiers, only the Cortex-A15 one, NEON without the crypto extension, stays under qemu; the crypto extension's and the NEON-denied one run natively (maintainer, 2026-11-17, rejected: the NEON-denied tier on qemu's Cortex-A15 too). The NEON denial is rind's software mask, and the Cortex-A15 tier's qemu run already faults on an instruction from the extension; natively, the NEON-denied tier no longer faults on a NEON instruction outside rind's dispatch, which saves about 33 min a run.
- ✅ SDE keeps every CPU tier, weekly; PRs run only the tiers their diff can reach (rejected: buying the old CPUs to run them natively). Native masking with `rind_cpu_disable` picks a tier's paths but does not fault on an instruction the tier lacks, which is what SDE is for.
- ✅ Pull requests run three SDE models, and the weekly run runs every model, the merge queue every model except the slow ones (gnr, cnl), which run in `queue-build.yml` and are not required until the host is confirmed (maintainer, 2026-11-18, /quest-plan; rejected: every model on pull requests). This refines the line above: nearly every `rind/src` change reaches x86_64, so "only the tiers the diff can reach" ran all of them, about 434 hosted machine-hours in the 30 hours from 2026-11-17 12:00 UTC.
- ✅ `prove` re-checks on pull requests only the HOL Light proofs whose inputs changed, and runs cosim only when the models it checks changed (maintainer, 2026-11-18, /quest-plan; rejected: run everything on every pull request). It spent about 327 hosted machine-hours in those 30 hours.
- ✅ These quests sit in m0, whose goal covers hosted CI that blocks every PR (rejected: m2).
- Re-measure with the Actions REST API: per-label wait from a job's `created_at` to `started_at`, merge-group build time, and machine-hours per workflow over the 14 days after the last child lands. That re-measure is this README's own work: the PR that deletes the last child sets this epic's Scheduled date, 14 days after it lands. The 2026-12-03 date [kixel-ai/rind#843](https://github.com/kixel-ai/rind/pull/843) set was dropped on 2026-11-19 when new children joined, since an epic's date also blocks its children.

Extended with the maintainer on 2026-11-19, after the queue grew again. On 2026-11-18 rind ran 931 hosted job-hours, its hosted jobs waited p50 1.7 min and p90 84 min from `created_at` to `started_at`, and 25% of the job-hours went to jobs that were cancelled. Each pull request head that reaches x86_64 started a median 545 hosted minutes: x86-cpu 46%, prove 32%, ctgrind 15%. Dispatched ctgrind took another 425 hosted hours in 21 runs from 2026-11-16 to 2026-11-19, 231 of them on armv7, mostly its debug unit rows running to the 6-hour cancel before [kixel-ai/rind#843](https://github.com/kixel-ai/rind/pull/843) landed. Up to 117 hosted jobs ran at once (58 `ubuntu-latest`, 53 `ubuntu-24.04`, 21 `ubuntu-24.04-arm`), so the cap of 60 above is not the whole picture.

- ✅ nixos takes no trusted rind jobs beyond the merge queue's own `rind-queue` runner (rejected: yes, with a fresh VM per job; yes, as a plain runner). Don't propose it again.
- ✅ armv7's debug ctgrind rows are sped up so they finish (rejected: drop them). [kixel-ai/rind#843](https://github.com/kixel-ai/rind/pull/843) did so the same morning: they now pass in about 1h48m.

## Related

- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - adds the Mac mini as a second queue runner, which the queue overhead quest must not slow
- [Apple-silicon nightlies run on the Mac mini](/quest/m2/confidence/apple-nightlies.md) - takes the aarch64 and macOS heavy jobs off hosted runners
