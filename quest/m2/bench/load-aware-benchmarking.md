# [M] Benchmarks say what load they ran under, and what it cost

## Goal

Every benchmark row records the load it ran under, and the project knows, by measurement, how far a rind-over-competitor ratio moves with that load, how much waiting for a quiet host costs against running loaded, and what each operation costs in energy. A host that also runs CI runners and agents, as the benchmark hosts here do, then produces rows that are honest about their conditions instead of rows that are either discarded or trusted blindly.

## Plan

This is an internal quest on the owner's fork, written to be worked out with an agent in a later session. It is not a claim and not a proposal to the maintainer yet: its first output is a measurement and a recommendation, and a maintainer item appears under `## Waiting` only once the data supports one.

Why it came up (measured on 2026-11-19, on a 24-core laptop that also ran the agents doing the benchmarking):

- Interleaved A/B runs of the same code against itself, with an aws-lc-rs control, drifted 0.87 to 1.22 at load averages of 5 to 25, where the project's rule asks for a control within 1.02. A real win or loss could not be shown, and a correct rule discarded the whole run.
- `quest gate` waits for the load average to fall before a heavy command, so the machine's idle time is spent waiting. A strict gate took 17 to 28 minutes of wall time, most of it waiting, and dozens of gates and Lean builds queued behind each other at a load of 40 to 55.
- Controls on a loaded host are not noise of one kind. Candidates are a busy SMT sibling, shared L3 and memory bandwidth, a lower or uneven clock, and thermal throttling. Each affects rind and its competitors differently, so the ratio can move even when the control looks flat.

What to work out, in order:

1. **Measure how much load moves a ratio.** Pick four operations that stress different things (AES-GCM 16 KB for the vector units, Ed25519 verify for the integer multiplier, SHA-256 for the memory-light rounds, Argon2id for memory bandwidth). On a quiet pinned core, time rind and aws-lc-rs interleaved while a synthetic load runs on the other cores at fixed levels (idle, 25%, 50%, 75%, 100% of the remaining cores, then the same with the SMT sibling busy and idle). Record each ratio with its spread, and per operation and load level the absolute difference between the loaded and quiet medians beside the CI width, so a systematic bias shows (more rounds narrow the interval around a shifted ratio; they do not remove the shift). The output is a table of how the ratio and the control move with load, per host class (x86 desktop, x86 laptop, Apple silicon, Raspberry Pi, Jetson).
2. **Decide whether a loaded row is usable.** Test an adaptive rule against the fixed 1.02 control rule: accept a run when the paired rind-over-competitor ratio has a bootstrap interval narrower than a stated width (for example 2% at 95%), taking more interleaved rounds under load instead of waiting. Count how many rounds that takes at each load level, and whether it ever accepts a run the fixed rule would reject and that a quiet rerun then contradicts.
3. **Name the load levels a row can carry.** For example `quiet` (no other work, load average below a stated bound), `shared` (the host's normal mix of CI runners and agents), and `stressed` (a stated synthetic load). Record the level with the row's host data beside the existing control spread: load average before and after, the CPU clock, the temperature and throttle state where the platform exposes it, and the number of runnable tasks.
4. **Measure energy per operation, where the host allows it.** Energy is optional per host: the load and state-recording script (step 3, and the first done criterion) needs no sudo, and a host without an unprivileged energy source simply has no energy columns. What each source needs:
   - Linux x86, RAPL (`/sys/class/powercap/*/energy_uj`, `perf stat -e power/energy-pkg/`): root or `CAP_PERFMON`, since the PLATYPUS mitigation made the counters unreadable to ordinary users. Without it: leave energy out, or the owner makes a one-time choice to relax it (a udev rule setting group read on the `energy_uj` files, or `sysctl kernel.perf_event_paranoid` lowered for the perf route), or use an external meter.
   - Apple silicon, `powermetrics --samplers cpu_power`: needs root. There is no unprivileged equivalent worth relying on here. Without it: leave energy out, run `powermetrics` once under sudo that the owner chooses to allow, or use an external meter.
   - Raspberry Pi, `vcgencmd pmic_read_adc` (Pi 5): readable without root where the user can open `/dev/vcio` (the `video` group); the Pi 4 has no PMIC reading, so use an external meter or leave energy out.
   - Jetson, `tegrastats`: readable by the user on the stock image; if not, leave energy out or use an external meter.
   - Any host: an external meter at the wall gives whole-device energy and needs no privilege on the host.

   Record each host's energy support (source, privilege needed, covers package or whole device, resolution, or "none") with its row, so a missing column reads as "no sensor access" and not as zero. Where energy is read, record joules per operation beside time. Report idle power, loaded power and energy per operation for rind and the competitor at each load level. A faster routine that draws more power per operation is a different result from one that does not, and the project has not measured it.
5. **Cost the two strategies.** Compare waiting for a quiet host with running loaded and taking more rounds: wall time, hosted-runner minutes where a runner is involved, and the energy of the extra rounds against the energy of an idle host that waits. The load that was not rind's (other agents, CI runners) is the case of interest, since it is the common one on a shared benchmark host.
6. **Write the recommendation.** Which rows a loaded host may publish, with what label; whether `quest gate` should keep waiting or offer a bounded, labelled loaded mode; what to add to `admin/bench-report`'s schema; and whether energy per operation belongs in the report.

What done looks like:

- A script that applies a stated load level to the other cores and records the host's state around each round, usable on a laptop, a Raspberry Pi and an Apple-silicon Mac without sudo (energy readings are optional per host, and the script records which energy source each host had, or none), with the platform differences stated.
- The measurement table from step 1 for at least two host classes, committed as data, not only as prose.

Things to keep in mind:

- Pin to one core and keep a separate target directory per variant, as every other benchmark here does. Load tests change the load, not the method.
- Do not average away a disagreement. If loaded and quiet runs of the same pair give different winners, that result is the finding.
- A synthetic load is not the real mix. Include at least one run with the real mix (the hosts' actual CI runners and agents) so the table can say how far the synthetic levels stand in for it.
- Energy numbers need the sensor named, its resolution, and whether it covers the package or the whole device.

## Waiting

- steelhead99x: choose which hosts to measure first (the 24-core Arrow Lake laptop, a second x86 machine, an Apple-silicon Mac, a Raspberry Pi 5 and a Raspberry Pi 4 are available) and which of them can read energy without root; check with `ls /sys/class/powercap`, `powermetrics --samplers cpu_power` (needs sudo) and `vcgencmd pmic_read_adc`, and for each host that cannot, choose between leaving energy out, a one-time udev or sysctl relaxation, or an external meter.
- Maintainer: once step 6 has a recommendation, decide whether the report may carry a row measured under `shared` load, with its label, and whether it gains an energy column. Options and a recommendation go here with the data.
