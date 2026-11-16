# [M] x86-cpu finishes inside the job limit on any hosted runner

## Goal

A full `x86-cpu` run, every SDE model, finishes well inside GitHub's 6-hour job limit on whichever hosted x86_64 runner it lands on, and SDE runs on AMD and Intel runners alike.

## Plan

- Runs on main took from 35 minutes to about 5 hours on 2026-11-14 and 2026-11-15, by runner; the split looks like AMD against Intel hosts under SDE, which nobody has measured. kixel-ai/rind#789 found Intel SDE crashing the Go acvptool on GitHub's AMD runners.
- Measure first: per-step times by host CPU (`/proc/cpuinfo` in the job log) over the last two weeks of runs. Then fix what the data shows, such as splitting models across jobs, pinning to a runner type, or skipping what crashes under SDE on AMD with a reason. No new hardware, per [the epic](/quest/m0/ci-speed/README.md).
- [The hosted-runner trim](/quest/m0/ci-speed/hosted-trim.md) narrows the models a PR runs; this quest is the full weekly run.
