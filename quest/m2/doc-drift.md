# [XS] Platform and CI docs match main

## Goal

`PLATFORMS.md`, `UPSTREAM.md`, and `CONTRIBUTING.md` describe what rind and
its CI do on `main`: 32-bit x86 builds at the 1.90 MSRV, and pull requests get
no mutation run.

## Plan

Decided 2026-11-12 (user, /quest-plan), from rind's trimmed Pullfrog
learnings:

- `PLATFORMS.md:97-99` says 32-bit `x86` needs Rust 1.94 because
  libcrux-platform calls `__cpuid` outside `unsafe`.
  [moq-dev/rind#623](https://github.com/moq-dev/rind/pull/623) removed that
  exception, and `check:msrv` checks i686 at 1.90 (`sh/dispatch.sh:253`), but
  [moq-dev/rind#614](https://github.com/moq-dev/rind/pull/614) brought the
  sentence back. Delete it again, and delete `UPSTREAM.md`'s "libcrux-platform
  calls `__cpuid` outside `unsafe`" entry (`UPSTREAM.md:177-182`): its
  workaround is gone, since `README.md` states no exception and CI checks i686
  at the MSRV, and its "Goes when" links the deleted x86 quest.
- `CONTRIBUTING.md:49` lists "a mutation run over the PR's diff" among the
  pull-request subsets, but `mutants.yml` has run only nightly and on dispatch
  since [moq-dev/rind#668](https://github.com/moq-dev/rind/pull/668). Drop it,
  and re-read the rest of that sentence against each workflow's triggers when
  the work starts: open PR
  [moq-dev/rind#693](https://github.com/moq-dev/rind/pull/693) moves Miri off
  pull requests too.

Caused by: [moq-dev/rind#614](https://github.com/moq-dev/rind/pull/614)
(PLATFORMS.md) and [moq-dev/rind#668](https://github.com/moq-dev/rind/pull/668)
(CONTRIBUTING.md).
