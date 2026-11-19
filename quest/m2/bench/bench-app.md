# [M] A bench command anyone can run, and the decisions to ship it

## Goal

`admin/bench-app` gives a contributor one command that times rind against aws-lc-rs and ring on their own machine, in interleaved rounds, scrubs the result, and writes a host JSON that `admin/bench-report render` imports, so a new machine reaches `BENCHMARKS.md` the same way the report's hosts do. It is a command line tool only: the web bench and leaderboard at moq-bench.dev are separate tooling in steelhead99x/moq-bench-game, not part of this quest.

## Plan

- Base: `admin/bench-app`, a script beside `admin/bench-report` that loads it as a module and reuses its host fields, machine tag, toolchain check, operation IDs, and schema. It times `rind-bench`'s existing criterion benches; it adds no crypto and no dependency.
- Rounds: a compact suite of report operations that rind, aws-lc-rs, and ring all have rows for, at least 5 rounds, each round running every library before the next round starts, pinned to one core where the OS allows. Before and after every round it records the core's governor, the temperature, and the throttle state.
- Verdict: a round that throttled is not clean, and while the aws-lc-rs control spread (each row's slowest round over its fastest) is above 1.02, the round furthest from the control medians is dropped. The run is accepted when at least 5 rounds are left; otherwise it is written as `noisy` with the reason, which `render` skips.
- Scrubbing: paths, usernames, hostnames, IP and MAC addresses, emails, wifi names, and tokens never leave the host. The scrub fails the run if a value it was told to remove survives.
- Output: `<host>.json`, which `render --from DIR` imports and `render --check` then accepts.

## Waiting

Each item opens with who acts. Options are lettered, the recommendation first.

- Maintainer: where results live. (a) Contributors open a PR to `rind-results` with the command's output, as #76 to #78 did. (b) The command fills a GitHub issue form. (c) It only prints; contributors paste. Recommended: (a), because the review, scrubbing, and host-slug checks already live there.
- Maintainer: trust. The report accepts self-reported timings. (a) Keep community rows out of README, in a separate table, until a host has a second independent run. (b) Accept them as labelled, with the control spread and throttle state beside each row. (c) Require a CI re-run before a row reaches README. Recommended: (a).
- Maintainer: which hosts reach the report. (a) Add a host only by a maintainer-approved PR; the command only proposes the slug. (b) Let the command register a slug by itself. Recommended: (a).
- Maintainer: noise policy. (a) Accept a run only when the aws-lc-rs control stays within 1.02, no throttle bit is set, and at least 5 interleaved rounds were clean. (b) Accept any run with the values shown. Recommended: (a), which the command enforces today.
- Maintainer: privacy. Confirm the scrub list above is enough, and that scrubbed results may be committed to `rind-results`.
- Maintainer: release. `admin/bench-app` is a script, never published, and runs from the repository. Confirm it stays that way.
- Maintainer: dependencies. It adds none: Python's standard library and the crates `rind-bench` already uses. Confirm `deny` needs no change.
- Maintainer: review (draft, `REVIEW_REQUIRED`).
