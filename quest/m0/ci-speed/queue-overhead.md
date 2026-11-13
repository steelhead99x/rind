# [M] The merge queue spends its time building

## Goal

A merge group's time goes to `just ci` and nothing else: the build never waits in `quest gate` behind agent work, the required `Queue` context never waits for a hosted runner, and the self-hosted runner's hooks and the build's independent modules don't serialize time they need not.

## Plan

Measured 2026-11-12 over 381 merge groups: build median 2.5 min, p90 11.7, max 29.5; groups build one at a time, so every wait below delays the whole queue.

- `queue-build.yml` runs `nix develop --command quest gate just ci "$BASE"` without `QUEST_GATE_PRIORITY=1`, which `quest gate --help` says a check that lands PRs should set. Two of six sampled logs sat 160 s and 320 s with no output before `just ci` started. Set it.
- The required `Queue` job in `queue.yml` runs on `ubuntu-latest`; 23 of 381 waited over 5 min for a runner (p99 41 min, max 90), 8.6 h of stalled queue in total. Report the required context without a hosted runner, keeping `queue-build.yml`'s runner-group isolation (its header explains it). If that needs a ruleset change, an agent with admin scope can make it through `gh api`; otherwise list it under `Waiting`.
- The runner's pre- and post-job cache-gc hooks took up to 60 s and 76 s. Move the cleanup out of the job's path, such as a timer on the host, or make it cheap.
- Keep the change compatible with the Mac mini joining as a second queue runner.

## Related

- [The merge queue runs rind's tests natively on aarch64](/quest/m0/mac-mini-runner.md) - the second runner this must not slow
- [just ci runs only what a change can break, concurrently](/quest/m0/ci-speed/ci-scope.md) - shortens the build itself; this quest removes the time around it
