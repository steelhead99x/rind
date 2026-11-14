# [M] The merge queue runs rind's tests natively on aarch64

## Goal

Every merge group builds and runs rind's tests natively on aarch64, on the maintainer's Mac mini as a second self-hosted runner beside the x86_64 one, and the group fails if they fail. It covers macOS on Apple silicon and aarch64 Linux in a VM on the same machine. armv7 stays out (Apple silicon has no AArch32); the `check:cross` work in [kixel-ai/rind#594](https://github.com/kixel-ai/rind/pull/594)'s quest covers its compilation.

## Plan

Planned with the maintainer on 2026-11-10, after [kixel-ai/rind#583](https://github.com/kixel-ai/rind/pull/583) and [kixel-ai/rind#564](https://github.com/kixel-ai/rind/pull/564) passed the x86_64-only queue but together broke aarch64 tests: ✅ the maintainer bought a Mac mini for rind; ✅ its roles are this queue runner, a benchmark host ([its quest](/quest/m2/bench/mac-mini.md)), Apple-silicon nightlies ([its quest](/quest/m2/confidence/apple-nightlies.md)), and an agent workstation; ✅ this quest in m0, the others in m2 (rejected: all m2; all m0).

- Set the machine up reproducibly (nix-darwin or the flake's own shells), register a self-hosted runner for kixel-ai/rind with a label of its own in a runner group that, like `rind-queue`, admits only `queue-build.yml` at `refs/heads/main` (its header explains why), and run `queue-build.yml`'s merge-group build on both runners, each job's context required by main's ruleset (today `Queue build / Build`), so a group needs both with no fan-in job waiting on a hosted runner.
- aarch64 Linux: a lightweight VM (for example Lima or the nix-darwin Linux builder) running the same `just ci` the x86_64 host runs. Pick whichever keeps the queue's added time smallest, and record it.
- The agent workstation role is configured in the maintainer's machine configuration, not in this repo. Keep the runner's work under `quest gate` so agents and the queue share the machine as they share this host.
- If the merge-group build on the Mac mini adds more than a few minutes to landing, say so in the PR and propose trimming it to what catches aarch64-only breakage.

## Waiting

- Maintainer: the Mac mini arrives, is on the network, and agents can reach it over SSH with an account that can install Nix and register a runner. Physical setup and network access can't be done by an agent. Check by SSHing to it.
