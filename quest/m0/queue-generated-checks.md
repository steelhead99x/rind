# [M] The merge queue runs regenerate and the vg checks when a group touches them

## Goal

A merge group whose diff touches the paths that trigger the `regenerate` workflow or `prove`'s `vg` jobs on a pull request runs those checks before it merges, and a failure fails the group. So two PRs that each pass alone, but break vendored code together, never reach `main`.

## Plan

- Caused by [kixel-ai/rind#855](https://github.com/kixel-ai/rind/pull/855), which moved `admin/import-vg`'s `REV` after [kixel-ai/rind#845](https://github.com/kixel-ai/rind/pull/845) had imported routines at the old pin. Each PR's `regenerate` and `vg` runs passed against a base without the other. The queue runs neither, so `main` failed both until [kixel-ai/rind#877](https://github.com/kixel-ai/rind/pull/877) re-imported, and every PR touching `admin/**` failed meanwhile.
- Decided 2026-11-18 (maintainer, /quest-plan): ✅ `regenerate` and both `vg` jobs (x86_64 and arm), only when the group's diff touches the paths their pull-request triggers list (rejected: on every group, which spends runner minutes on groups that cannot break them; `regenerate` alone, which misses a routine whose bytes drift while its text matches; all of `prove`, 75 minutes or more against a queue build of about 7).
- They run in parallel with the queue build, so a group waits no longer than now.
- `main`'s ruleset requires only `Queue build / Build`, and `repo-settings` in dotfiles owns the ruleset, so make that context depend on the new jobs, through `needs:` or an equivalent, rather than adding required contexts. A skipped job, for a group that doesn't touch the paths, must still let the build pass.
- `merge_group` events take no `paths` filter: diff the group's base and head SHAs to decide.
- Share the job definitions with `regenerate.yml` and `prove.yml`, for example through a reusable workflow, so the queue's checks and the PR's checks cannot drift apart.
- Check it with a queued PR that touches `admin/import-vg` and one that doesn't.
