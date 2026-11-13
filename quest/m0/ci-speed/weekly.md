# [M] The heavy suites run weekly and finish

## Goal

rind's heavy scheduled suites run once a week on GitHub-hosted runners instead of nightly, each finishes inside its timeout, and every one still runs on demand with `gh workflow run`. The weekly run checks everything: every crate, CPU tier, and target the suites cover.

## Plan

Decided with the maintainer on 2026-11-12 ([the epic](/quest/m0/ci-speed/README.md) holds the shared decisions):

- ✅ Weekly: `bench`, `x86-cpu` (every SDE model), `miri`, `fuzz`, `ctgrind`'s full matrix, and `timing` (already weekly). `build` stays nightly as the broadest cheap check of each day's merges (rejected: everything weekly, which could leave a cross-target break on main for a week; only bench and miri weekly, which leaves about 8 h a night on the hosted cap). The other nightly workflows (`asan`, `coverage`, `lints`, `prove`, `python`, `dart-libraries`, `regenerate`) stay as they are unless a measurement shows one is heavy.
- Nightly cost before: about 25 machine-hours on average, 45 to 90 since Nov 10; bench about 9.8 h, ctgrind 3.2 h, build 3.0 h, fuzz 2.8 h, miri 1.7 h.
- `miri` jobs hit the 6 h timeout on every run. Shard them so each finishes, and treat a timeout as the failure it is.
- Stagger the weekly schedules so they don't all start at once and fill the 60-job cap for PRs.
- `alert.yml` keeps watching every scheduled workflow; check its expectations follow the new schedules.
- Fix every doc that says these run nightly, such as TESTING.md and the workflows' header comments.

## Related

- [Releases publish only after the full suite passes locally](/quest/m0/ci-speed/release-check.md) - runs the same suites on the released crates before a release PR merges
- [Mutation testing runs weekly on native runners](/quest/m0/ci-speed/mutants-slim.md) - moves mutants to the same weekly cadence
