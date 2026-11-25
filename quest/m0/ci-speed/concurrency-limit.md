# [XS] GitHub raises kixel-ai's hosted-job concurrency limit

## Goal

GitHub Support has answered a request to raise the kixel-ai organization's concurrent hosted-job limit, and its answer is recorded in [the epic](/quest/m0/ci-speed/README.md)'s Plan.

## Plan

- ✅ Ask GitHub Support for a higher limit (maintainer, 2026-11-19). Decided, not yet filed: see Waiting.
- [GitHub's limits page](https://docs.github.com/en/actions/reference/limits) gives the Team plan, kixel-ai's, 60 concurrent standard-runner jobs and says Support can raise it. Yet up to 117 hosted jobs ran at once on 2026-11-18. Each label's own peak, reached at different moments, was 58 `ubuntu-latest`, 53 `ubuntu-24.04` and 21 `ubuntu-24.04-arm`, so ask Support which limit binds as well as to raise it.
- An agent drafts the request in this quest's PR, citing that day's p90 queue wait of 84 minutes and that rind is public, so its minutes are free and only concurrency binds.

## Waiting

- Maintainer: file the drafted request with GitHub Support as an owner of kixel-ai, since Support takes it only from an organization owner's account and an agent holds none. An agent can drive the maintainer's signed-in Chrome with `agent-browser` if asked. Done when Support replies; record the answer and delete this quest.
