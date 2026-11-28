# [S] The site's browser check never hangs

## Goal

`sh/site.sh`'s headless Chrome check (`site/scripts/browser.ts`) never stalls a run. Its stall is reproduced and fixed at the root cause, and every wait it makes is bounded, so a stall fails within a minute naming what it waited on.

## Plan

Planned with the maintainer on 2026-11-27 (`/quest-run`).

- Seen once: on [kixel-ai/rind#1118](https://github.com/kixel-ai/rind/pull/1118), `Check` hung for 44 minutes in this check until it was cancelled ([job 140301952855](https://github.com/kixel-ai/rind/actions/runs/45936862605/job/140301952855)). The rerun passed.
- Reproduce it before fixing, for example by looping the check under load on a hosted runner. Find which wait never returned, such as the browser launch, a navigation, or a selector, and fix why. Don't add a retry.
