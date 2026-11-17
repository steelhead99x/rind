# [M] Bench report host slugs stop overwriting machines

## Goal

Results from different machines never overwrite each other, and bad input cannot stop the host list from loading.

## Plan

Difficulty: 6/10 (estimate).

Fork PR #107, base `main`. The user retargeted it from `fork/bench-report`, which was only an old copy of fork main; the branch merges `sync/up-main-*` (upstream main plus fork quests) to stay current. Score 4/10, fork only.

- High: remove Pullfrog from `alert.yml`.
- High: untagged results overwrite another machine's data.
- Medium: do not let tagged hosts take over untagged aliases.
- Medium: do not delete an alias when refreshing.
- Medium: do not let one bad JSON file stop `load_hosts`.
- Fix: store collisions as `<slug>-<tag>`, never treat an untagged file as any machine's (a tagged result goes beside it, an untagged one is refused), never reuse or delete untagged files automatically, and require `--host` when there is no tag.
- Unreadable files and results without times are never destinations, and `summary`/`render` skip them on stderr.
- Of one machine's results under one slug in a collection, the newest `started` is imported.
- Expect a light conflict with upstream #619.
