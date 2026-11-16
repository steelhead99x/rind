# Bench report host slugs stop overwriting machines

Difficulty: 6/10 (estimate)


## Goal

Results from different machines never overwrite each other, and bad input cannot stop the host list from loading.

## Plan

Fork PR #107, base `fork/bench-report`, head `449e868c`. Score 4/10, fork only.

- High: remove Pullfrog from `alert.yml`.
- High: untagged results overwrite another machine's data.
- Medium: do not let tagged hosts take over untagged aliases.
- Medium: do not delete an alias when refreshing.
- Medium: do not let one bad JSON file stop `load_hosts`.
- Fix: store collisions as `<slug>-<tag>`, never reuse or delete untagged files automatically, and require `--host` when there is no tag.
- Expect a light conflict with upstream #619.

## Related

- [CI alert on cancel](106-alert-on-cancel.md) - touches the same bench-report branch
