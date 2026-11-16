# [S] Alert on cancel stops reporting old alerts as new

## Goal

The cancel alert is correct and does not duplicate alerts that upstream already ships.

## Plan

Difficulty: 3/10 (estimate).

Fork PR #106, base `fork/bench-report`, head `36441665`. Score 6/10. Upstream twin #796.

- Fix the four `sh/alert.sh` mediums from the earlier review.
- Do not present scheduled-cancel alerts as new; upstream #743 already has them.
- Merge after upstream #808.

## Related

- [Bench report host slugs](/quest/m0/107-bench-report-host-slugs.md) - same base branch
