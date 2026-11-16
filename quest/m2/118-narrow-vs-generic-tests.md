# Narrow vs generic tests

Difficulty: 4/10 (estimate)


## Goal

The narrow and generic multiplier paths are tested against each other after the narrow fixes land.

## Plan

Fork PR #118, head `e0029889`, score 9/10. Depends on [#82](82-narrow-multiplier-schedules.md): merge #82 once it is fixed, then rerun the tests.
