# [S] Decide the bench-report alias rules

## Goal

https://github.com/steelhead99x/rind/pull/107 has a recorded decision on how a tagged benchmark result maps to its host alias, and the branch follows that decision.

## Plan

A review asked that a tagged result keep its plain host slug only when the existing file has the same tag, and otherwise use `slug-tag`, and that untagged files are never merged or deleted. That undoes earlier-round fixes. Record the decision on the pull request, then apply it.

## Waiting

- Maintainer: choose the alias rules for https://github.com/steelhead99x/rind/pull/107. Options: (1) adopt the reviewer's rule (a tagged result maps to its slug only if that file has the same tag, otherwise `slug-tag`; never merge or delete untagged files); (2) keep the earlier-round rules. Check: a comment or commit on the pull request states the choice, and the branch matches it.
