# [XS] Decide the bench-report alias rules

## Goal

https://github.com/steelhead99x/rind/pull/107 has a recorded decision on how a tagged benchmark result maps to its host alias.

## Plan

This is a person action, not a coding session. A review asked that a tagged result keep its plain host slug only when the existing file has the same tag, and otherwise use `slug-tag`, and that untagged files are never merged or deleted. That undoes earlier-round fixes. Record the choice on the pull request. Do not change the branch in this step.

Success check: `gh pr view 107 --repo steelhead99x/rind --json body --jq .body; gh api repos/steelhead99x/rind/issues/107/comments --jq '.[].body'` prints a decision that names option 1 (the reviewer's rule) or option 2 (keep the earlier-round rules).

## Waiting

- Maintainer: choose the alias rules for https://github.com/steelhead99x/rind/pull/107. Options: (1) adopt the reviewer's rule (a tagged result maps to its slug only if that file has the same tag, otherwise `slug-tag`; never merge or delete untagged files); (2) keep the earlier-round rules. Check: the success check above finds that choice.
