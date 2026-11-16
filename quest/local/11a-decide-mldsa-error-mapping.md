# [XS] Decide ML-DSA wipe and refusal error mapping

## Goal

https://github.com/steelhead99x/rind/pull/109 has a recorded decision on whether refusal error mapping keys only on the algorithm OID, and the wait on https://github.com/kixel-ai/rind/pull/789 is cleared or waived.

## Plan

This is a person action, not a coding session. Most of the medium findings clear if error mapping keys only on the algorithm OID, not on other fields. Do not change the branch in this step.

Success check: `gh pr view 789 --repo kixel-ai/rind --json state --jq .state` is `MERGED`, or `gh api repos/steelhead99x/rind/issues/109/comments --jq '.[].body'` says the work can proceed without it; and `gh pr view 109 --repo steelhead99x/rind --json body --jq .body; gh api repos/steelhead99x/rind/issues/109/comments --jq '.[].body'` prints a decision on OID-only mapping.

## Waiting

- kixel-ai/rind#789: this fork draft waits on that upstream pull request. Check: `gh pr view 789 --repo kixel-ai/rind --json state --jq .state` is `MERGED`, or a comment on https://github.com/steelhead99x/rind/pull/109 says the work can proceed without it.
- Maintainer: decide whether error mapping on https://github.com/steelhead99x/rind/pull/109 keys only on the algorithm OID. Check: a comment or the pull request body states the choice.

## Related

- [Fix the ML-DSA seed-tail parity test](/quest/local/12a-fix-mldsa-seed-tail.md) - other open ML-DSA work on the fork
