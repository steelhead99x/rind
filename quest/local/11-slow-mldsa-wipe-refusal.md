# [S] Decide ML-DSA wipe and refusal error mapping, then fix the draft

## Goal

https://github.com/steelhead99x/rind/pull/109 maps refusal errors by a recorded rule, and its medium findings are fixed or refuted.

## Plan

Most of the medium findings clear if error mapping keys only on the algorithm OID, not on other fields. After https://github.com/kixel-ai/rind/pull/789 lands or is otherwise resolved, apply the chosen mapping and fix the remaining findings.

## Waiting

- kixel-ai/rind#789: this fork draft waits on that upstream pull request. Check: #789 is merged, or a comment on https://github.com/steelhead99x/rind/pull/109 says the work can proceed without it.
- Maintainer: decide whether error mapping on https://github.com/steelhead99x/rind/pull/109 keys only on the algorithm OID. Check: a comment or commit on the pull request states the choice.

## Related

- [Fix the ML-DSA seed-tail parity test](/quest/local/12-slow-parity-harness.md) - other open ML-DSA work on the fork
