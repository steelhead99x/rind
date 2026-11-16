# [XS] Close fork mirrors of the upstream drafts

## Goal

https://github.com/steelhead99x/rind/pull/111, https://github.com/steelhead99x/rind/pull/112, https://github.com/steelhead99x/rind/pull/113, https://github.com/steelhead99x/rind/pull/114, and https://github.com/steelhead99x/rind/pull/115 are closed. Each mirrors an upstream draft in https://github.com/kixel-ai/rind/pull/790 through https://github.com/kixel-ai/rind/pull/794.

## Plan

- Before closing, confirm that later fixes on the fork originals were ported to the upstream drafts, including the documentation fix at `fe5a0ee5` on https://github.com/steelhead99x/rind/pull/79. If a later fix is missing from the matching upstream draft, port it first and do not close that pair until the heads match on the fix.
- Close the five fork pull requests only after that check, and only with an explicit go. Leave the upstream drafts open.

## Waiting

- Maintainer: after the porting check, approve closing the five fork pull requests. Check: #111 through #115 are closed and the matching upstream drafts remain open.

## Related

- [Review the table-alignment and CI-cancel-alert drafts](/quest/local/04-easy-review-table-align-ci-alert.md) - reviews two of the upstream drafts those fork pull requests mirror
