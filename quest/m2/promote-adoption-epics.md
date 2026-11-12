# [XS] Promote the aws-lc-rs epic out of adoption

## Goal

`quest/m2/adoption/aws-lc-rs/` is its own epic at `quest/m2/aws-lc-rs/`, so
no epic in this tree holds another. Adoption's README names it as a blocker
instead of a child.

## Plan

Decided 2026-11-09 (user, /quest-plan in
[moq-dev/quest#594](https://github.com/moq-dev/quest/pull/594)): epics no
longer nest, since a nested epic means its parent is too large, and every
epic gets a branch its quests land on. ✅ Promote each nested epic to a
sibling in its milestone (rejected: merge its quests into the parent). The same PR promoted `quest/m5/verified-armv7/`.
The targets epic, the other one nested here, finished in place.

`quest mv` refuses to move a quest with an open PR, since the PR's branch is
named after the quest's path, so this waits for them. Start no new quest
under the old path first. Then run
`quest mv quest/m2/adoption/aws-lc-rs quest/m2/aws-lc-rs`.

## Waiting

- moq-dev/rind: the open PRs under the epic land or close. Check with
  `gh pr list -R moq-dev/rind --search "head:quest/m2/adoption/aws-lc-rs"`
  listing none.
