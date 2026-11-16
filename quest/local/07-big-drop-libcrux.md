# [M] Resolve and review the drop-libcrux draft

## Goal

https://github.com/kixel-ai/rind/pull/794 merges cleanly into upstream main and has one review round recorded, with findings fixed or refuted.

## Plan

The draft conflicts with upstream main. Resolving that means pushing a merge commit to the upstream pull request branch, so it waits on an explicit go.

- Merge upstream main into the branch and resolve the conflict, keeping the drop of libcrux.
- Run a review round against the new head and the current upstream main.
- Fix or refute each finding. Do not mark the draft ready in this quest.

## Waiting

- Maintainer: approve pushing a merge of upstream main into the branch of https://github.com/kixel-ai/rind/pull/794. Check: the pull request merges cleanly.

## Related

- [Resolve and review the ESP32-S3 SHA draft](/quest/local/08-big-esp32-s3-sha.md) - another upstream draft that conflicts with main
- [Resolve and review the hash-to-curve, adapter-mutant, and Ed25519 CCTV drafts](/quest/local/09-big-h2c-mutants-cctv.md) - further upstream drafts that conflict with main
