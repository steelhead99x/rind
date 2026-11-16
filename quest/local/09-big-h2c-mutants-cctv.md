# [M] Resolve and review the hash-to-curve, adapter-mutant, and Ed25519 CCTV drafts

## Goal

https://github.com/kixel-ai/rind/pull/791, https://github.com/kixel-ai/rind/pull/792, and https://github.com/kixel-ai/rind/pull/797 each merge cleanly into upstream main and have one review round recorded, with findings fixed or refuted.

## Plan

All three drafts conflict with upstream main, mostly from the signature API change in https://github.com/kixel-ai/rind/pull/781. Resolving that means pushing a merge commit to each upstream pull request branch, so it waits on an explicit go.

- Merge upstream main into each branch and resolve the conflict against the new API.
- Run a review round on each new head against the current upstream main.
- Fix or refute each finding. Do not mark the drafts ready in this quest.

## Waiting

- Maintainer: approve pushing a merge of upstream main into the branches of https://github.com/kixel-ai/rind/pull/791, https://github.com/kixel-ai/rind/pull/792, and https://github.com/kixel-ai/rind/pull/797. Check: each pull request merges cleanly.

## Related

- [Resolve and review the drop-libcrux draft](/quest/local/07-big-drop-libcrux.md) - another upstream draft that conflicts with main
- [Resolve and review the ESP32-S3 SHA draft](/quest/local/08-big-esp32-s3-sha.md) - another upstream draft that conflicts with main
