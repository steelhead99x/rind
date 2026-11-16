# [M] Resolve and review the ESP32-S3 SHA draft

## Goal

https://github.com/kixel-ai/rind/pull/793 merges cleanly into upstream main and has one review round recorded, with findings fixed or refuted. The pull request notes that the board speedup has not been measured.

## Plan

The draft conflicts with upstream main. Resolving that means pushing a merge commit to the upstream pull request branch, so it waits on an explicit go.

- Merge upstream main into the branch and resolve the conflict.
- Run a review round against the new head and the current upstream main.
- Record in the pull request that SHA performance on the ESP32-S3 board has not been measured, and do not claim a speedup without numbers.
- Fix or refute each finding. Do not mark the draft ready in this quest.

## Waiting

- Maintainer: approve pushing a merge of upstream main into the branch of https://github.com/kixel-ai/rind/pull/793. Check: the pull request merges cleanly.

## Related

- [Resolve and review the drop-libcrux draft](/quest/local/07-big-drop-libcrux.md) - another upstream draft that conflicts with main
- [Settle the remaining findings on the wide-multiplier and SHA-512 IRAM drafts](/quest/local/13-slow-wide-multiplier-sha512-iram.md) - related SHA-512 IRAM work on the fork
