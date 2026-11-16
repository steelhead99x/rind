# [XS] Post the HPKE edge-vector pull request description

## Goal

https://github.com/kixel-ai/rind/pull/798 uses the title and body below in place of the claim placeholder, after the text is approved.

## Plan

This is a person action, not a coding session. Post the text only after an explicit go. Do not edit the branch for the description alone.

Title: HPKE runs the IETF revision's edge-case vectors

Body:

Adds the five edge-case vectors from hpkewg/hpke `e298f94`: P-256 key rejection, empty and zero-byte AEAD inputs, empty info, info containing zeros, and PSK with no base nonce. New tests: `rfc9180_edge_cases` and `derive_rejects_a_candidate_at_or_above_the_order`. Notes on the hand-copied appendix go in `thirdparty/vectors/README.md` and `admin/sync-vectors`, and the quest file is removed.

Success check: `gh pr view 798 --repo kixel-ai/rind --json title,body --jq '.title + "\n" + .body'` prints the title `HPKE runs the IETF revision's edge-case vectors` and a body that contains `rfc9180_edge_cases` and `derive_rejects_a_candidate_at_or_above_the_order`.

## Waiting

- Maintainer: approve posting the title and body above on https://github.com/kixel-ai/rind/pull/798. Check: the success check above matches that text.

## Related

- [HPKE runs the IETF revision's edge-case vectors](/quest/m2/confidence/hpke-edge-vectors.md) - the quest this draft finishes
