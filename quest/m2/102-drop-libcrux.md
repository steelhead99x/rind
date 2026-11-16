# Drop libcrux

Difficulty: 8/10 (estimate)


## Goal

libcrux is removed where it is not needed, and the SHA-2 and Poly1305 proofs state their assumptions consistently.

## Plan

Fork PR #102 (upstream twin #794; fork #115 mirrors it), head `e5f128c6`. Score 5/10, on #94. A local commit `a6bb4040` is untested.

- First decide whether 64-bit portable keeps libcrux. That decision covers the high finding and one medium.
- Add mutants exclusions for the 26-bit Poly1305's `|` to `^` mutants.
- Add a quest for a `poly1305_32` proof.
- The Axioms docstring must say the SHA-2 theorems rest on hypotheses.
- Make the two SHA-2 hypotheses state the same contract.
- Fix the stale libcrux pins and the duplicated clamp code.
