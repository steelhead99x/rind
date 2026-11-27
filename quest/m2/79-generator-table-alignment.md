# [M] Generator table alignment

## Goal

Generator tables have real alignment guarantees, not just type checks, and the aarch64 proof does not depend on a generated name.

## Plan

Difficulty: 5/10 (estimate).

Fork PR #79, head `cfb3e411`. Score 8/10. Upstream twin #790; fork #111 mirrors it. Lean proofs pass for both.

- The alignment asserts check the type, not the address.
- `AlignedTable` duplicates `low::abi::Aligned`.
- The aarch64 proof depends on the generated name `a_post`.
- No before/after benchmark exists.
- P-384 calls `generator_table()` inside its loop.
