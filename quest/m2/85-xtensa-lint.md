# [S] Xtensa lint

## Goal

The Xtensa lint runs on the right triggers, keeps the user's rustc wrapper, and turns off only the false-positive lint.

## Plan

Difficulty: 3/10 (estimate).

Fork PR #85, head `271b7397`. Score 6/10. Depends on [fork PR #84](https://github.com/steelhead99x/rind/pull/84).

- Add `sh/bare-metal-rustc` to the `just check` trigger.
- Keep a configured `rustc-wrapper`.
- On the ESP-IDF row, turn off only the false-positive lint, not all of Clippy.

Next: [#87](/quest/m2/87-poly1305-26bit-limbs.md).
