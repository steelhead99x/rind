# Xtensa lint

Difficulty: 3/10 (estimate)


## Goal

The Xtensa lint runs on the right triggers, keeps the user's rustc wrapper, and turns off only the false-positive lint.

## Plan

Fork PR #85, head `271b7397`. Score 6/10. Depends on [#84](84-bare-metal-no-std.md).

- Add `sh/bare-metal-rustc` to the `just check` trigger.
- Keep a configured `rustc-wrapper`.
- On the ESP-IDF row, turn off only the false-positive lint, not all of Clippy.

Next: [#87](87-poly1305-26bit-limbs.md).
