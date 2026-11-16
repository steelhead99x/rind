# [L] Poly1305 in 26-bit limbs

## Goal

Poly1305 selects the right code for every target, including custom target JSON files and riscv64 without M or Zmmul.

## Plan

Difficulty: 7/10 (estimate).

Fork PR #87, head `67f48a31`, on #85. CI passes. This feeds #794.

- Read `TARGET` so custom target JSON files are detected.
- Use the 16-bit multiply on riscv64 without M or Zmmul.
- The ARMv5TE proof has stale register facts.
- Add ctgrind for the `mul16.rs` halves.
- Make sure `+mul16` targets still get the division and float scan.
- Confirm the mask select in `finish` is still hidden from the compiler.
