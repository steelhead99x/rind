# [M] ESP32-S3 SHA and HChaCha

## Goal

The Xtensa assembly that ships is tested under QEMU, rolled SHA-512 and HChaCha20 are limited to ESP-IDF Xtensa, and the layout job builds rind itself.

## Plan

Difficulty: 6/10 (estimate).

Fork PR #69 (upstream twin #793; fork #114 mirrors it), head `9ee58187`. Score 5/10.

Mediums:
- Have CI run the Xtensa asm that ships, using QEMU.
- Limit rolled SHA-512 and HChaCha20 to ESP-IDF Xtensa.
- Have the layout job build rind itself.

From the #793 review:
- Add the `maj` mutants exclusion.
- Test rolled SHA-512 from non-initial states.

Lows (six, including):
- bounds checks in `hchacha20_double_round`
- a test that compares a function with itself
- the Graviola attribution in three LICENSE files

Resolve the one-line `alert.yml` conflict. Do not reuse #793's local commit `bf8384f4`, which breaks the Lean proofs.
