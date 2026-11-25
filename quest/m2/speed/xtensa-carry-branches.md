# [M] SHA-512 on Xtensa has no branch on a carry, then Ed25519, then P-256

## Goal

On the ESP32-S3 (`xtensa-esp32s3-none-elf`, Xtensa LX7), the SHA-512 block function rind runs has no conditional branch on the carry of a `u64` addition, its digests are unchanged, and its board time is no worse than its control's, each MEASURED on one board with interleaved controls. Ed25519 signing and verification and P-256 then get the same, each as its own quest cut from this one's Plan after SHA-512 measures. If the board shows SHA-512 slower with the split, this quest's PR records the measurement and deletes the quest, and the later milestones are dropped with it.

## Plan

Drafted 2026-11-21 (Claude), owner-requested after the ESP32-S3 ChaCha20-Poly1305 work. Its Poly1305 PR ([steelhead99x/rind#280](https://github.com/steelhead99x/rind/pull/280), which [steelhead99x/rind#296](https://github.com/steelhead99x/rind/pull/296) carried onto this base) found that LLVM's Xtensa backend adds two `u64`s as `add` plus a conditional `bltu` on the carry, so a secret value's carry decides a branch: a timing dependence `AGENTS.md` forbids, and a taken branch costs cycles. #280 removed it from Poly1305. The same pattern is in every other 64-bit sum in the image.

What the S3 image holds, counted by disassembly of the linked image of #278 (carry-shaped `bltu`/`bgeu` pairs, a count of instructions, not of executions, and not yet attributed to rind's code or to the RustCrypto and dalek code linked into the same harness):

- SHA-512: 522 in `compress512` (the `sha2` crate's and rind's rolled body).
- Ed25519: 103 of 121 in `PublicKey::verify`, and about 100 in each scalar multiplication (103 and 95 in dalek's), with `ed25519_sign` inlined into the harness.
- P-256: not built for the S3 in that round; its 32-bit multiply (`generic/p256_mul32.rs`) and the field and scalar arithmetic around it are the candidates, count them first.

Because the image links rind and RustCrypto and dalek, the first step of each milestone is a count of the carry-shaped branches in rind's own symbols only, from `xtensa-esp32s3-elf-objdump` of an image built from the control revision. Only rind's count is this quest's. The other libraries' stay as they are; the quest's goal is about what rind runs, not a claim against theirs.

### Method (the same for every milestone, as #280's)

1. Split every 64-bit sum that touches secret data so that no `u64` add exists on the path, or, where the sum is of 32-bit words, derive the carry without a conditional branch. #280 split Poly1305's products at bit 28 so each limb sum stayed in a `u32`. SHA-512 has no products, so its split is on the sums themselves: a 64-bit word is a pair of `u32`s, the low words add in `u32` and the carry out is `((a & b) | ((a | b) & !sum)) >> 31`, taken from the operands and the sum with `and`, `or`, `xor` and a shift, and the high words add the carry in. That is a design hypothesis, not a result: the quest measures it against the instruction count and the board time and keeps it only if both hold (the cost is ESTIMATED from the instruction count before any board run, with the derivation in the PR, and then MEASURED). The 64-bit rotates `rotate_right` of the round functions are separate: write them as `u32` pair shifts, which LLVM may already do without a carry branch, and check in the disassembly.
2. Keep the arithmetic identical. A host test compares the split body with the existing body (and, for SHA-512, with FIPS 180-4's known answers and the `sha2` crate's digests) over random inputs and edge values: all-ones words, a carry out of the low word on every addition, `0x0000_0000_ffff_ffff + 1`, chaining states and messages at 0, 111, 112, 127, 128 and 1,000,000 bytes, as `split_matches_wide` does for Poly1305 in #280.
3. ctgrind where the host can run it: the split bodies are plain Rust, so the host `admin/ctgrind` build marks the message and key as secret and covers them as it covers the existing bodies. Say in the PR which target the ctgrind ran on (x86_64, not Xtensa, which has no valgrind), and that on the host a `u64` add has no branch anyway, so that run checks the new code's own structure, not the removed branch. The removed branch is checked only by the disassembly count (no `bltu` or `bgeu` whose operands are a sum and an addend in the body) and by the board's timing.
4. Board A/B on the S3, MEASURED only: images built from one worktree path, interleaved with controls (the control image flashed between the variant images, at least five, repeating within 0.01 percent as #280's did) at 80 MHz first and at 240 MHz as a scaling check, on the fixed harness (`harness-open-fix.patch` and the workshop's `firmware-s3`, both libraries doing the same work per row, the RFC 8439 and RFC 8032 known answers in-image, every capture's KAT lines PASS before any timing is read). The figures come from the median of the rounds in each capture; the PR table says rounds, board and clock. A first image that fails a KAT on the board is reported as such, as #279's was.
5. Every number in the PR and in this file is labelled MEASURED (board or host, with the setup) or ESTIMATED (derived, with the derivation). A count from a disassembly is neither: it is called a count.

### Milestone 1: SHA-512 only (this quest)

- Code: rind's SHA-512 block function on `target_arch = "xtensa"`, in `low/generic/sha512_rolled.rs` (the rolled 80-round loop over a 16-word window, the body 32-bit microcontrollers run) and, once it lands, the unrolled body of the IRAM placement in `low/generic/sha512.rs` (see below). One shared helper holds the split add so both bodies run the same arithmetic; the dispatch is by `cfg(target_arch = "xtensa")` and the host test builds both. HMAC-SHA-384/512, HKDF, PBKDF2 and Ed25519's hashing take it with no change of their own.
- Checks: the host tests of step 2, the strict gate, ctgrind of step 3, disassembly counts before and after (rind's `compress` symbols), the board A/B of step 4 (SHA-512 rows of the harness at 16 B, 243 B and 1500 B and a many-block row, rind against the control and against `sha2`).
- Exit: digests unchanged on the host and on the board's known answers, the count of rind's carry-shaped branches in the SHA-512 block function at zero, and the board time (MEASURED) no worse than the control's at every size, else the quest records the numbers and is deleted.

### Milestone 2: Ed25519 (a follow-up quest after milestone 1 measures)

Signing, verification and the scalar multiplications: first attribute the 103 of 121 and the roughly 100 per multiplication to rind's symbols (`mid/ed25519.rs`, `low/portable/curve25519.rs`, `generic/edwards25519_msm.rs`) and to dalek's; for rind's, the field arithmetic and the scalar reduction mod the group order are where `u64` sums of secret limbs occur. Same method; the known answers are RFC 8032 and Wycheproof's Ed25519 vectors, the differential tests are against aws-lc-rs and an independent Rust implementation, as `AGENTS.md` requires, and the board rows are sign and verify (45.3 ms and 67.3 ms for rind at 80 MHz in the last run, MEASURED, so any change is judged against those). Expect the work to be larger than SHA-512's: field multiplication products have a split like Poly1305's (#280's bit-28 split), not the pair-of-words add.

### Milestone 3: P-256 (a follow-up quest after milestone 2)

ECDSA P-256 sign and verify and ECDH on the S3: count first, since the S3 image has no P-256 row yet (the next board round builds one), then the same method on `generic/p256_mul32.rs` and the field and order arithmetic. Known answers: NIST CAVP and Wycheproof; differential tests against aws-lc-rs and RustCrypto's `p256`.

### How this relates to steelhead99x/rind#94

[steelhead99x/rind#94](https://github.com/steelhead99x/rind/pull/94) places an unrolled SHA-512 body in IRAM on ESP-IDF (`xtensa-esp32s3-espidf`), with a flash opt-out feature, and keeps the rolled loop of `sha512_rolled.rs` on every other 32-bit target; another worker is changing it so that the smaller, rolled SHA-512 is the default on bare metal (`xtensa-esp32s3-none-elf`), which is the target the S3 workshop firmware runs. This quest is about the arithmetic inside whichever body runs, not about which body or where it is placed, so the two compose:

- On `none-elf` the body is the rolled one after #94: milestone 1's first target, and part of what the 522 count covers (rind's rolled body and the `sha2` crate's).
- On ESP-IDF the unrolled IRAM body is selected: it has the same carry-shaped adds and takes the same shared helper, but code in IRAM must not reach flash, so the helper is `#[inline(always)]` and the layout check (`admin/esp32s3-sha512-layout`, which checks no call in the block and the IRAM size ceiling of 20,480 bytes) must still pass: the split adds instructions, so the ceiling is a real constraint, MEASURED by that script. Milestone 1 changes #94's body only after #94 lands, so the two PRs do not edit `sha512.rs` at once; until then milestone 1 starts on the rolled body.
- The two quests' measurements are separate: #94's is IRAM against flash placement; this one's is the same body with and without the split.

### Out of scope

- Constant-time proofs on Xtensa, and proofs of the split bodies (the Lean proofs plan in [the rolled SHA-2 quest](/quest/m4/verified/rolled-sha2-esp.md), whose SHA-512 body this changes; that quest's proof then covers the split body, so update its Plan when milestone 1 lands).
- RustCrypto's and dalek's own carry branches in the same image.
- Other targets: the carry branch is Xtensa's LLVM lowering; riscv32 and Cortex-M do not have it, and the split is `cfg(target_arch = "xtensa")` only so they keep their code.
- Anything the board did not measure is not claimed in the PR.

## Waiting

- Maintainer: land [steelhead99x/rind#94](https://github.com/steelhead99x/rind/pull/94) (or say to start on the rolled body alone) before the IRAM unrolled body of milestone 1 is changed; the rolled body can start now. Check: #94 merged, or this Waiting item removed with a note.
- steelhead99x: flash the images listed in the PR, interleaved with the control, with `run-board.sh`, and send the logs, as for [steelhead99x/rind#296](https://github.com/steelhead99x/rind/pull/296)'s board runs. Check: the PR body's table holds board medians for every image.

## Related

- [The rolled SHA-2 loops on microcontrollers](/quest/m4/verified/rolled-sha2-esp.md) - the proof of the SHA-512 body this changes
