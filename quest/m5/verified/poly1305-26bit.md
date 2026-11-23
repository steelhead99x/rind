# [L] The 26-bit limb Poly1305 is proven equal to RFC 8439 in Lean

## Goal

`low::generic::poly1305_32::Poly1305`, rind's Poly1305 in five 26-bit limbs held in `u32`s that the portable backend runs on riscv32 with the M extension (steelhead99x/rind#275) and on Xtensa (steelhead99x/rind#278), is proven in Lean, through Aeneas's translation of the Rust, to compute the tag of `Rind/Spec.lean`'s `poly1305.mac` (RFC 8439 section 2.5.1) for every key and every split of the message into `add_bytes` calls. That includes `reduce_split`, the Xtensa reduction whose limb sums are `u32` pairs with no `u64` carry (steelhead99x/rind#280), and `finish`'s 16-bit-halves tag addition. Constant time is a separate property and is not claimed here.

## Plan

Drafted 2026-11-21 (Claude), owner-requested. The 26-bit path runs ahead of HACL*'s proven Poly1305 under `AGENTS.md`'s fastest-source rule, with its proof planned ([the C6 quest](/quest/m2/speed/esp32c6-chacha20poly1305.md)); until this quest lands it is covered by differential tests (RFC 8439, aws-lc, HACL*, the 64-bit Poly1305, 20,000 random and edge states for `reduce_split` against `reduce_wide`) and ctgrind only.

What `proofs/` already has to build on:

- `Rind/Spec.lean`'s `poly1305.mac`, `poly1305.p`, `poly1305.clamp` and `poly1305.leNum`: RFC 8439's accumulator over the padded blocks, `(a + n + 2^(8 len)) * r mod p`, then `(a + s) mod 2^128` as little-endian bytes. This is the theorem's right-hand side, already used by `Rind/X86_64/ChaCha20Poly1305.lean`'s `OnePass` and `Rind/ChaCha20Poly1305Test.lean`, which checks the spec against RFC 8439's vectors.
- `Rind/Bytes.lean` (how Rust's little-endian byte conversions relate to `Rind.Spec`'s numbers, for the `read32` and `to_le_bytes` steps) and `Rind/Core.lean` (models of the standard-library items Aeneas's library lacks, where a model of `black_box` would go).
- The Aeneas pipeline and its conventions in `admin/prove` (one `charon` extraction per file set with `--start-from` and `--include`, as the `generic::chacha20` and portable SHA-2 passes do) and `proofs/README.md`'s composition rule. No theorem about `low::generic::poly1305` (the 64-bit Poly1305) or `poly1305_32` exists, so this is the first Poly1305 limb proof; [the portable ChaCha20-Poly1305 quest](/quest/m5/verified/chacha20-poly1305-portable.md) plans the 64-bit one and shares the arithmetic lemma in milestone 2.
- Precedent for a hand model of what Aeneas cannot translate: [the rolled SHA-2 quest](/quest/m4/verified/rolled-sha2-esp.md) models `asm!` blocks by hand and says in the proofs README what the check trusts. VG's `Spec/Poly1305.lean` (vendored under `proofs/verified-garbage/`) is a second spec to cross-check `poly1305.mac` against, not a dependency.

Milestones, each a commit or a PR on this quest's branch, in order:

1. Extraction. Make `admin/prove` translate `poly1305_32.rs` for a 32-bit portable configuration, and decide at the start, as the rolled SHA-2 quest does, how Charon reaches `reduce_split` on a host: it is `cfg(any(target_arch = "xtensa", test))` and `reduce` picks it only on Xtensa. Candidate: a proof cfg that compiles both bodies and a dispatch the proof states as a disjunction, so each target's choice is covered. Settle what Aeneas cannot take: `bytes.align_to::<u32>()` in `blocks` (unsafe), `core::hint::black_box` in `finish`, `Blockwise` and `zeroise_value`. Recommendation: prove `Blocks::block` and `finish` as they are, restate the word-aligned path as equal to the byte path in one small lemma proved on the model (its Rust fallback is the byte path the host tests already run), and say in the proofs README that the `align_to` split is trusted to partition the input in order. Check: the extracted `.lean` builds and `admin/prove` fails if the Rust and the extraction diverge.
2. The limb arithmetic. State the abstraction `val h = sum h_i * 2^(26 i)` and prove `reduce_wide`: under the bounds `Blocks::block`'s comment states (each limb of `h` under 2^27 after the message add, `r` the clamped limbs, `s_i = 5 r_i`), `val (reduce h r s) = val h * val r mod p` up to the limb bounds the next block needs (every limb under 2^26 but the second, under 2^26 + 2^6), by the identity `2^130 = 5 mod p` for the folded products. All `u64` sums are shown to stay in range, so Aeneas's overflow obligations discharge. The same lemma serves the 64-bit Poly1305 of the sibling quest.
3. The carry-free split. Prove `reduce_split h r s = reduce_wide h r s` on the bounds of `Blocks::block`: for each product `x = h * r` (h under 2^28, r and `s` under 5 * 2^26), `mulhi (h << 4) r = x >> 28` and `mul (h << 4) r = 16 * (x mod 2^28)`, so a limb's sum is `a + 2^28 b` with `a` and `b` each below 2^32, and the carry `(a >> 26) + (c_in >> 26) + 4 b` equals `reduce_wide`'s `u64` carry with no `u32` overflow (the doc comment's 3.4e9 bound is a lemma, not a comment). This is the one proof of the new idea; the others are textbook.
4. Whole message and tag. Prove `blocks` and `add_bytes` fold the 16-byte blocks of any split into `poly1305.mac`'s accumulator (the `Blockwise` buffer, the full-block and tail paths, `hibit`), then `finish`: the last short block with its `0x01` after the message and no hibit, the full carry (the comment's bounds: h1 carries 0 or 1), the choice between `h` and `h - p` as `(h + 5) >> 130`, and the 16-bit-halves `+ s` equal to `(h + s) mod 2^128`. Conclude `Poly1305::new` then `add_bytes`* then `finish` equals `poly1305.mac key (concat msgs)`, with the clamp as `Spec`'s `clamp`.
5. Integration. Add the theorem to `proofs/README.md`, restate it as the `RunsPoly1305_32` hypothesis the portable AEAD proof takes, and update [the portable ChaCha20-Poly1305 quest](/quest/m5/verified/chacha20-poly1305-portable.md), which this feeds, plus the doc comments in `poly1305_32.rs` and `portable/poly1305.rs` that say the path is not proven.

Out of scope:

- Constant time. No branch, memory index or variable-time instruction on a secret is a different property: ctgrind (`admin/ctgrind`, the host build) checks the Rust, and Lean over Aeneas's translation, which is functional, cannot state it here. The multiply-contract question (whether `mull` and `muluh`, `umull` or `mulhu` take operand-independent time on a given core) is a hardware fact and stays [the C6 quest's](/quest/m2/speed/esp32c6-chacha20poly1305.md) open decision.
- The Xtensa instruction semantics: `mull` and `muluh` appear in the Rust only as `u32` wrapping multiply and `mulhi`, so the proof is about that Rust. That the compiler lowers them to those instructions, and the S3 image's carry-branch counts, stay with the board checks and the disassembly in the S3 PRs.
- The HACL* and 64-bit Poly1305 paths, the ChaCha20 half of the AEAD, and `mid::chacha20poly1305`'s glue (the sibling quest's).
- Any speed change: this quest changes no code on the path except what extraction needs (a cfg, a split of `blocks`), with the S3 and C6 numbers unchanged, which the PR states with a differential run.

Sizing: L because milestone 3 is new mathematics over `u32` carries and milestone 1 has open Aeneas questions; milestones 2 and 4 are the shape of proofs `proofs/` already has for SHA-2 and ChaCha20.

## Related

- [ChaCha20-Poly1305 on 32-bit portable targets](/quest/m2/speed/esp32c6-chacha20poly1305.md) - where the 26-bit Poly1305 was accepted unproven, and the multiply-contract decision
- [ChaCha20-Poly1305 on the ESP32-S3](/quest/m2/speed/esp32s3-aead.md) - the carry-free split this proves
- [The portable ChaCha20-Poly1305 proof](/quest/m5/verified/chacha20-poly1305-portable.md) - the AEAD proof this feeds and the 64-bit Poly1305's
- [The rolled SHA-2 loops on microcontrollers](/quest/m4/verified/rolled-sha2-esp.md) - the extraction and hand-model precedent
