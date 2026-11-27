# [L] armv7's Rust AES-GCM is proven

## Goal

AES-GCM without the crypto extension, armv7's remaining Rust-only path, earns the ✓ on armv7.

## Plan

- `admin/prove`'s `extract_armv7` translates the AES-GCM API into `proofs/Rind/Armv7/`, down to `low/generic/aes_nohw.rs` in 32-bit words and `ghash_nohw.rs`, with `Rind/Armv7/{Types,Funs}External.lean` defining what it leaves opaque. `encrypt_block_spec` and `encrypt_batch_spec` (`Rind/Armv7/AesNohwBlock.lean`, `AesNohwCipher.lean`) prove the cipher's rounds on the round keys a `Schedule` holds, against Vale's `eval_cipher`, and `new_schedule_spec` and `schedule_encrypt_block` (`Rind/Armv7/AesNohwKey.lean`) that `NohwKey::new` and `NohwKey::schedule` hold Vale's `key_to_round_keys_LE` of the key, under which `encrypt_block` is `aes_encrypt_LE`.
- Left, in order, each stated against `Rind/Vale.lean`'s spec as x86_64's and aarch64's AES-GCM theorems are:
  - `Schedule::keystream` and `ctr32` as counter mode;
  - `ghash_nohw.rs`'s `gcm_mul32_nohw`, Karatsuba multiply, and reduction, against `Rind/Gf128.lean`;
  - `mid/portable/aes_gcm.rs`'s `initial_counter`, `pass`, and `tagged`, and `AesGcm`'s API with the crypto-extension and NEON checks finding neither, over armv7's HOL Light constant-time compares restated as x86_64's `CtEqual.lean` restates its own;
  - then the ✓ in `benchmarks/verified.toml` and its pin in `Rind/Armv7/Axioms.lean`.
- The round steps are proven at each bit position by `bv_decide` on the 32-bit words. [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md) proves the same file in SSE2 words: it reuses `Rind/AesSbox.lean`'s decision tree and the byte-level statements (`Batch.byte`, `Batch.block`), with its own word lemmas.
- ML-KEM's portable arithmetic is [its own quest](/quest/m4/verified/mlkem-portable.md); its Keccak-f is assembly, in [armv7's assembly](/quest/m5/verified-armv7/assembly.md).
- Poly1305 without NEON is libcrux's HACL\*-compiled Rust, which `benchmarks/verified.toml` counts, under rind's glue.
- The runs on the index-loop rewrite of `aes_nohw.rs` and `mid/portable/aes_gcm.rs` found nothing to fix (read 2026-11-25): [ctgrind `armv7:no-neon`](https://github.com/kixel-ai/rind/actions/runs/45463507839) passed, and the armv7 [`aes_gcm` bench](https://github.com/kixel-ai/rind/actions/runs/45463503971) timed rind within 1% of main's weekly run. Both armv7 bench rows have NEON, so no row times `aes_nohw.rs`'s 32-bit configuration.
- Decided 2026-11-12 (maintainer, /quest-unblock): ✅ land the armv7 translation and its ChaCha20 header-protection proof first, leaving AES-GCM here (rejected: keep that PR open until AES-GCM is proven; land it and fold armv7's AES-GCM into the x86_64 no-AES-NI quest).
- [Decided 2026-11-24](https://github.com/kixel-ai/rind/pull/1001#issuecomment-7141398690) (maintainer, /quest-run): ✅ `bv_decide`'s axioms are in the trust base (rejected: kernel-checked proofs of each step); ✅ Vale's `sbox` and `mixColumns` are irreducible definitions (rejected: keep them opaque); ✅ the translation and the rounds landed before the ✓ (rejected: hold until the ✓); ✅ that landing did not wait for the bench and ctgrind runs above (rejected: wait for both).
