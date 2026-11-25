# [M] ChaCha20-Poly1305 on x86_64 with AVX-512 earns the ✓ from pyca/verified-garbage's proof

## Goal

Every VG routine that ChaCha20-Poly1305 and XChaCha20-Poly1305 run on x86_64 with AVX-512 IFMA is imported as a theorem, so both AEADs earn the ✓ on those CPUs, where VG's code runs at every length.

## Plan

Decided 2026-11-21 (orchestrator, for the maintainer, in [kixel-ai/rind#949](https://github.com/kixel-ai/rind/pull/949)'s merge pick): ✅ keep this quest (rejected: drop it and record a reason in `benchmarks/gaps.toml`).

- Runs ([kixel-ai/rind#953](https://github.com/kixel-ai/rind/pull/953)): `low::x86_64::chacha20poly1305`'s `seal_ifma` and `open_ifma`, one wrapper each over VG's `vg_chacha20_poly1305_seal_ifma` and `vg_chacha20_poly1305_open_ifma`, at every length where `HaveIfmaForVgChaCha20Poly1305` (AVX, AVX2, AVX-512 F and VL, AVX512_IFMA: seal needs AVX, F, and IFMA, open the rest too) passes. VG's AVX-512 and AVX-512 VL variants, and OpenSSL's separate passes, measured slower and are not imported.
- Import each wrapper's VG theorem as one axiom, under [the m4 epic's composition rule](/quest/m4/verified/README.md#composition-rule), as `proofs/Rind/Aarch64/VgChaCha20Poly1305.lean` does for the SVE2 pair ([kixel-ai/rind#885](https://github.com/kixel-ai/rind/pull/885)), whose `Rind.VgChaCha20Poly1305` already proves VG's spec is `Rind.Spec`'s RFC 8439. The axioms cite VG's x86_64 `Verified.lean` at the `_ifma` variants `Artifacts/ChaCha20Poly1305/X86_64.lean` registers.
- `proofs/Rind/X86_64/ChaCha20Poly1305.lean` proves the AEAD API, the `mid` glue, and HChaCha20 down to the one-pass call, but since #953 only on CPUs whose IFMA check fails (`RunsChaCha20Poly1305`). Add the IFMA branch: on those CPUs `seal` and `open` need no `OnePass`. VG's open zeroes the message when the tag is wrong, where aws-lc's leaves the plaintext, so state the one-pass open as the aarch64 proof does (plaintext if the tag matches, else zeros) and carry that through `open_tail_spec`, which zeroes it again either way.
- Add the `benchmarks/verified.toml` entries for x86_64 with `cpu = ["avx", "avx2", "avx512f", "avx512vl", "avx512ifma"]`. [aws-lc's seal and open](/quest/m4/verified/chacha20-poly1305-x86/aead.md) still owns CPUs without IFMA.
- Model gaps follow the epic's rulings of 2026-11-17 ([kixel-ai/rind#815](https://github.com/kixel-ai/rind/pull/815#issuecomment-6943056592)).
