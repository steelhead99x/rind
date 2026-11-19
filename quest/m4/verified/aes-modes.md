# [L] AES-CTR and AES-CBC are proven on x86_64 with AES-NI

## Goal

`cipher::AesCtr` and AES-CBC earn the ✓ on x86_64 with AES-NI, as they have on aarch64 with the crypto extension, where key wrap has it on both.

## Plan

- What is left is HOL Light: `Rind/X86_64/AesModesApi.lean` already proves the APIs over `Rind/X86_64/AesModesLow.lean`'s axioms `hw_ctr32_spec`, `hw_cbc_encrypt_spec`, and `hw_cbc_decrypt_spec`, which restate theorems of aws-lc's `aes_hw_ctr32_encrypt_blocks` and `aes_hw_cbc_encrypt`, as rind's build emits them, in the x86_64 model of rind's s2n-bignum fork, `thirdparty/s2n-bignum`, against `hol-light/x86_64/aes_hw_spec.ml`.
- `hol-light/x86_64/aes_hw_cbc_encrypt.ml` proves encryption (`AES_HW_CBC_ENCRYPT_ENCRYPT_SUBROUTINE_CORRECT`) and, for decryption, the 8-block loop, the tails of one to seven blocks, and the loop's exit. Left: the one-block path at 0xc0, the frame setup at 0x120 into the tails and the loop, the epilogue at 0x870, and the decryption subroutine theorem.
- `aes_hw_ctr32_encrypt_blocks` has its listing and spec on the `aes-modes/ctr-hol` branch, and no proof yet: its prologue, the 8-block iteration, its tail, and the epilogue, then the subroutine theorem.
- The three axioms landed unproven, unlisted in `Axioms.lean`, with no ✓ claimed and `proofs/README.md` naming them pending (decided with the maintainer on 2026-11-13 on [kixel-ai/rind#707](https://github.com/kixel-ai/rind/pull/707): ✅ land them with the glue (rejected: drop the x86_64 CTR/CBC Lean files until the HOL Light proofs land)).
- `admin/prove`'s `hol_light_proofs` already runs `aes_hw_cbc_encrypt.o`, so the remaining CBC decryption steps above go into that file, which needs no new entry; add CTR's `.o` once its proof exists. Once both are proven, check that each axiom restates its theorem, add the x86_64 theorems to `Rind/X86_64/Axioms.lean`, and say so in `proofs/README.md`.
- Running HOL Light: cap its memory (`systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0` under `quest gate`); a Gröbner-basis step in CTR's iteration once grew past 28 GB, so rewrite word arithmetic explicitly rather than calling the decision procedures on large goals.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
