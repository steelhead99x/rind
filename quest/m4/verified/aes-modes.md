# [L] AES-CTR and AES-CBC are proven on x86_64 with AES-NI

## Goal

`cipher::AesCtr` and AES-CBC earn the ✓ on x86_64 with AES-NI, as they have on aarch64 with the crypto extension, where key wrap has it on both.

## Plan

- What is left is HOL Light: `Rind/X86_64/AesModesApi.lean` already proves the APIs over `Rind/X86_64/AesModesLow.lean`'s axioms `hw_ctr32_spec`, `hw_cbc_encrypt_spec`, and `hw_cbc_decrypt_spec`, which restate theorems of aws-lc's `aes_hw_ctr32_encrypt_blocks` and `aes_hw_cbc_encrypt`, as rind's build emits them, in the x86_64 model of rind's s2n-bignum fork, `thirdparty/s2n-bignum`, against `hol-light/x86_64/aes_hw_spec.ml`.
- `hol-light/x86_64/aes_hw_cbc_encrypt.ml` proves CBC encryption (`AES_HW_CBC_ENCRYPT_ENCRYPT_SUBROUTINE_CORRECT`) and decryption (`AES_HW_CBC_ENCRYPT_DECRYPT_SUBROUTINE_CORRECT`).
- Tranches: decided by the owner on 2026-11-25, each tranche lands on its own as it is ready, and this quest stays open for the rest (rejected: hold every tranche until the whole quest is done).
- Done, first tranche ([steelhead99x/rind#268](https://github.com/steelhead99x/rind/pull/268)): the HOL Light theorem for CBC decryption above, finishing `aes_hw_cbc_encrypt.ml` (the one-block path at 0xc0, the frame at 0x120 into the tails and the 8-block loop, the return, and rbp saved and restored). It proves aws-lc's routine only: `hw_cbc_decrypt_spec` stays an axiom whose restatement of that theorem is unchecked, CBC earns no ✓, and nothing about CTR changes.
- Left: CTR's HOL Light proof (below), then the restatement check of all three axioms, their listing in `Rind/X86_64/Axioms.lean`, and the ✓ for `cipher::AesCtr` and AES-CBC; the PR that claims the ✓ deletes this quest.
- `aes_hw_ctr32_encrypt_blocks` has its listing and spec on the `aes-modes/ctr-hol` branch, and no proof yet: its prologue, the 8-block iteration, its tail, and the epilogue, then the subroutine theorem.
- The three axioms landed unproven, unlisted in `Axioms.lean`, with no ✓ claimed and `proofs/README.md` naming them pending (decided with the maintainer on 2026-11-13 on [kixel-ai/rind#707](https://github.com/kixel-ai/rind/pull/707): ✅ land them with the glue (rejected: drop the x86_64 CTR/CBC Lean files until the HOL Light proofs land)).
- `admin/prove`'s `hol_light_proofs` already runs `aes_hw_cbc_encrypt.o`, which needs no new entry; add CTR's `.o` once its proof exists. Once CTR is proven too, check that each axiom restates its theorem (including that `HwSchedule` is the theorem's key schedule, and that the wrappers pass `enc` zero for decryption and slices that give the theorem's nonoverlap), add the x86_64 theorems to `Rind/X86_64/Axioms.lean`, and say so in `proofs/README.md`.
- Running HOL Light: cap its memory (`systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0` under `quest gate`); a Gröbner-basis step in CTR's iteration once grew past 28 GB, so rewrite word arithmetic explicitly rather than calling the decision procedures on large goals.
- Upstream: offering this work to awslabs/s2n-bignum is optional, and there is no standing approval: stop and ask the maintainer before posting there or anywhere outside [the orgs AGENTS.md lists](/AGENTS.md#development) (decided with the maintainer on 2026-11-07 on [kixel-ai/rind#448](https://github.com/kixel-ai/rind/pull/448)).
