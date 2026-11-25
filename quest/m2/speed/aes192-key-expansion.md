# [XS] AES-192 key expansion on x86_64 is as fast as aws-lc-rs's

## Goal

On x86_64 with AES-NI, setting up an AES-192-GCM key takes no more than aws-lc-rs's time, as AES-128 and AES-256 already do.

## Plan

Found by the 0.4 report refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)) in the weekly bench's native x86_64 tier ([run 44941104585](https://github.com/kixel-ai/rind/actions/runs/44941104585), a Xeon 6975P with VAES and AVX-512): AES-192-GCM key setup took 111.6 ns against aws-lc-rs's 96.8 (1.15×), while AES-128 took 94.5 against 103.3 and AES-256 92.2 against 101.9. The run before, on an EPYC 9V74, had AES-192 at 132.0 against 136.4.

- `low/x86_64/aes.rs`'s `aes192_expand` runs a loop of eight serial `aesenclast` steps that branches on the step's parity to place round keys straddling its two vectors, where AES-128's and AES-256's expansions are straight-line. Unroll it, or follow aws-lc's `aes_hw_set_encrypt_key_alt` for AES-192, and time both on Intel and AMD tiers; the GHASH key powers the GCM setup builds after it are shared with AES-128 and AES-256, so the difference is in the schedule.
- The expansion is one of the routines `proofs/` translates with Aeneas; keep its proof, or update it in the same PR.
- Bench `aes_gcm` on the weekly bench's x86_64 tiers before and after.
