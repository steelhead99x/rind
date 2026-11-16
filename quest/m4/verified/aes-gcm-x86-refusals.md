# [M] x86_64's 96-bit AES-GCM theorems state their refusals

## Goal

The x86_64 AES-GCM theorems for 96-bit nonces hold for every input: `AesGcm::encrypt` and `decrypt`, and the AEAD and `aead::gcm::Key` theorems above them, state that AAD of 2^61 bytes or more and messages past 2^36 - 32 bytes are refused with `WrongLength`, leaving the buffer as it was, instead of taking those bounds as hypotheses.

## Plan

- `check_gcm_lengths_eq` (`proofs/Rind/X86_64/AesGcmAny.lean`) already states the refusal, and `aes_gcm_encrypt_any_spec` and `aes_gcm_decrypt_any_spec` there show the shape: split on the bounds, and the refused branch returns its inputs.
- Restate, bottom up: `aes_gcm_encrypt_vale` and `aes_gcm_decrypt_vale` (`AesGcm.lean`), `aes_gcm_encrypt_by8` and `aes_gcm_decrypt_by8` (`AesGcmClmul.lean`), `aes_gcm_encrypt_spec` and `aes_gcm_decrypt_spec`, then the AEAD API's `aes_gcm_seal`, `aes_gcm_seal_append_tag`, `aes_gcm_seal_append_tag_vec`, `aes_gcm_open_separate_tag`, and `aes_gcm_open` (`AesGcmAead.lean`), and `gcm_key_seal`, `gcm_key_seal_append_tag`, `gcm_key_open_separate_tag`, and `gcm_key_open` (`GcmKey.lean`), each with what the API returns and leaves in the buffer on a refusal.
- Split from [the AVX-512 by-16 quest](https://github.com/kixel-ai/rind/pull/773), which carried it from #703 but does not depend on it.
