# [S] SHA-256's streaming context costs no more than one-shot on short inputs

## Goal

`digest::Context::new`, `update`, and `finish` for SHA-256 run within noise of one-shot `digest::digest` at 16 B and 64 B on x86_64 and aarch64.

## Plan

Found on 2026-11-12, benchmarking pyca/verified-garbage against rind on a Ryzen 9 9950X: SHA-256 through the context took about 36 ns at 16 to 64 B, against 19 ns one-shot. Decided with the maintainer the same day: ✅ a quest in m2. TLS and QUIC hash many short transcripts through the context.

- Find where the 17 ns goes, such as dispatch, buffer setup, or copying the state, and remove it. Check SHA-384/512 and HMAC's context for the same overhead.
- Prove nothing is lost: the digest proofs in `proofs/` cover the context path, so a change there keeps `admin/prove` passing.
