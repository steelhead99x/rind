# [S] P-256 verification with a key used once costs no more than aws-lc-rs's on rind's own arithmetic

## Goal

Where rind verifies P-256 ECDSA on its own arithmetic (x86_64 without BMI2 and ADX, armv7, and the portable backend), verifying with a key parsed for that one call, as `UnparsedPublicKey` and rustls do, takes no more than aws-lc-rs's time, while a key parsed once and reused keeps its cached table.

## Plan

Found by the 0.4 report refresh ([kixel-ai/rind#991](https://github.com/kixel-ai/rind/pull/991)) in the weekly bench's `no ADX` tier ([run 44941104585](https://github.com/kixel-ai/rind/actions/runs/44941104585), a Xeon 6975P with ADX denied): one-shot verification took 52.1 µs against aws-lc-rs's 45.3 (1.15×), while the same key parsed once took 46.4 against 44.4, so about 5.7 µs of rind's one-shot time is per-key setup. The AMD EPYC 7763 tiers pay about 7.3 µs the same way (67.8 against 60.5 µs), under 10% of aws-lc-rs's time there only because the parsed path is faster.

- `mid/p256.rs`'s `VerifyingKey::raw_ecdsa_verify` builds P, 3P, ..., 15P on first use with `public_odd_multiples`: a doubling, seven additions, and `public_batch_as_affine`'s one `bignum_inv_p256` and per-point conversions. The cache pays for that on a reused key, not on a key verified once.
- Profile where the setup goes, then try a one-shot path that leaves the multiples in Jacobian form and adds them with full rather than mixed additions, or a smaller window for a key used once. Keep whichever is fastest on the one-shot row without slowing the parsed row.
- Bench `p256` on the weekly bench's `no ADX` tier, armv7, and the portable tier, and on `ovh-iad` and `ovh-sea` (Haswell, no ADX), before and after.
