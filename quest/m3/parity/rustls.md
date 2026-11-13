# [S] rustls provider parity

## Goal

rind-rustls offers the rest of aws-lc-rs's rustls provider: the MLKEM1024 key-exchange group, and the ML-DSA-44, ML-DSA-65, and ML-DSA-87 signature schemes, both signing and verifying.

## Plan

- Waits on rind having ML-KEM-1024, which its sibling below builds; rind's ML-DSA landed in [kixel-ai/rind#610](https://github.com/kixel-ai/rind/pull/610), as `signature::sign::MlDsaKeyPair<P>` and `signature::verify::ML_DSA_*`. They moved here from m4's post-quantum epic with the maintainer on 2026-11-09 (✅ m3/parity; rejected: m2, or pushing this quest back to m4), so this quest no longer waits on a later milestone.
- rind-rustls already offers every other algorithm aws-lc-rs's provider does, `hpke` included.
- `aws_lc_rs_parity` and `aws_lc_rs_items` in `rind-rustls/src/lib.rs` list
  these as the only gaps; drop each exclusion as it lands, and
  each from rind-rustls's README and MIGRATING.md.

## Required

- [ML-KEM-512 and ML-KEM-1024](/quest/m3/parity/ml-kem.md) - rind's ML-KEM-1024
