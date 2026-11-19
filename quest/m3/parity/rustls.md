# [S] rustls provider parity

## Goal

rind-rustls offers the rest of aws-lc-rs's rustls provider: the MLKEM1024 key-exchange group, and the ML-DSA-44, ML-DSA-65, and ML-DSA-87 signature schemes, both signing and verifying.

## Plan

- rind has both: ML-KEM-1024 as `kem::DecapsulationKey<MlKem1024>` from [kixel-ai/rind#606](https://github.com/kixel-ai/rind/pull/606), and ML-DSA as `ml_dsa::KeyPair<P>` and `ml_dsa::PublicKey<P>` from [kixel-ai/rind#610](https://github.com/kixel-ai/rind/pull/610). They moved here from m4's post-quantum epic with the maintainer on 2026-11-09 (✅ m3/parity; rejected: m2, or pushing this quest back to m4).
- rind-rustls already offers every other algorithm aws-lc-rs's provider does, `hpke` included.
- `aws_lc_rs_parity` and `aws_lc_rs_items` in `rind-rustls/src/lib.rs` list
  these as the only gaps; drop each exclusion as it lands, and
  each from rind-rustls's README and MIGRATING.md.
