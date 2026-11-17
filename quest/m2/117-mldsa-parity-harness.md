# [M] ML-DSA parity harness refusal kinds

## Goal

ML-DSA refuses malformed keys with the same error kinds as aws-lc-rs, and every secret path the adapter's refusal checks add runs in constant time under ctgrind.

## Plan

Fork PR #117 against fork `main`, which carries the former `cursor/mldsa-error-kinds-71e2` adapter work.

- Decided 2026-11-17 (maintainer, PR #117 comment 6935083086): ✅ Option A, keep aws-lc-rs's exact refusal kinds; a wrong-set key is loaded in full first, and ctgrind covers that path (rejected: Option B, refusing by length up front, which returns `Unspecified` where aws-lc-rs returns `InvalidEncoding`). Done: `from_raw_private_key` and `from_pkcs8` load every wrong-set key in full, `tests/parity.rs` pins each form, tail, and set against aws-lc-rs 1.19.0, and `tests/ctgrind.rs` checks the raw and PKCS#8 wrong-set loads.
- Left: `from_pkcs8` names `WrongAlgorithm` for a secp256k1, P-224, brainpoolP256r1, or DSA key only after checking its secret scalar in the adapter. The checks are branch-free, but the adapter cannot declassify their verdict, so a ctgrind test of that path fails on the one branch on it.

## Waiting

- Maintainer: how the adapter's `WrongAlgorithm` verdict gets ctgrind coverage. Options: a hidden `__ctgrind` feature on rind-aws-lc-rs that marks the verdict public, enabled by `admin/ctgrind` (recommended: the checks stay exact and the rule that new secret paths get a ctgrind test holds); or refuse those curves' and DSA's keys as `WrongAlgorithm` from the public OID alone and delete the adapter's curve arithmetic, which diverges from aws-lc-rs only for a malformed key of a type rind cannot load.

## Related

- [Close #109](/quest/review-followups/README.md) - superseded by this branch plus #117
