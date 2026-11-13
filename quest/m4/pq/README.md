# rind covers the standardized post-quantum algorithms

## Goal

rind offers every NIST post-quantum standard and the hybrids that TLS, HPKE, and MLS deploy, without waiting for a consumer: ML-KEM-512 and ML-KEM-1024 beside today's ML-KEM-768, ML-DSA-44/65/87, SLH-DSA, the hybrid KEMs (X-Wing, and P-256 and P-384 with ML-KEM), and FN-DSA and HQC once NIST finalizes them.

## Plan

Decided with the maintainer on 2026-11-07, planning m4's long-term work with no token budget. These leave [aws-lc-rs extras on demand](/quest/m3/parity/aws-lc-extras.md) and are built here, except [ML-KEM-512 and ML-KEM-1024](/quest/m3/parity/ml-kem.md) and ML-DSA (landed in [kixel-ai/rind#610](https://github.com/kixel-ai/rind/pull/610)), which moved to m3's parity epic with the maintainer on 2026-11-09 (✅ m3/parity; rejected: m2, or pushing rustls parity back to m4): [rustls provider parity](/quest/m3/parity/rustls.md) needs them, and m3 could not finish while they sat here. The leaves below build on the typed API ML-KEM's quest sets.

- Each algorithm follows `AGENTS.md`: a verified source where one exists (mlkem-native, mldsa-native, s2n-bignum, libcrux's hax-verified ML-KEM and ML-DSA), Wycheproof and NIST vectors, differential tests against aws-lc-rs, ctgrind, and a benchmark on every backend.
- The scope ([kixel-ai/rind#450](https://github.com/kixel-ai/rind/pull/450), 2026-11-06) planned one leaf per algorithm below, in build order. Its measurements: mldsa-native's and mlkem-native's proven kernels, through s2n-bignum, are the fastest sources for ML-KEM and ML-DSA (libcrux trails aws-lc-rs, which runs them); the SPHINCS+ team's SIMD code is the fastest SLH-DSA, and none is verified; FN-DSA and HQC have no draft FIPS yet.
- API, across the epic (maintainer, 2026-11-07, on [kixel-ai/rind#450](https://github.com/kixel-ai/rind/pull/450)): one sealed marker type per parameter set parameterizes the key, ciphertext, and signature types, such as `DecapsulationKey<MlKem1024>` and `MlDsaKeyPair<MlDsa65>`, so a wrong pairing fails to compile and each type is its set's exact size. Verification keeps the `&'static` algorithm constants of `signature::verify`, since a certificate names its algorithm at run time. The leaves may update ARCHITECTURE.md's `&'static` rule to match and break rind-rustls, rind-bench, and the fuzzers, in the next breaking release.
- Where aws-lc-rs lacks an algorithm (SLH-DSA, X-Wing, the CFRG hybrids, FN-DSA, HQC), differential tests run against libcrux, RustCrypto, or `fips205` instead, plus the published vectors, and behavior follows the standard and its LAMPS or IETF profile (maintainer, 2026-11-07). The first leaf that needs this adds a line to AGENTS.md's differential-testing rule saying so, which the maintainer approved.
