# [L] An ACVP module wrapper for fresh test sets

## Goal

A `rind-acvp` binary (unpublished, beside rind-bench) answers ACVP test
sets for every algorithm and CPU path in rind's FIPS module, so the lab can
run NIST's production server against it and rind's CI can run fresh demo
sets, not only the sample sets `admin/sync-acvp` keeps.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- ✅ `rind-acvp` speaks the module wrapper protocol of BoringSSL's and aws-lc's `acvptool`. `cargo test -p rind-acvp` checks sample answers for SHA-256 (AFT and standard Monte Carlo), HMAC-SHA-256, AES-ECB, AES-GCM, ECDSA P-256 keyVer and sigVer, ML-KEM-768 keyGen from `d || z`, and ML-DSA-44 keyGen from its seed. `admin/acvp` runs `acvptool` itself when it is on `PATH`. On 2026-11-12, `acvptool -wrapper rind-acvp -json` matched SHA-256 AFT (512 tests) and AES-GCM (60).
- ✅ ML-KEM-768 key generation takes the given `d || z`. ML-DSA key generation takes the given seed. ECDSA keyGen from extra bits is not in `acvptool`'s protocol: it sends only `testing candidates`, and the sample's extra-bits groups carry no seed. The wrapper answers testing candidates.
- ✅ RSA key generation stays out of the module. rind has no FIPS 186-5 generation from the server's seeds or candidates, which this plan allows.
- ✅ No TLS 1.3 KDF command. rind-rustls gives rustls an HMAC (`HkdfUsingHmac` in `rind-rustls/src/cipher_suite.rs`); rustls derives the traffic secrets, outside rind. Nothing to answer until a FIPS build of rind-rustls derives them through rind.
- AES-GCM with `ivGen: internal` is refused. Sealing with an IV the module generates is [its quest](/quest/m4/fips/gcm-iv.md), which is not done. External nonces are answered, and that is what the sample sets contain.
- One process is one CPU path. A debug build, and a release build with `--cfg rind_cpu_disable`, honours `RIND_CPU_DISABLE_<feature>`. The module's load-time mask in a release build is still [the module quest](/quest/m4/fips/module.md); this wrapper calls rind until that crate exists. The paths were not each run here.
- `hmacDRBG` (generate, reseed, prediction resistance) for SHA-1 and SHA-2 is answered by a DRBG written in `rind-acvp`, not by rind. A vector run tests the wrapper. Switch the handler to rind's DRBG once [moq-dev/rind#677](https://github.com/moq-dev/rind/pull/677) lands: that pull adds reseed and generate-with-additional-input to `HmacDrbg`. The known-answer check is aws-lc's `testmodulewrapper` vector, not a sample file: `admin/sync-acvp` does not fetch an `hmacDRBG` set.

## Waiting

- Maintainer: request ACVP demo server credentials from NIST, which issues a TLS client certificate per organization, so fresh sets run before the lab's production run. An agent cannot contact NIST. Optional until the lab is engaged: the offline runs cover the wrapper meanwhile. Done once a credential is stored as a secret and this item is deleted.

## Required

- [The module](/quest/m4/fips/module.md) - the services and CPU mask the wrapper drives
