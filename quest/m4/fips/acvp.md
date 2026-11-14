# [L] An ACVP module wrapper for fresh test sets

## Goal

A `rind-acvp` binary (unpublished, beside rind-bench) answers ACVP test
sets for every algorithm and CPU path in rind's FIPS module, so the lab can
run NIST's production server against it and rind's CI can run fresh demo
sets, not only the sample sets `admin/sync-acvp` keeps.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- ✅ `rind-acvp` speaks the module wrapper protocol of BoringSSL's and aws-lc's `acvptool`. `cargo test -p rind-acvp` checks sample answers, hostile operation parameters, complete request framing, and secret reply ownership. The executable tests SHA, HMAC, PBKDF, DRBG, and all three advertised ECDH curves over that protocol. `admin/acvp` runs the client over every supported sample set, compares every required deterministic result field, and rejects missing, duplicate, or unexpected replies, including missing Monte Carlo entries. Fresh keys and signatures are checked for encoded results; the client also asks the wrapper to verify ECDSA and RSA signatures. All ML-DSA signing and verification samples run, including the empty external context. The runner omits multi-GiB hash LDT samples in favor of a short crate test; both the client and wrapper accept LDT requests through 8 GiB. Its header also lists client restrictions: alternate Monte Carlo, partial-byte AES-CTR, ECDSA keyGen other than testing candidates, and RSA sigVer public exponents above 33 bits. Raw RSA primitives accept the wider exponents in their sample sets.
- ✅ The registration describes the client's supported subset. HMAC uses revision 1.0, ML-KEM encapsulation uses expanded keys and FIPS203-tr1, ML-DSA signing uses expanded keys and pure external/internal interfaces under FIPS204-tr1, KDA requests non-hybrid inputs, GCM uses an external IV, and CTR advertises byte-aligned final partial blocks. The framed registration test checks these contracts. [UPSTREAM.md](/UPSTREAM.md#acvptool-expects-older-sample-formats) records the sample adaptations and pinned client.
- ✅ ML-KEM-768 key generation takes the given `d || z`. ML-DSA key generation takes the given seed. ECDSA keyGen from extra bits is not in `acvptool`'s protocol: it sends only `testing candidates`, and the sample's extra-bits groups carry no seed. The wrapper answers testing candidates.
- ✅ RSA key generation stays out of the module. rind has no FIPS 186-5 generation from the server's seeds or candidates, which this plan allows.
- ✅ No TLS 1.3 KDF command. rind-rustls gives rustls an HMAC (`HkdfUsingHmac` in `rind-rustls/src/cipher_suite.rs`); rustls derives the traffic secrets, outside rind. Nothing to answer until a FIPS build of rind-rustls derives them through rind.
- AES-GCM with `ivGen: internal` is refused. Sealing with an IV the module generates is [its quest](/quest/m4/fips/gcm-iv.md), which is not done. External nonces are answered, and that is what the sample sets contain.
- One process is one CPU path. A debug build, and a release build with `--cfg rind_cpu_disable`, honours `RIND_CPU_DISABLE_<feature>`. `rind-fips` applies that mask as the module loads. This wrapper calls rind: the module does not offer `__acvp`'s seeded operations. The paths were not each run here.
- ✅ `hmacDRBG` (generate, reseed, prediction resistance) for SHA-1 and SHA-2 is rind's `HmacDrbg` ([moq-dev/rind#677](https://github.com/moq-dev/rind/pull/677)). In addition to aws-lc's known-answer vector, `admin/acvp` runs independent Python oracles for all four advertised DRBG hashes and modes, PBKDF for every advertised hash, KDA/HKDF through its 255-block limit, and the vendored CAVP ECDH answers for every advertised scheme and role. `admin/sync-acvp` does not fetch a DRBG sample set.

## Waiting

- Maintainer: request ACVP demo server credentials from NIST, which issues a TLS client certificate per organization, so fresh sets run before the lab's production run. An agent cannot contact NIST. Optional until the lab is engaged: the offline runs cover the wrapper meanwhile. Done once a credential is stored as a secret and this item is deleted.
