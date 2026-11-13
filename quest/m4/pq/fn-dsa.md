# [L] FN-DSA

## Goal

rind signs and verifies FN-DSA (FIPS 206, from Falcon) at both parameter sets, on every backend, once NIST publishes the final standard.

## Plan

From [the scope](/quest/m4/pq/README.md), 2026-11-06.

- Candidate: Thomas Pornin's [`fn-dsa`](https://github.com/pornin/rust-fn-dsa) (Rust, Unlicense), which tracks NIST's draft and promises compatibility only from its 1.0. It measured 125 µs to sign and 6.7 µs to verify FN-DSA-512 on desktop (1.3 ms keygen). Its signing uses the hardware `f64` on x86_64 and aarch64, relying on those instructions running in constant time; decide then whether to keep that or its integer emulation, and measure both. `AGENTS.md` lets no variable-time instruction depend on a secret, so keeping the hardware path takes either evidence that those instructions run in constant time on every CPU rind supports or an exception recorded in `AGENTS.md`, as [Argon2id](/quest/m4/protocols/argon2.md)'s is; that is the maintainer's call when this is scoped again.
- No verified implementation exists, and aws-lc-rs has none. The [epic](/quest/m4/pq/README.md)'s rule sends differential tests to libcrux, RustCrypto, or `fips205`, and on 2026-11-09 none of them implements FN-DSA ([RustCrypto/signatures](https://github.com/RustCrypto/signatures) and [libcrux](https://github.com/cryspen/libcrux) have no such crate). A port of `fn-dsa` cannot be its own oracle, so name an independent one when this is scoped again.
- Scope it again when the standard lands: the API follows ML-DSA's (`signature::sign::MlDsaKeyPair<P>` over sealed parameter-set markers, from [kixel-ai/rind#610](https://github.com/kixel-ai/rind/pull/610)), and tests take ACVP vectors once NIST publishes them, through `admin/sync-acvp` and `crate::test::acvp`. ACVP-Server v1.1.0.43 has no FN-DSA set.

## Waiting

- NIST: publishes FIPS 206. As of NIST IR 8547 (2026-10-27) it is still being developed and no draft is out. Check [NIST's FIPS list](https://csrc.nist.gov/publications/fips) for FIPS 206 final; on 2026-11-09 it lists nothing above FIPS 205.
