# [XL] The rind-fips module: boundary, self-tests, and approved services

## Goal

A `rind-fips` crate builds a module that meets FIPS 140-3 Level 1's software
requirements: a defined boundary with a load-time integrity test, the
self-tests, an error state, approved services only, and the zeroization FIPS
adds to rind's `wipe`. Its API is rind's, minus what is not approved, so
`use rind_fips as rind` compiles wherever a consumer uses only approved
algorithms.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- Boundary: a `cdylib` built by `rind-fips`'s build script with pinned flags
  (`panic = "abort"`, no LTO into the caller), whose `.text` and `.rodata`
  are the module, as aws-lc's dynamic module is `bcm.o` inside
  `libcrypto.so`. A Rust `rlib` cannot be a boundary: generics and inlining
  put module code in the caller's codegen units, so the module exports a
  non-generic C ABI over opaque, heap-held handles, and `rind-fips` wraps it
  in rind's types. Static linking needs aws-lc's delocation (out-calls through
  redirectors, rodata folded into text, so the final link relocates nothing
  hashed); try running aws-lc's `delocate` on rustc's `--emit asm` only once
  a consumer needs a static module, as a second certificate like aws-lc's
  static #5314.
- Integrity: a constructor runs the HMAC-SHA2-256 and SHA2-256 CASTs, then
  compares an HMAC-SHA2-256 over the module's text and rodata with the value
  a post-link step (rind's equivalent of `inject_hash.go`) wrote into the
  library. Function pointers in `.data.rel.ro`, such as CPU dispatch tables,
  sit outside the hash, so the module keeps none; a test reads the built
  library and fails if it has any. Also an on-demand integrity test service.
- Self-tests: every other CAST runs once before its algorithm's first use
  (allowed by IG 10.3.A; aws-lc 3.1 runs them all at load, costing startup
  every process pays), at the smallest approved size, for each function
  (encrypt and decrypt, sign and verify, encaps and decaps). A pairwise
  consistency test follows every key pair generation: ECDSA, Ed25519, RSA,
  ML-KEM, and ML-DSA. A failure prints which test failed and aborts, as
  aws-lc does; output stays inhibited. A `BREAK_TESTS`-style build corrupts
  each test's input so the lab sees every failure path.
- Approved services only, with approved parameters as types: RSA signing at
  2048 bits and up, SHA-1 only for HMAC and legacy verification, PBKDF2 with
  SP 800-132's salt and output floors, AES-GCM sealing only with an
  internally generated IV ([its quest](/quest/m4/fips/gcm-iv.md)). A
  `version()` service names the module and version.
- Zeroization, beyond `wipe`, which the module always enables:
  - SSPs that live only inside a call: ECDSA's nonce and its inverse, ECDH's
    shared secret and its intermediate points, ML-KEM's re-encryption
    message and implicit-rejection key, ML-DSA's `y` and `rnd`, RSA's CRT
    intermediates and blinding factors, HMAC's padded key blocks, HKDF's PRK,
    PBKDF2's `U` blocks, and expanded AES and GHASH keys on the stack.
  - Moves: a moved Rust value leaves its old bytes behind, so keys live only
    behind the module's heap handles and are never moved.
  - DRBG state at process exit, as aws-lc's destructor does.
  Measure what this costs against rind and aws-lc-rs's FIPS build.
- CPU paths: every path the module can select on a tested operational
  environment gets its own ACVP run ([the client](/quest/m4/fips/acvp.md)),
  reached with a load-time CPU mask in the release build (today
  `RIND_CPU_DISABLE_*` works only in debug builds). Paths that run on no
  tested CPU, such as x86_64's SSE2 integer AES, are left out of the module,
  which refuses such CPUs with an error naming the feature.

## Waiting

- Maintainer: approve the module's exception to `AGENTS.md`'s wipe rule, which keeps stack temporaries and copies inside a call unwiped and leaves `wipe` opt-in. FIPS requires zeroizing SSPs once no longer needed, temporaries included. Options: add one line saying the FIPS module always wipes and also wipes SSPs inside a call (recommended: it confines the cost to `rind-fips`); or wipe temporaries in `rind` too, so the module needs no exception (slower for every consumer). An agent cannot change an `AGENTS.md` rule unprompted. Done once the rule is settled in the Plan and this item is deleted.

## Required

- [The DRBG](/quest/m4/fips/drbg.md) - the approved random generator every key generation and internal IV draws from
