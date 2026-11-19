# [M] rind implements RustCrypto's traits

## Goal

Published adapters give rind's algorithms RustCrypto's traits, so code generic over `Digest`, `Mac`, `Aead`, `Signer` and `Verifier`, or the KEM traits runs on rind by naming a different type. Its tests run RustCrypto's own implementations beside rind's and show the same outputs.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ build it. The audit recommended the name `rind-rustcrypto`; the split below replaces it with one crate per trait crate.

- The trait crates on crates.io that day: `digest` 0.11.3, `aead` 0.6.1, `signature` 3.0.0, `kem` 0.3.0. Confirm with `cargo info` when starting, and target the current release of each.
- What to implement, in the order the downloads suggest: SHA-2 and SHA-3 as `Digest`; HMAC as `Mac`; AES-GCM and ChaCha20-Poly1305 as `Aead` and its in-place form; ECDSA, Ed25519, RSA, and ML-DSA as `Signer` and `Verifier`; ML-KEM as the KEM traits. Each type is a thin wrapper that calls rind.
- A trait rind cannot back honestly is left out and listed in the README: `Digest`'s `Clone` of a running hash and its `Reset` only where rind's context has them, and nothing that needs a raw block cipher or an unauthenticated stream cipher unless `rind::cipher` already offers it.
- Tests: each implementation against RustCrypto's own crate for the same algorithm as a dev-dependency (`sha2`, `hmac`, `aes-gcm`, `p256`, `ed25519-dalek`, `rsa`, `ml-kem`), on fixed and random inputs and on the edges: empty and maximal lengths, a wrong tag, and a malformed key, signature, or ciphertext, which both must refuse. ML-KEM is the exception to test as what it is: an altered ciphertext of the right length is not refused but decapsulates to FIPS 203's implicit-rejection secret, so there the test is that both return the same secret, and that it differs from the real one. Only a ciphertext of the wrong length is an error. Plus one generic function per trait instantiated with rind's type. The adapters add no primitive and no encoding, so Wycheproof and the aws-lc-rs differential stay where AGENTS.md puts them, on rind's own tests of what each wrapper calls.
- It handles secrets only by passing them to rind, so it adds no constant-time path of its own. If a trait forces a copy of a key into a wrapper, that copy is a new secret-handling path: the wrapper wipes it as AGENTS.md's key types do, and gets a constant-time test of its own. An adapter cannot reach rind's `low::ct::secret_slice`, which is `pub(crate)` in a private module, so its test marks the bytes secret through `crabgrind`, as `rind-ring/tests/ctgrind.rs` does, and `admin/ctgrind` runs it.
- MIGRATING.md gains a section mapping RustCrypto's crates to rind's types, and the README lists the crates with the other adapters.
- Decided 2026-11-18 (maintainer, /quest-complete): ✅ a crate per trait crate, `rind-digest` 0.11.x, `rind-aead` 0.6.x, `rind-signature` 3.x, and `rind-kem` 0.3.x, each following `sh/adapter-versions.sh`'s version rule as written, with no change to the script (rejected: one `rind-rustcrypto` crate versioned on its own, with a feature per trait crate and version). Each adapts one upstream, as every other `rind-<consumer>` crate does, so a trait crate's new major bumps only its own adapter.
- A new crate cannot be created by trusted publishing: `CONTRIBUTING.md`'s Releases section has the maintainer publish its first version by hand, so the PR sets `release = false` for each in `.release-plz.toml` until then, as [rind 0.4's quest](/quest/m2/api/release-0.4.md) plans for rind-openmls.

