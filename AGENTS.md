rind is a pure-Rust cryptography library for [MoQ](https://github.com/moq-dev/moq), derived from [graviola](https://github.com/ctz/graviola), which it no longer tracks.
This is one Rust workspace: the `rind` library, its `rind-<consumer>` adapter crates such as `rind-rustls`, and the unpublished bench, cpuid, timing, and fuzz crates.
[ARCHITECTURE.md](ARCHITECTURE.md) covers the `low`/`mid`/`high` layering, [PLATFORMS.md](PLATFORMS.md) the CPU requirements, and [CONTRIBUTING.md](CONTRIBUTING.md) how to run the tests.

# Required

- Exactly one backend compiles per target, the portable one where rind has no assembly, and a CPU missing a required feature fails with an error naming it.
- Keys, signatures, ciphertexts, and encodings are hostile input: a malformed one is an error, never a panic, and its cost is bounded by design.
- Secret-dependent code runs in constant time: no branch, memory index, or variable-time instruction depends on a secret. New secret-handling paths get a ctgrind test (`admin/ctgrind`). The one exception is Argon2id's data-dependent half, which picks the memory it reads from password-derived values: the cost of its memory hardness, which RFC 9106 and RFC 9807 accept. It declassifies each such index, so ctgrind still checks the rest.
- Pick the fastest permissively licensed source for each primitive on each backend. Take a formally verified one (s2n-bignum, libcrux/HACL*, fiat-crypto) only where it measures as fast at every size; otherwise run the fastest and plan its proof. New arithmetic states where its correctness argument comes from.
- Test every primitive against Wycheproof where vectors exist, and differentially against aws-lc-rs (a dev-dependency only).
- Give the API one way to do each job. Borrow an aws-lc-rs or ring name only when it is as clear; the migration guide maps theirs to rind's.
- When in doubt about behavior (what to accept, refuse, or wipe), follow aws-lc-rs: it is the library rind would use if it didn't require C.
- A key type wipes its whole value on drop, public parts included: FIPS 140-3 requires zeroising public security parameters too, and a whole-value wipe lets `rind/tests/zeroing.rs` check every byte. Wipe keyed state and heap scratch derived from a private key before they are freed, since that scratch can be as good as the key, but only under the `wipe` feature: wipe through `low::zeroise` or `low::zeroise_value`, which do nothing without it. Wipe nothing else: digest contexts, decrypted messages, stack temporaries, other scratch, and copies inside a call stay unwiped. Safe Rust cannot read them, so wiping them costs speed for nothing.
- Benchmark performance-sensitive changes against aws-lc-rs.
- An adapter for a third-party crate lives in its own `rind-<consumer>` crate, so that crate's major bump never forces one in `rind`. It offers exactly the API of the provider its upstream ships, adding nothing, so swapping one for the other changes no other code; its README lists what rind cannot back. A divergence is a bug, fixed in a patch release.

# Development

PRs target `main`.

Quests: before any work, run `quest context` and follow it, unless this session already holds its rules.
