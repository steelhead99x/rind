# rind offers the building blocks modern protocols need

## Goal

rind offers the primitives that protocols above TLS build on, so their Rust implementations can run entirely on rind:

- HPKE's post-quantum KEMs, and MLS through rind-openmls, on top of `rind::hpke` (RFC 9180);
- RSA blind signatures (RFC 9474) and VOPRF/OPRF (RFC 9497), for Privacy Pass;
- FROST threshold Schnorr signatures (RFC 9591);
- ECVRF (RFC 9381);
- the PAKEs SPAKE2+ (RFC 9383, which Matter uses in a pre-RFC draft) and OPAQUE (RFC 9807).

## Plan

Decided with the maintainer on 2026-11-07, planning m4's long-term work with no token budget. Each block follows `AGENTS.md`'s rules: types that make misuse fail to compile, the RFCs' test vectors and Wycheproof where present, differential tests against an established implementation, and ctgrind for secret paths. aws-lc-rs implements none of these protocols, so the differential tests run against the Rust crate each protocol's consumers already use.

The scope ([kixel-ai/rind#449](https://github.com/kixel-ai/rind/pull/449)) ordered the blocks by reach and planned the primitives rind lacks (hash-to-curve, ristretto255 with a constant-time edwards25519 scalar multiplication, and Argon2id) as their own quests. Each protocol ships as a public rind module with its own misuse-resistant types, and the primitives under them stay crate-internal, rather than rind exposing scalar and point arithmetic for consumers' generic traits (`voprf::Group`, `frost_core::Ciphersuite`). Adapters for a consumer's crypto trait, such as openmls's `OpenMlsCrypto`, are separate `rind-<consumer>` quests, planned when one is wanted.
