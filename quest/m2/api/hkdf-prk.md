# [S] HKDF PRKs load from bytes and fill a slice

## Goal

A caller that holds a pseudorandom key as bytes, and wants HKDF-Expand written into a slice, does both through `rind::hkdf::Prk`: it loads the bytes, and one call fills the output. rind-ring, rind-aws-lc-rs, and rind-openmls delete the HKDF-Expand each carries today.

## Plan

Found by the 2026-11-12 audit. `Prk` can be made by `Salt::extract`, or from another `Prk`'s `expand` (`impl From<Okm<'_, &'static Algorithm>> for Prk`, `rind/src/high/hkdf.rs:211`), but not from bytes: that constructor is `pub(crate)` (`hkdf.rs:79`). A protocol that receives a PRK, as TLS 1.3's key schedule and MLS's do, has no way in, so three adapters wrote HKDF-Expand over `rind::hmac`: `rind-ring/src/hkdf.rs:105`, `rind-aws-lc-rs/src/hkdf.rs:123` (`expand_into`), and `rind-openmls/src/provider.rs:60`.

- Make the constructor public. The audit recommends the name `Prk::new(algorithm, bytes)`, which is what it is called inside the crate. aws-lc-rs and ring call theirs `new_less_safe`, and AGENTS.md borrows their name only when it is as clear: `less_safe` warns of nothing a caller can act on, since a PRK from bytes is how these protocols work.
- Replace `expand(info, len).fill(out)` with `fill(&self, info: &[&[u8]], out: &mut [u8]) -> Result<(), Error>`. Today the length is given twice, once to `expand` as a `usize` standing in for a key type and again as the slice's length, and a mismatch is a runtime error. Dropping `KeyType for usize` is the breaking change, so the commit is `feat(hkdf)!:`.
- `expand` keeps its other key types (an AEAD key, a QUIC header key, an HMAC key, and the next `Prk`, which HKDF chaining added); this changes only the path that ends in bytes.
- Each adapter then calls rind and deletes its copy. Their own APIs don't change.
- MIGRATING.md's HKDF rows change with it.
- The PRK is secret. If the public constructor or `fill` adds a path `admin/ctgrind` does not already cover, add its test, as AGENTS.md requires.

rind 0.4 [waits for this](/quest/m2/api/release-0.4.md), since a break left out of it would be a 0.5.
