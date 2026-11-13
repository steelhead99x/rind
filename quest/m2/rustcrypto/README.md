# rind backs code written for RustCrypto

## Goal

A project written against RustCrypto's traits can run on rind: generic code takes rind's types where it takes `sha2`'s or `aes-gcm`'s, and the maintainer knows, from a spike on real dependency trees, whether one `[patch]` line can move a whole tree the way `rind-patch` moves ring's.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): of the bets the audit offered for making rind usable across the ecosystem, the maintainer picked ✅ the trait implementations and ✅ the `[patch]` spike, with a `no_std` build and adapters on wasm32, which are [adoption's](/quest/m2/adoption/README.md). An npm package was offered and not picked.

Why this one: much of the Rust ecosystem's crypto goes through RustCrypto (crates.io that day counted about 415 million recent downloads of `digest`, 379 million of `sha2`, and 93 million of `aead`). [Adoption](/quest/m2/adoption/README.md) already counts big names on RustCrypto as the marketing wins, since rind is several times faster there, and today each of them would have to rewrite its calls to try it.

- The traits come first and are useful alone: a crate generic over `Digest` or `Aead` takes rind with a type parameter.
- The `[patch]` shims are a spike, because whether they work is not knowable from here. `[patch]` swaps a crate for another of the same name, so a shim has to be named `sha2` and offer `sha2`'s whole API at its version, and RustCrypto's concrete crates expose more than their traits. The spike reports how much of real trees builds and passes; the maintainer decides from that whether shims are a product.
- Both follow AGENTS.md's adapter rule: their own crates, upstream's API and nothing added, a README listing what rind cannot back.
- rind files no upstream PRs to get itself adopted (maintainer, 2026-11-11), and nothing here does.
