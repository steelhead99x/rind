# [M] The portable backend's SHA-3 is proven

## Goal

SHA3-256, SHA3-384, and SHA3-512 earn the ✓ on the portable backend (`arch = "portable"` in `benchmarks/verified.toml`), and its SHAKE calls rest on the proven sponge: `Rind/X86_64/Sha3.lean`'s proof runs on `admin/prove`'s portable translation, over the Keccak-f `Rind/Portable/Keccak.lean` proves.

## Plan

Decided 2026-11-13 (maintainer, /quest-merge of #649): ✅ keep this quest (rejected: drop).

Found by [the portable backend's proofs](https://github.com/kixel-ai/rind/pull/649), which merged the Keccak-f translation [kixel-ai/rind#647](https://github.com/kixel-ai/rind/pull/647) added into its own and left the sponge opaque there.

- Translation: move the `mid::sha3` start points in `admin/prove` from the `assembly` list to `hashes`, and drop the portable pass's `--opaque crate::mid::sha3` and `Rind/Portable/{Types,Funs}External.lean`'s SHA-3 stand-ins.
- Proof: a `Rind/Portable/KeccakDispatch.lean` states `RunsSha3` as the entry guard alone, as `Sha512Entry.lean` does for SHA-512, and gives `Sha3.lean` the dispatch theorems it uses from `Keccak.lean`'s, with FIPS 202's round constants discharged by `mid::sha3::RC`. Then `admin/prove` writes `Sha3.lean` for the portable backend by renaming the target, as it does for aarch64. Rename `Keccak.lean`'s theorems where they clash with the dispatch's.
- Report: a `verified.toml` row for `sha3-256/*`, `sha3-384/*`, and `sha3-512/*` with `arch = "portable"`, and the portable section of `proofs/README.md` updated.

## Related

- [ML-KEM's construction is proven](/quest/m4/verified/mlkem-construction.md) - its SHAKE calls run this sponge on the portable backend too
