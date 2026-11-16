# [S] Give pyrind an ecdsa module in rind 0.4's shape

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `pyrind.ecdsa` has `KeyPair` and `PublicKey` in place of `pyrind.signature`'s `EcdsaKeyPair` and a shared `PublicKey`. A public key's constructor takes the algorithm's own encoding, `from_spki` a `SubjectPublicKeyInfo`, and `to_spki` lives only on the public key. A key pair's `public_key()` returns the same object each call. The pull request stays a draft, and no release is published.

## Plan

The work is already claimed on that upstream draft. Continue on its branch; do not open a second claim. Touch `rind-python/python/pyrind/ecdsa/` (new stubs), `rind-python/python/pyrind/signature/__init__.pyi`, and `rind-python/src/signature.rs` only as far as ECDSA. Leave Ed25519, RSA, and key wrap for later steps.

Success check: from the repo root in `nix develop`, build the wheel the way `sh/python.sh test` does, then `PYTHONPATH="$out/site" python3 -m unittest discover --start-directory rind-python/tests -k ecdsa` and `(cd "$out/site" && python3 -m mypy.stubtest pyrind.ecdsa)` both exit 0.

## Related

- [pyrind takes rind 0.4's shape](/quest/m2/api/pyrind-shape.md) - the quest this draft implements
