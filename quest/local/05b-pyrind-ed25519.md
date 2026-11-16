# [S] Give pyrind an ed25519 module in rind 0.4's shape

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `pyrind.ed25519` has `KeyPair` and `PublicKey` in place of `pyrind.signature`'s `Ed25519KeyPair` and a shared `PublicKey`, with the same constructor, `from_spki`, `to_spki`, and cached `public_key()` rules as the ecdsa module. The pull request stays a draft, and no release is published.

## Plan

Continue on the #799 branch. Touch `rind-python/python/pyrind/ed25519/` (new stubs), `rind-python/python/pyrind/signature/__init__.pyi`, and `rind-python/src/signature.rs` only as far as Ed25519.

Success check: from the repo root in `nix develop`, build the wheel the way `sh/python.sh test` does, then `PYTHONPATH="$out/site" python3 -m unittest discover --start-directory rind-python/tests -k ed25519` and `(cd "$out/site" && python3 -m mypy.stubtest pyrind.ed25519)` both exit 0.

## Required

- [Give pyrind an ecdsa module in rind 0.4's shape](/quest/local/05a-pyrind-ecdsa.md) - the first per-algorithm module, so Ed25519 can match its shape
