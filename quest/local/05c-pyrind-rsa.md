# [S] Give pyrind an rsa module in rind 0.4's shape

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `pyrind.rsa` has `KeyPair` and `PublicKey`. An RSA public key takes PKCS#1, is bound to no algorithm, verifies with any `pyrind.rsa` verification algorithm whose modulus floor it meets, refusing a smaller key at `verify`, and has `modulus_len()`. `RsaKeyPair.public_key(algorithm)` becomes `rsa.KeyPair.public_key()`. `rsa.EncryptingKey(algorithm, der)` takes PKCS#1, with `EncryptingKey.from_spki`. The pull request stays a draft, and no release is published.

## Plan

Continue on the #799 branch. Touch `rind-python/python/pyrind/rsa/`, `rind-python/src/rsa.rs`, and the remaining signature RSA surface only.

Success check: from the repo root in `nix develop`, build the wheel the way `sh/python.sh test` does, then `PYTHONPATH="$out/site" python3 -m unittest discover --start-directory rind-python/tests -k rsa` and `(cd "$out/site" && python3 -m mypy.stubtest pyrind.rsa)` both exit 0.

## Required

- [Give pyrind an ed25519 module in rind 0.4's shape](/quest/local/05b-pyrind-ed25519.md) - signatures already share one shape before RSA joins them
