# [S] Point pyrind-cryptography internals at the new pyrind API

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, pyrind-cryptography's internals use the new pyrind calls wherever they used pyrind's Python API, and its own tests still pass. pyrind-cryptography keeps pyca/cryptography's API exactly. The pull request stays a draft, and no release is published.

## Plan

Continue on the #799 branch. Touch `rind-python/cryptography/pyrind_cryptography/hazmat/primitives/asymmetric/ec.py`, `ed25519.py`, `rsa.py`, and `rind-python/cryptography/pyrind_cryptography/hazmat/primitives/keywrap.py`, plus `rind-python/cryptography/tests/` only if a call site forces it.

Success check: from the repo root in `nix develop`, build the wheel the way `sh/python.sh test` does, then `PYTHONPATH="$out/site:rind-python/cryptography" python3 -m unittest discover --start-directory rind-python/cryptography/tests` exits 0.

## Required

- [Move pyrind's own tests to the new module shape](/quest/local/05e-pyrind-tests.md) - pyrind's public API is stable enough for the adapter to move
