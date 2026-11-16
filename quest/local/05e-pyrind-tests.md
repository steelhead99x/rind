# [S] Move pyrind's own tests to the new module shape

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `rind-python/tests/` (`test_api.py`, `test_readme.py`, and `test_wycheproof.py`) call the new `pyrind.ecdsa`, `pyrind.ed25519`, `pyrind.rsa`, and `pyrind.key_wrap` APIs, and those tests pass. The pull request stays a draft, and no release is published.

## Plan

Continue on the #799 branch. Update only files under `rind-python/tests/`.

Success check: from the repo root in `nix develop`, build the wheel the way `sh/python.sh test` does, then `PYTHONPATH="$out/site" python3 -m unittest discover --start-directory rind-python/tests` exits 0.

## Required

- [Reshape pyrind key wrap to wrap_key and unwrap_key with a Mode](/quest/local/05d-pyrind-key-wrap.md) - every public name the tests must move is already in place
