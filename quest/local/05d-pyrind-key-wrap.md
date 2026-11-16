# [S] Reshape pyrind key wrap to wrap_key and unwrap_key with a Mode

## Goal

On the branch of https://github.com/kixel-ai/rind/pull/799, `pyrind.key_wrap.AesKek`'s four methods are `wrap_key(mode, key)` and `unwrap_key(mode, wrapped)` with a `key_wrap.Mode` of `KW` or `KWP`. The pull request stays a draft, and no release is published.

## Plan

Continue on the #799 branch. Touch `rind-python/python/pyrind/key_wrap.pyi` and the matching Rust bindings only.

Success check: from the repo root in `nix develop`, build the wheel the way `sh/python.sh test` does, then `PYTHONPATH="$out/site" python3 -m unittest discover --start-directory rind-python/tests -k key_wrap` and `(cd "$out/site" && python3 -m mypy.stubtest pyrind.key_wrap)` both exit 0.

## Required

- [Give pyrind an rsa module in rind 0.4's shape](/quest/local/05c-pyrind-rsa.md) - the rest of the 0.4 shape is in place before key wrap changes
