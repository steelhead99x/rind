Repository-specific review rules for `rind` (extends Quest's shared review rules, read from the base branch).

# Cryptography checks

`rind` is a cryptography library: assume a secret leaks and hostile input breaks it until the diff shows otherwise. Check these first on every added or touched path:

- **Constant time**: trace each secret through the change. A secret-dependent branch, index, or variable-time instruction is a finding, as is a new secret not covered by `low::ct::secret_slice` or `admin/ctgrind`.
- **Panics**: every `unwrap`, `expect`, index, slice, overflow, or `assert` reachable from caller input is a finding unless the types rule it out.
- **Coverage**: a primitive or encoding missing Wycheproof vectors (where they exist) or differential tests against `aws-lc-rs` and an independent Rust oracle (listed in `TESTING.md`; oracle alone where `aws-lc-rs` lacks it) is incomplete. Verify edges (zero, modulus, empty/maximal lengths, malformed encodings).
- **Wiped secrets**: key types zeroise their whole value on drop (public parts included, tested in `rind/tests/zeroing.rs`; enums holding only such key types like `rind::KeyPair` don't add their own `Drop`); keyed state and private-key-derived heap scratch zeroise via `low::zeroise` / `low::zeroise_value`. Wiping anything else (digest contexts, decrypted messages, copies inside a call, stack/unkeyed heap scratch) is a finding, except inside `rind-fips` (which zeroes service stacks and freed heap blocks) or unmodified proven upstream routines.

# Dependabot

A Dependabot PR's lockfile update can take a crate release younger than `.github/dependabot.yml`'s cooldown. Run `sh/cooldown.sh <base>` on its head: any listed release is a finding until 7 days old.
