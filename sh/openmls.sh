#!/usr/bin/env bash
# Runs openmls's own test suite, its known-answer and interop vectors
# included, on rind-openmls: checks out openmls at the release Cargo.lock
# pins, swaps its openmls_rust_crypto for a crate re-exporting rind-openmls,
# which has the same API, and tests openmls with every ciphersuite the
# provider offers. Extra arguments go to `cargo test`.
#
# Usage: sh/openmls.sh [cargo test arguments]
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
root=$PWD
version=$(cargo metadata --format-version 1 --locked |
    jq -r '[.packages[] | select(.name == "openmls") | .version] | if length == 1 then .[0] else error("expected one openmls in Cargo.lock") end')
dir=.tmp/upstream/openmls@$version

rm -rf "$dir"
git init -q "$dir"
git -C "$dir" fetch -q --depth 1 https://github.com/openmls/openmls "refs/tags/v$version"
git -C "$dir" -c advice.detachedHead=false checkout -q FETCH_HEAD

# openmls's crates name the draft features too, so the stand-in declares them,
# empty: nothing here turns them on.
rm -rf "$dir/openmls_rust_crypto"
mkdir -p "$dir/openmls_rust_crypto/src"
echo 'pub use rind_openmls::*;' >"$dir/openmls_rust_crypto/src/lib.rs"
cat >"$dir/openmls_rust_crypto/Cargo.toml" <<EOF
[package]
name = "openmls_rust_crypto"
version = "$(sed -n 's/^version = "\(.*\)"$/\1/p' "$dir/traits/Cargo.toml")"
edition = "2024"

[dependencies]
rind-openmls = { path = "$root/rind-openmls" }

[features]
test-utils = ["rind-openmls/test-utils"]
extensions-draft = ["rind-openmls/extensions-draft"]
draft-ietf-mls-pq-ciphersuites = []
targeted-messages-draft = []
virtual-clients-draft = []
EOF

# rind-openmls takes openmls_traits and openmls_memory_storage from crates.io;
# these make it share openmls's own copies.
cat >>"$dir/Cargo.toml" <<'EOF'

[patch.crates-io]
openmls_traits = { path = "traits" }
openmls_memory_storage = { path = "memory_storage" }
EOF

cd "$dir"
CARGO_TARGET_DIR="$root/target/openmls" cargo test -p openmls --no-default-features \
    --features extensions-draft,extensions-draft-test-dependencies,all-ciphersuites "$@"
