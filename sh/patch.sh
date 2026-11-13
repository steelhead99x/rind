#!/usr/bin/env bash
# Lint, build, and run patch/fixture with ring patched from kixel-ai/rind-patch,
# the way a binary patches it, and rind-ring patched to this checkout, so a
# rind-ring change runs through the shim before its release. Then check that
# ring resolves to the shim alone and rind-ring to this checkout.
#
# Usage: sh/patch.sh
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

args=(
    --manifest-path patch/fixture/Cargo.toml
    --config "patch.crates-io.rind-ring.path=\"$PWD/rind-ring\""
)

cargo fmt --check --manifest-path patch/fixture/Cargo.toml

# A lockfile from an earlier run pins that run's rind-patch commit, so take
# its main as a binary adding the patch now would.
cargo generate-lockfile "${args[@]}"

# A second ring would be crates.io's, kept by a requirement the shim's version
# does not meet, and a rind-ring from crates.io would mean the shim requires a
# version this checkout no longer has. Metadata resolves every target, as a
# build of any would.
packages=$(cargo metadata "${args[@]}" --format-version 1 |
    jq -r '.packages[] | select(.name == "ring" or .name == "rind-ring") | "\(.name) \(.source)"' | sort)
expected=$'^rind-ring null\nring git\\+https://github\\.com/kixel-ai/rind-patch#[0-9a-f]{40}$'
if [[ ! "$packages" =~ $expected ]]; then
    echo "error: expected the rind-patch shim's ring and this checkout's rind-ring, got:" >&2
    echo "$packages" >&2
    exit 1
fi

cargo clippy "${args[@]}" --target-dir target -- --deny warnings
cargo run "${args[@]}" --target-dir target
