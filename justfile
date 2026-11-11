#!/usr/bin/env just --justfile
# Using Just: https://github.com/casey/just?tab=readme-ov-file#installation
#
# Every recipe is a menu entry: one line that runs a tool, or a script under
# sh/. Logic belongs in the script.

# List the recipes.
default:
    just --list

# Lints, compiles, and tests only the crates the branch changed plus
# everything depending on them; `check --all` is the unscoped suite. BASE
# defaults to the PR base, then a main upstream, then origin/main.

# Lint, compile, and test what the branch changed since BASE, plus its dependents.
check $BASE="":
    sh/dispatch.sh check "$BASE"

# Run CI's gate over the branch diff against BASE; missing tools fail.
ci $BASE="":
    CI_STRICT=1 sh/dispatch.sh ci "$BASE"

# Run CI's gate over every crate.
gate:
    just ci --all

# Report what CI selects before installing the dev shell or build caches.
ci-select $BASE="":
    sh/dispatch.sh ci "$BASE" --query

# Auto-fix lint and formatting for what the branch changed since BASE.
fix $BASE="":
    sh/dispatch.sh fix "$BASE"

# Build, lint, and test armv7, running the tests under qemu on both CPU paths (Linux only).
armv7:
    nix develop .#armv7 --command sh/armv7.sh

# Build, lint, and test SHELL's target, such as s390x or i686, under qemu
# unless the host runs it natively (Linux only).
qemu SHELL:
    nix develop .#{{SHELL}} --command sh/qemu.sh

# Lint and test the portable backend, forced on this x86_64 Linux host.
portable:
    nix develop --command sh/portable.sh

# Lint and test rind on wasm32-wasip2 under wasmtime (Linux only).
wasm:
    nix develop .#wasm --command sh/wasm.sh

# Test the portable backend under Miri for TARGET, such as s390x-unknown-linux-gnu (Linux only).
miri TARGET="x86_64-unknown-linux-gnu":
    nix develop .#miri --command sh/miri.sh {{TARGET}}

# Check dependencies against advisories, licenses, and sources in deny.toml.
audit:
    cargo deny check

# Open or update the release PR, then publish a release PR landed since BEFORE.
release $BEFORE="":
    sh/release.sh "$BEFORE"
