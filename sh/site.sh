#!/usr/bin/env bash
# Build site/ from its frozen lockfile after its unit tests, check the output's
# pages, policy, and links (site/scripts/check.ts), and load it in headless
# Chrome (site/scripts/browser.ts). The build reads crates.io's index and the
# adapters' published READMEs (site/src/lib/registry.ts), so it needs the
# network.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/../site"
bun install --frozen-lockfile
bun test
bun run build
# Chrome puts a socket under $TMPDIR, and a socket's path must fit in 108
# bytes, which a TMPDIR nested by `nix develop` inside another can exceed.
TMPDIR=/tmp bun scripts/browser.ts
