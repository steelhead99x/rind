#!/usr/bin/env bash
# Diff published adapters' public APIs against their upstream providers.
# The nightly rustdoc pin and the omissions file format are in admin/adapter-api.py.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
exec python3 admin/adapter-api.py "$@"
