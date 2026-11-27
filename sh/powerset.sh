#!/usr/bin/env bash
# Lints the library of each published crate under every combination of its
# Cargo features, as cargo-hack's powerset picks them, so no combination a
# dependent can turn on breaks its build or leaves dead code, as `just
# powerset` runs it in the dev shell.
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

metadata=$(cargo metadata --format-version 1 --no-deps --locked)
mapfile -t crates < <(jq -r '.packages[] | select(.publish == null) | "\(.name) \(.manifest_path | rtrimstr("/Cargo.toml"))"' <<<"$metadata")
for crate in "${crates[@]}"; do
    name=${crate%% *}
    dir=${crate#* }
    features() {
        jq -r --arg name "$name" ".packages[] | select(.name == \$name) | .features | to_entries[] | $1 | .key" <<<"$metadata"
    }
    # A feature that turns on nothing and that the library's code never names
    # changes no build of it, such as one kept only so an upstream's feature
    # list carries over. These toggle together, as one, rather than doubling
    # the powerset each.
    noops=()
    while read -r feature; do
        grep -rqE "feature *= *\"$feature\"" "$dir/src" "$dir"/build.rs 2>/dev/null || noops+=("$feature")
    done < <(features 'select(.value == [] and (.key | startswith("__") | not))')
    args=()
    if ((${#noops[@]} > 1)); then
        args+=(--group-features "$(IFS=,; echo "${noops[*]}")")
    fi
    # Features named `__*` are the workspace's own test hooks, such as
    # `__ctgrind`, which no dependent turns on.
    hidden=$(features 'select(.key | startswith("__"))' | paste -sd,)
    [[ -z "$hidden" ]] || args+=(--exclude-features "$hidden")
    cargo hack clippy -p "$name" --feature-powerset "${args[@]}" --lib --locked -- --deny warnings
done
