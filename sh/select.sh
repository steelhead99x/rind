#!/usr/bin/env bash
# Print the Cargo package arguments for the crates a diff touches, plus every
# workspace crate depending on them, one argument per line.
#
# Usage: sh/select.sh CHANGED_FILE [ALL] [--lib]
# A change outside any crate's directory (the root manifest, the lockfile,
# thirdparty/ test vectors) can reach every crate, so it selects --workspace,
# as does a non-empty ALL. --lib keeps only the crates with a library, which
# `cargo test --doc` requires.
set -euo pipefail

usage="usage: sh/select.sh CHANGED_FILE [ALL] [--lib]"
changed=${1:?$usage}
all=${2:-}
lib=${3:-}
if [[ $# -gt 3 || (-n "$lib" && "$lib" != --lib) ]]; then
    echo "$usage" >&2
    exit 2
fi

if [[ -n "$all" ]]; then
    echo --workspace
    exit
fi

root=$(git rev-parse --show-toplevel)
metadata=$(cargo metadata --format-version 1 --no-deps --locked)

# Each member's directory, relative to the root, and its name.
declare -A dirs=()
while IFS=$'\t' read -r dir name; do
    dirs[$dir]=$name
done < <(jq -r --arg root "$root/" '.packages[] | [(.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml")), .name] | @tsv' <<<"$metadata")

declare -A selected=()
while IFS= read -r path; do
    # The innermost crate directory holding the path, so a nested crate such
    # as rind-fips/module is selected rather than its parent.
    dir=${path%/*}
    while [[ "$dir" == */* && -z "${dirs[$dir]:-}" ]]; do
        dir=${dir%/*}
    done
    if [[ "$path" == */* && -n "${dirs[$dir]:-}" ]]; then
        selected[${dirs[$dir]}]=1
    elif grep -qE '^(thirdparty/|Cargo\.(toml|lock)$|\.rustfmt(\.unstable)?\.toml$)' <<<"$path"; then
        echo --workspace
        exit
    fi
done <"$changed"

# Add workspace dependents until nothing new appears. rind-fips's build
# script builds rind-fips-module with a cargo of its own, an edge the
# metadata does not show.
edges=$(jq -r '.packages[] | .name as $n | .dependencies[] | select(.path != null) | [.name, $n] | @tsv' <<<"$metadata")
edges+=$'\nrind-fips-module\trind-fips'
grew=1
while [[ -n "$grew" ]]; do
    grew=
    while IFS=$'\t' read -r dep dependent; do
        if [[ -n "${selected[$dep]:-}" && -z "${selected[$dependent]:-}" ]]; then
            selected[$dependent]=1
            grew=1
        fi
    done <<<"$edges"
done

libs=$(jq -r '.packages[] | select(any(.targets[]; .kind | index("lib"))) | .name' <<<"$metadata")
for name in "${!selected[@]}"; do
    if [[ -z "$lib" ]] || grep -qxF "$name" <<<"$libs"; then
        printf -- '-p\n%s\n' "$name"
    fi
done
