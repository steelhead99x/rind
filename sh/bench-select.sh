#!/usr/bin/env bash
# Print the bench targets of ROW, space-separated, that a dispatched `bench`
# run asked for in $BENCHES, or all of ROW when BENCHES is empty. An empty ROW
# stands for every rind-bench target. A name in BENCHES that is no rind-bench
# target fails the run, so a typo never measures nothing.
#
# Usage: BENCHES='aes_gcm sha2' sh/bench-select.sh 'ROW'
set -euo pipefail

if [[ $# -ne 1 ]]; then
    echo "usage: BENCHES='NAME...' sh/bench-select.sh 'ROW'" >&2
    exit 2
fi
cd "$(dirname "${BASH_SOURCE[0]}")/.."

mapfile -t all < <(cargo metadata --format-version 1 --no-deps --locked |
    jq -r '.packages[] | select(.name == "rind-bench").targets[] | select(.kind == ["bench"]).name')
read -ra row <<<"$1"
((${#row[@]})) || row=("${all[@]}")
read -ra want <<<"${BENCHES:-}"

for name in "${want[@]}"; do
    if ! printf '%s\n' "${all[@]}" | grep -qxF -- "$name"; then
        echo "sh/bench-select.sh: rind-bench has no bench target '$name'" >&2
        exit 1
    fi
done

selected=()
for name in "${row[@]}"; do
    if ((${#want[@]} == 0)) || printf '%s\n' "${want[@]}" | grep -qxF -- "$name"; then
        selected+=("$name")
    fi
done
echo "${selected[*]}"
