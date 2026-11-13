#!/usr/bin/env bash
# Verify every third-party action the workflows and composite actions use is
# pinned to a full commit SHA with its version in a trailing comment, so a moved
# tag or branch can't change what CI runs, and Dependabot can keep it current.
# Local actions (./) are exempt: they change only through this repository.
# The queue build uses this repository's main branch so runner admission can
# restrict it to that trusted workflow, independently of a PR's workflow edits.
#
# Usage: sh/pins.sh
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# Each `uses:` as "line<TAB>ref<TAB>comment": a reusable workflow, a workflow
# step, or a composite action's step.
# shellcheck disable=SC2016 # A yq program, not a shell expansion.
uses='(.jobs[]?.uses, .jobs[]?.steps[]?.uses, .runs.steps[]?.uses)
    | select(. != null)
    | (line | tostring) + "\t" + . + "\t" + line_comment'

status=0 count=0
while IFS= read -r -d '' file; do
    if ! refs=$(yq "$uses" "$file"); then
        echo "sh/pins.sh: cannot read $file" >&2
        exit 2
    fi
    while IFS=$'\t' read -r line ref comment; do
        [[ -n "$ref" && "$ref" != ./* ]] || continue
        [[ "$ref" != kixel-ai/rind/.github/workflows/queue-build.yml@main ]] || continue
        count=$((count + 1))
        if [[ ! "$ref" =~ ^[^@]+@[0-9a-f]{40}$ ]]; then
            echo "$file:$line: $ref is not pinned to a full commit SHA" >&2
            status=1
        elif [[ -z "$comment" ]]; then
            echo "$file:$line: $ref has no trailing version comment" >&2
            status=1
        fi
    done <<<"$refs"
done < <(find .github/workflows .github/actions \
    \( -path '.github/workflows/*' -o -name 'action.y*ml' \) \
    \( -name '*.yml' -o -name '*.yaml' \) -type f -print0 | sort -z)

if ((status)); then
    echo "pin each to a commit SHA: uses: owner/repo@<sha> # vX.Y.Z" >&2
    exit 1
fi
echo "all $count third-party actions are pinned"
