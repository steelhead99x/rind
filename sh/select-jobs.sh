#!/usr/bin/env bash
# Pick the jobs, and the matrix rows, that a dispatched workflow run named in
# its `jobs` input, for the workflow's `select` job to hand the rest.
#
# Usage: sh/select-jobs.sh WORKFLOW 'ENTRY...'
#        sh/select-jobs.sh --check
#
# Each ENTRY is a job ID, which runs the job whole, or `job:value,...`, which
# runs only the rows of its matrix that take each named value on that value's
# axis, as `armv7:no-neon,debug` runs armv7's one debug no-NEON row. Entries
# are separated by single spaces and follow the workflow's job order, and a
# job's values its matrix's order, so one selection has one spelling, and one
# concurrency group. Anything else, such as a typo, fails, so a dispatch never
# quietly runs nothing.
#
# It prints, for $GITHUB_OUTPUT, `jobs=`, a JSON array of the named job IDs,
# and `exclude=`, a JSON object of each filtered job's matrix exclusions. A
# job checks the first in its `if:` and takes the second as its matrix's
# `exclude`; only a matrix of literal axes, without `include`, takes a filter,
# since GitHub adds back an excluded row that an `include` names.
#
# `--check`, which `just ci` runs, fails a job of a workflow taking a `jobs`
# input that would run whatever the selection says, or that lacks the
# `!cancelled()` that keeps GitHub from skipping it whenever `select` skips.
set -euo pipefail

usage="usage: sh/select-jobs.sh WORKFLOW 'ENTRY...' | --check"
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [[ "${1:-}" == --check ]]; then
    [[ $# -eq 1 ]] || {
        echo "$usage" >&2
        exit 2
    }
    errors=0
    for file in .github/workflows/*.yml; do
        [[ $(yq '.on.workflow_dispatch.inputs | has("jobs")' "$file") == true ]] || continue
        # shellcheck disable=SC2016 # A jq program, not a shell expansion.
        problems=$(yq -o=json . "$file" | jq -r '
            if .jobs | has("select") | not then "has no select job"
            else .jobs | to_entries[] | select(.key != "select")
                | .key as $id | .value
                | if ([.needs // []] | flatten | index("select")) == null then "\($id) does not need select"
                  elif (.if // "" | tostring | contains("needs.select.outputs.jobs") and contains("'\''\($id)'\''") | not)
                  then "\($id) does not check needs.select.outputs.jobs for itself in its if:"
                  elif (.if | tostring | test("!\\s*cancelled\\(\\)") | not)
                  then "\($id) skips whenever select does: its if: needs !cancelled()"
                  else empty end
            end')
        while IFS= read -r problem; do
            [[ -z "$problem" ]] || {
                echo "error: $file: $problem" >&2
                errors=1
            }
        done <<<"$problems"
    done
    exit "$errors"
fi
[[ $# -eq 2 ]] || {
    echo "$usage" >&2
    exit 2
}

# shellcheck disable=SC2016 # A jq program, not a shell expansion.
yq -o=json . "$1" | jq -r --arg entries "$2" '
    def fail($msg): "sh/select-jobs.sh: \($msg)\n" | halt_error(1);
    (.jobs | keys_unsorted - ["select"]) as $ids
    | .jobs as $jobs
    | ($entries | [splits("\\s+") | select(. != "")]) as $split
    | if $split == [] then fail("names no job")
      elif $split | join(" ") != $entries then fail("separate entries with single spaces, as the concurrency group reads them")
      else . end
    | $split as $entries
    | [$entries[] | capture("^(?<id>[^:]+)(:(?<values>.+))?$") // fail("cannot read \(.)")
        | .values |= (if . == null then [] else split(",") end)
        | . as {$id}
        | .index = ($ids | index($id) // fail("no job \($id); jobs: \($ids | join(" "))"))] as $picks
    | if [$picks[].index] != ([$picks[].index] | unique) then
        fail("name each job once, in the workflow order: \($ids | join(" "))")
      else . end
    | {
        jobs: [$picks[].id],
        exclude: [$picks[] | select(.values != []) | .id as $id | .values as $values
            | $jobs[$id].strategy.matrix as $matrix
            | if ($matrix.exclude // "" | tostring | contains("needs.select.outputs.exclude") | not)
                or ($matrix | has("include")) then
                fail("\($id) takes no row filter: its matrix needs literal axes, no include, and the select job'\''s exclude")
              else . end
            # Every value of every literal axis, in matrix order.
            | [$matrix | to_entries[] | select(.key != "exclude" and (.value | type) == "array")
                | .key as $axis | .value[] | {axis: $axis, value: ., name: tostring}] as $all
            | [$values[] as $name | [$all | to_entries[] | select(.value.name == $name)]
                | if length == 1 then .[0] | {index: .key} + .value
                  elif length == 0 then fail("\($id) has no row value \($name); values: \([$all[].name] | join(" "))")
                  else fail("\($id): \($name) names more than one axis") end] as $named
            | if [$named[].index] != ([$named[].index] | unique) then
                fail("name each of \($id)'\''s values once, in its matrix order: \([$all[].name] | join(" "))")
              else . end
            | ([$named[].axis] | unique) as $axes
            | if [$axes[] as $a | [$all[] | select(.axis == $a)] - [$named[] | del(.index)]] | any(. == []) then
                fail("\($id): naming every value of an axis is naming none")
              else . end
            | {key: $id, value: [$all[] | select(.axis as $a | $axes | index($a))
                | select(.name as $n | [$named[].name] | index($n) | not) | {(.axis): .value}]}
        ] | from_entries
      }
    | "jobs=\(.jobs | tojson)", "exclude=\(.exclude | tojson)"'
