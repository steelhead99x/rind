#!/usr/bin/env bash
# Restore the newest corpus artifact NAME that a fuzz.yml run on main saved
# into DIR, for the next run to start from. An artifact, not the Actions
# cache: the weekly runs are further apart than the 7 days the cache keeps an
# entry, and other workflows' caches evict it sooner. Without one, as on the
# first run, DIR starts empty and the seeds fill it.
#
# Usage: sh/fuzz-corpus.sh NAME DIR
# Needs GH_TOKEN with `actions: read` and GITHUB_REPOSITORY.
set -euo pipefail

usage="usage: sh/fuzz-corpus.sh NAME DIR"
name=${1:?$usage}
dir=${2:?$usage}
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY is required}"

mkdir -p "$dir"
# Only a scheduled or dispatched fuzz.yml run on main in this repository runs
# main's own workflow file, so only its artifacts are trusted. Matching on the
# artifact's branch alone would also take one from any workflow a fork's pull
# request ran from a branch named main.
repo_id=$(gh api "repos/$GITHUB_REPOSITORY" --jq .id)
runs=$(gh api "repos/$GITHUB_REPOSITORY/actions/workflows/fuzz.yml/runs?branch=main&per_page=100" --jq "
    .workflow_runs[]
    | select((.event == \"schedule\" or .event == \"workflow_dispatch\")
        and .head_repository.id == $repo_id)
    | .id")
for run in $runs; do
    found=$(gh api "repos/$GITHUB_REPOSITORY/actions/runs/$run/artifacts?name=$name" \
        --jq '[.artifacts[] | select(.expired | not)] | length')
    if [[ "$found" -gt 0 ]]; then
        gh run download "$run" --repo "$GITHUB_REPOSITORY" --name "$name" --dir "$dir"
        echo "restored $name from run $run: $(find "$dir" -type f | wc -l) inputs" >&2
        exit 0
    fi
done
echo "no saved corpus $name; starting empty" >&2
