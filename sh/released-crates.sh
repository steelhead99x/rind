#!/usr/bin/env bash
# Print, as JSON, the crates crates.io holds that were published from the
# commits main gained since BEFORE (HEAD alone without it), grouped by that
# commit: [{"commit": SHA, "crates": [{"name": NAME, "version": VERSION}]}].
# Each published workspace crate, at the version a commit's Cargo.lock gives
# it, counts when crates.io has that version and the commit `cargo package`
# recorded in it is this one. So a rerun after a partial release finds what
# the first run published, even where release-plz's tag or GitHub Release
# failed, and a version published from an earlier commit is left out.
#
# Usage: sh/released-crates.sh [BEFORE]
set -euo pipefail

before=${1:-}
cd "$(git rev-parse --show-toplevel)"

range=(--max-count=1 HEAD)
[[ -z "$before" ]] || range=("$before..HEAD")

published=$(cargo metadata --format-version 1 --no-deps --locked |
    jq -c '[.packages[] | select(.publish != []) | .name]')

crate=$(mktemp)
trap 'rm -f "$crate"' EXIT

for commit in $(git rev-list --first-parent "${range[@]}"); do
    # Workspace members are the lockfile's packages without a source.
    git show "$commit:Cargo.lock" | yq -p toml -o json '.package' |
        jq -r --argjson published "$published" \
            '.[] | select(has("source") | not) | select(.name | IN($published[])) | "\(.name) \(.version)"' |
        while read -r name version; do
            status=$(curl --silent --show-error --output "$crate" --write-out '%{http_code}' \
                "https://static.crates.io/crates/$name/$name-$version.crate")
            case "$status" in
                200) ;;
                # Not published.
                404) continue ;;
                *)
                    echo "error: crates.io answered $status for $name $version" >&2
                    exit 1
                    ;;
            esac
            sha1=$(tar -xzOf "$crate" "$name-$version/.cargo_vcs_info.json" | jq -r .git.sha1)
            [[ "$sha1" != "$commit" ]] || jq -nc --arg commit "$commit" --arg name "$name" --arg version "$version" \
                '{commit: $commit, name: $name, version: $version}'
        done
done | jq -sc 'group_by(.commit) | map({commit: .[0].commit, crates: map({name, version})})'
