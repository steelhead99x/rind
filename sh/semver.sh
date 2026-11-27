#!/usr/bin/env bash
# Fail a branch that breaks the public API of a published crate it changed,
# unless it is marked breaking. cargo-semver-checks compares each crate's
# rustdoc at HEAD with the same crate at the branch's merge-base: crates.io's
# release is the wrong baseline, since main holds every breaking change a
# minor release batches.
#
# Usage: sh/semver.sh [BASE]
# rind below 1.0 may break only in a minor release, which a `!` marks: a
# commit subject between BASE and HEAD, or PR_TITLE, as in `feat(kem)!: ...`.
# A marked branch skips rind's check. An adapter's API is its upstream's, so a
# plain `!` does not excuse it: it breaks in the change that sets its version
# to its upstream's next breaking release, which cargo-semver-checks reads
# from the manifest, or in one marked with its name as the scope, such as
# `fix(rind-ring)!: ...`, which restores parity the patch release owes.
set -euo pipefail

usage="usage: sh/semver.sh [BASE]"
if [[ $# -gt 1 ]]; then
    echo "$usage" >&2
    exit 2
fi

cd "$(git rev-parse --show-toplevel)"
base=$(sh/changed.sh --merge-base "${1:-}")
changed=$(sh/changed.sh "$base")

# The crates that reach crates.io, which each sit in a directory of their name:
# `publish = false` gives the others an empty `publish` list.
published=$(cargo metadata --format-version 1 --no-deps --locked |
    jq -r '.packages[] | select(.publish == null) | .name')

subjects=$(git log --format=%s "$base..HEAD"; printf '%s\n' "${PR_TITLE:-}")
# A `!` whose scope names an adapter marks that adapter only.
marked() {
    if [[ "$1" == rind ]]; then
        local others
        others=$(grep -vE '^[a-z]+\((.*,)?rind-[^),]*(,.*)?\)!:' <<<"$subjects" || true)
        grep -qE '^[a-z]+(\([^)]*\))?!:' <<<"$others"
    else
        grep -qE "^[a-z]+\((.*,)?$1(,.*)?\)!:" <<<"$subjects"
    fi
}

status=0
for package in $published; do
    grep -q "^$package/" <<<"$changed" || continue
    # A crate new in this branch has no baseline to compare with.
    if ! git cat-file -e "$base:$package/Cargo.toml" 2>/dev/null; then
        echo "semver: $package is new; no baseline"
        continue
    fi
    if marked "$package"; then
        # release-plz proposes a breaking version for a break it finds at the
        # released one, which sh/adapter-versions.sh refuses: a parity fix sets
        # its patch version by hand.
        if [[ "$package" != rind ]]; then
            latest=$(git tag -l "$package-v*" --sort=-v:refname | head -n1)
            version=$(cargo metadata --format-version 1 --no-deps --locked |
                jq -r --arg p "$package" '.packages[] | select(.name == $p) | .version')
            released=${latest#"$package-v"}
            if [[ -n "$latest" && ("$released" == "$version" ||
                "$(printf '%s\n%s\n' "$released" "$version" | sort -V | tail -n1)" != "$version") ]]; then
                echo "semver: $package is marked breaking but $version is not newer than its latest release $released; set its next patch version" >&2
                status=1
                continue
            fi
        fi
        echo "semver: $package is marked breaking; skipping its check"
        continue
    fi
    args=(--package "$package" --baseline-rev "$base")
    # Below 1.0, a patch release adds API, so only a break is a finding. An
    # adapter's release type comes from its version: unbumped, cargo-semver-checks
    # assumes minor, and the one that sets the version to upstream's next
    # breaking release may break. admin/adapter-api holds the rest of an
    # adapter's API to its upstream's.
    [[ "$package" != rind ]] || args+=(--release-type minor)
    cargo semver-checks "${args[@]}" || status=1
done
exit "$status"
