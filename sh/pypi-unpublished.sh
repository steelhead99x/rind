#!/usr/bin/env bash
# Print the git ref to build PACKAGE from if its current version is released
# and PyPI does not have all of it yet, or nothing.
#
# Usage: sh/pypi-unpublished.sh pyrind|pyrind-cryptography
# release-plz tags rind-python when a release PR lands, since it never goes
# to crates.io, so pyrind builds from that tag. release-plz does not know
# pyrind-cryptography, whose version is bumped by hand in
# rind-python/cryptography, so any version PyPI lacks is released and builds
# from HEAD, once release-plz releases a pyrind it requires.
# release.yml publishes what this names, and retries on a later push if
# publishing failed.
set -euo pipefail

package=${1:?usage: sh/pypi-unpublished.sh pyrind|pyrind-cryptography}

cd "$(git rev-parse --show-toplevel)"

pyrind=$(cargo metadata --format-version 1 --no-deps --locked |
    jq -r '.packages[] | select(.name == "rind-python") | .version')
# Exit status 2 means no such tag: this pyrind is unreleased.
tagged=0
git ls-remote --exit-code --tags origin "refs/tags/rind-python-v$pyrind" >/dev/null || tagged=$?
case "$tagged" in
    0 | 2) ;;
    *) exit "$tagged" ;;
esac

case "$package" in
    pyrind)
        [ "$tagged" = 0 ] || exit 0
        version=$pyrind
        ref="rind-python-v$version"
        ;;
    pyrind-cryptography)
        # flit reads the version from __version__.
        version=$(sed -n 's/^__version__ = "\(.*\)"$/\1/p' rind-python/cryptography/pyrind_cryptography/__init__.py)
        if [ -z "$version" ]; then
            echo "error: no __version__ in pyrind_cryptography" >&2
            exit 1
        fi
        # release.yml installs it with this commit's pyrind, so it waits for
        # release-plz to release a pyrind its requirement takes, rather than
        # fail every push to main until then. One past pyrind still builds,
        # so that install fails loudly without stopping pyrind's own release.
        pin=$(python3 rind-python/cryptography/pin.py "$pyrind")
        if [ "$pin" = below ] || [ "$tagged" != 0 ]; then
            exit 0
        fi
        ref=$(git rev-parse HEAD)
        ;;
    *)
        echo "error: unknown package $package" >&2
        exit 1
        ;;
esac

# twine uploads the wheels before the sdist, so a version whose sdist is on
# PyPI is complete; one without it may be partly uploaded, and release.yml
# skips the files already there.
json=$(mktemp)
trap 'rm -f "$json"' EXIT
status=$(curl --silent --output "$json" --write-out '%{http_code}' "https://pypi.org/pypi/$package/$version/json")
case "$status" in
    200)
        if ! jq -e '.urls | any(.packagetype == "sdist")' "$json" >/dev/null; then
            echo "$ref"
        fi
        ;;
    404) echo "$ref" ;;
    *)
        echo "error: PyPI answered $status for $package $version" >&2
        exit 1
        ;;
esac
