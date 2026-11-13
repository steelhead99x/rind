#!/usr/bin/env bash
# Pin the libraries in LIB_DIR, as sh/dart-library.sh names them, in the
# package sh/dart-package.sh staged: hook/prebuilt.json maps each target to
# its download from the package version's GitHub release, its length, and its
# SHA-256, which the build hook checks.
#
# Usage: sh/dart-prebuilt.sh PACKAGE_DIR LIB_DIR
set -euo pipefail

usage="usage: sh/dart-prebuilt.sh PACKAGE_DIR LIB_DIR"
package=${1:?$usage}
libs=${2:?$usage}
version=$(yq .version "$package/pubspec.yaml")
release=https://github.com/kixel-ai/rind/releases/download/rind-dart-v$version

shopt -s nullglob
files=("$libs"/rind_dart-*)
[[ ${#files[@]} -gt 0 ]] || { echo "error: $libs holds no libraries" >&2; exit 1; }

pins='{}'
for path in "${files[@]}"; do
    name=$(basename "$path")
    target=${name#rind_dart-}
    target=${target%.*}
    sha256=$(shasum -a 256 "$path" | cut -d ' ' -f 1)
    pins=$(jq --arg target "$target" --arg url "$release/$name" \
        --arg sha256 "$sha256" --argjson size "$(wc -c <"$path")" \
        '.[$target] = {url: $url, size: $size, sha256: $sha256}' <<<"$pins")
done
printf '%s\n' "$pins" >"$package/hook/prebuilt.json"
