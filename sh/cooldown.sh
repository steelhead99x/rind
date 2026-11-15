#!/usr/bin/env bash
# List each crates.io release that Cargo.lock gains over a base ref and that is
# younger than the 7-day cooldown .github/dependabot.yml sets, and fail if there
# is one. Dependabot's lockfile updates can take such releases; see UPSTREAM.md,
# "Dependabot's Cargo lockfile updates skip its cooldown".
#
# Usage: sh/cooldown.sh <base-ref>
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

base=${1:?usage: sh/cooldown.sh <base-ref>}
days=7

# Each crates.io package in the lockfile on stdin, as "name version".
packages() {
    awk -F' = ' '
        $1 == "name" { name = $2 }
        $1 == "version" { version = $2 }
        $1 == "source" && $2 == "\"registry+https://github.com/rust-lang/crates.io-index\"" { print name, version }
    ' | tr -d '"' | sort -u
}

old=$(git show "$base:Cargo.lock" | packages)
new=$(packages <Cargo.lock)
cutoff=$(($(date +%s) - days * 86400))

status=0
while read -r name version; do
    [[ -n "$name" ]] || continue
    # The sparse index's layout: https://doc.rust-lang.org/cargo/reference/registry-index.html#index-files
    lower=${name,,}
    case ${#lower} in
        1 | 2) path=${#lower}/$lower ;;
        3) path=3/${lower:0:1}/$lower ;;
        *) path=${lower:0:2}/${lower:2:2}/$lower ;;
    esac
    published=$(curl -fsS "https://index.crates.io/$path" | jq -nr --arg name "$name" --arg version "$version" '
        [inputs | select(.vers == $version) | .pubtime | strings]
        | if length == 1 then "\(.[0] | fromdateiso8601) \(.[0])"
          else error("no publish time for \($name) \($version)") end')
    read -r epoch time <<<"$published"
    if ((epoch > cutoff)); then
        echo "$name $version, published $time"
        status=1
    fi
done < <(comm -13 <(printf '%s\n' "$old") <(printf '%s\n' "$new"))

exit "$status"
