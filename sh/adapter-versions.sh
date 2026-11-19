#!/usr/bin/env bash
# Verify each published rind-<consumer> adapter's version begins with the
# breaking part of the upstream version it adapts: major.minor below 1.0, major
# from 1.0 on. The upstream version is the adapter's requirement on the
# dependency named after it, or `package.metadata.rind.upstream` for an adapter
# that implements its upstream's API without depending on it, as rind-ring does.
#
# Usage: sh/adapter-versions.sh
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

# shellcheck disable=SC2016 # A jq program, not a shell expansion.
program='
# The semver-breaking part of a version or caret requirement, or null when it
# names no such part.
def breaking:
    (ltrimstr("^") | split(".")) as $v
    | if ($v | any(test("^[0-9]+$") | not)) then null
      elif $v[0] != "0" then $v[0]
      elif ($v | length) >= 2 then "\($v[0]).\($v[1])"
      else null end;
def norm: gsub("-"; "_");

.packages[]
| select((.name | startswith("rind-")) and .publish == null)
| (.name | ltrimstr("rind-") | norm) as $upstream
| ([.dependencies[] | select(.kind == null and ((.rename // .name) | norm) == $upstream) | .req]) as $reqs
| (.metadata.rind.upstream // null) as $declared
| (if $declared != null then $declared elif ($reqs | length) == 1 then $reqs[0] else null end) as $req
| if $req == null then
    "\(.name): needs one dependency named \($upstream), or package.metadata.rind.upstream"
  elif ($req | breaking) == null then
    "\(.name): upstream requirement \($req) is not a caret requirement naming major.minor, or major from 1.0 on"
  elif (.version | breaking) != ($req | breaking) then
    "\(.name) \(.version): version must begin with \($req | breaking), the breaking part of \($upstream) \($req)"
  else empty end
'

errors=$(cargo metadata --no-deps --format-version 1 | jq -r "$program")
if [[ -n "$errors" ]]; then
    echo "$errors" >&2
    exit 1
fi
