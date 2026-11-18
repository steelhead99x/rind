#!/usr/bin/env bash
# Load a built rind-openssl LIBRARY into the `openssl` on PATH through the
# README's configuration, and check each algorithm rind registers against
# OpenSSL's default provider: an Ed25519 signature made by one verifies under
# the other, and an X25519 exchange between a key of each agrees. rind makes
# its keys with `-propquery provider=rind`, which fails rather than fall back
# to the default provider; signing and exchange take the configuration's
# preference for rind, as a deployment does (a mandatory query there would
# also bar the default provider's file loader). The crate's provider tests
# check which provider ran each operation. The release runs this on each
# library before attaching it, against the OpenSSL its runner's system ships.
#
# Usage: sh/openssl-smoke.sh LIBRARY
set -euo pipefail

library=${1:?usage: sh/openssl-smoke.sh LIBRARY}
[[ -f "$library" ]] || { echo "error: no library at $library" >&2; exit 1; }
library=$(cd "$(dirname "$library")" && pwd)/$(basename "$library")

cd "$(git rev-parse --show-toplevel)"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Escaped, as `openssl.cnf` reads a `#` as a comment and a `$` as a variable.
module=$(printf '%s' "$library" | sed 's|[^A-Za-z0-9/._-]|\\&|g')
MODULE="module = $module" awk '/^module = /{ print ENVIRON["MODULE"]; next } { print }' \
    rind-openssl/openssl.cnf >"$work/documented.cnf"
grep -qxF "module = $module" "$work/documented.cnf"
# The default provider alone, as OpenSSL runs with no configuration.
: >"$work/default.cnf"

rind() { OPENSSL_CONF="$work/documented.cnf" openssl "$@"; }
default() { OPENSSL_CONF="$work/default.cnf" openssl "$@"; }

openssl version
# OpenSSL carries on without a provider it cannot load, so check it loaded.
rind list -providers | tee "$work/providers"
grep -qE '^ +rind$' "$work/providers" || { echo "error: OpenSSL did not load rind" >&2; exit 1; }

head -c 1000 /dev/urandom >"$work/message"
for maker in rind default; do
    for checker in rind default; do
        query=()
        [[ "$maker" == rind ]] && query=(-propquery provider=rind)
        "$maker" genpkey -algorithm ED25519 ${query[@]+"${query[@]}"} -out "$work/ed.pem"
        "$maker" pkeyutl -sign -rawin -inkey "$work/ed.pem" -in "$work/message" -out "$work/sig"
        "$checker" pkey -in "$work/ed.pem" -pubout -out "$work/ed.pub"
        "$checker" pkeyutl -verify -rawin -pubin -inkey "$work/ed.pub" \
            -in "$work/message" -sigfile "$work/sig"
    done
done

rind genpkey -algorithm X25519 -propquery provider=rind -out "$work/a.pem"
default genpkey -algorithm X25519 -out "$work/b.pem"
default pkey -in "$work/a.pem" -pubout -out "$work/a.pub"
default pkey -in "$work/b.pem" -pubout -out "$work/b.pub"
rind pkeyutl -derive -inkey "$work/a.pem" -peerkey "$work/b.pub" -out "$work/ab"
default pkeyutl -derive -inkey "$work/b.pem" -peerkey "$work/a.pub" -out "$work/ba"
cmp "$work/ab" "$work/ba"
[[ $(wc -c <"$work/ab") -eq 32 ]]

echo "rind-openssl: $library passed against $(openssl version)"
