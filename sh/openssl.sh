#!/usr/bin/env bash
# Run OpenSSL's own `evp_test` on its X25519 and Ed25519 data with
# rind-openssl loaded and preferred, as its README's configuration does;
# `-provider rind` fails the run if rind does not load, instead of letting
# the default provider pass it.
#
# Usage: nix develop .#openssl --command sh/openssl.sh
# That dev shell builds `evp_test` from the source of the OpenSSL the default
# one has. Each stanza that asks Ed25519's `instance` for Ed25519ctx or
# Ed25519ph is left out, since rind backs only pure Ed25519 and refuses
# them; OpenSSL's ED25519ctx and ED25519ph signature algorithms stay the
# default provider's, so their stanzas run.
set -euo pipefail

: "${OPENSSL_EVP_TEST:?run in the .#openssl dev shell}"

cd "$(git rev-parse --show-toplevel)"

# The library this build made, wherever a configured target puts it.
library=$(cargo build -p rind-openssl --locked --message-format=json |
    jq -r 'select(.reason == "compiler-artifact" and (.target.kind | index("cdylib"))) | .filenames[] | select(test("\\.(so|dylib)$"))')
if [[ -z "$library" || "$library" == *$'\n'* ]]; then
    echo "error: expected one rind-openssl library from the build, got: ${library:-none}" >&2
    exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Escaped, as `openssl.cnf` reads a `#` as a comment and a `$` as a variable.
module=$(printf '%s' "$library" | sed 's|[^A-Za-z0-9/._-]|\\&|g')
MODULE="module = $module" awk '/^module = /{ print ENVIRON["MODULE"]; next } { print }' \
    rind-openssl/openssl.cnf >"$work/openssl.cnf"
grep -qxF "module = $module" "$work/openssl.cnf"

skipped=0
for file in "$OPENSSL_EVP_TEST"/share/evp_test/*.txt; do
    # Stanzas are paragraphs.
    awk 'BEGIN { RS = ""; ORS = "\n\n" } !/Ctrl = instance:Ed25519(ctx|ph)/' "$file" >"$work/${file##*/}"
    count() { awk 'BEGIN { RS = "" } END { print NR }' "$1"; }
    skipped=$((skipped + $(count "$file") - $(count "$work/${file##*/}")))
done
echo "Left out $skipped stanzas for Ed25519ctx or Ed25519ph through Ed25519's instance." >&2

"$OPENSSL_EVP_TEST/bin/evp_test" -config "$work/openssl.cnf" -provider rind "$work"/evppkey_*.txt
