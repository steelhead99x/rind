#!/usr/bin/env bash
# Run OpenSSL's own `evp_test` on its X25519 and Ed25519 data with
# rind-openssl loaded and preferred, as its README's configuration does, and
# on its ECDSA and ECDH data with `ec = 1` added; `-provider rind` fails the
# run if rind does not load, instead of letting the default provider pass it.
#
# Usage: nix develop .#openssl --command sh/openssl.sh
# That dev shell builds `evp_test` from the source of the OpenSSL the default
# one has. Each stanza that asks Ed25519's `instance` for Ed25519ctx or
# Ed25519ph is left out, since rind backs only pure Ed25519 and refuses
# them; OpenSSL's ED25519ctx and ED25519ph signature algorithms stay the
# default provider's, so their stanzas run.
#
# The EC data runs with `ec = 1`, less each stanza that asks for what rind
# refuses, which are counted: a signature or verification over a digest the
# caller made (`Sign`, `Verify`), a digest other than SHA-256, SHA-384, and
# SHA-512, a curve other than P-256, P-384, and P-521 (by the name of each
# key the stanza uses, or its `group`), and explicit curve parameters.
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

# The same, with the NIST curves on.
sed 's/^# ec = 1$/ec = 1/' "$work/openssl.cnf" >"$work/openssl-ec.cnf"
grep -qxF 'ec = 1' "$work/openssl-ec.cnf"

mkdir "$work/ecx" "$work/ec"
count() { awk 'BEGIN { RS = "" } END { print NR }' "$1"; }

skipped=0
for file in "$OPENSSL_EVP_TEST"/share/evp_test/evppkey_*ecx*.txt; do
    # Stanzas are paragraphs.
    awk 'BEGIN { RS = ""; ORS = "\n\n" } !/Ctrl = instance:Ed25519(ctx|ph)/' "$file" >"$work/ecx/${file##*/}"
    skipped=$((skipped + $(count "$file") - $(count "$work/ecx/${file##*/}")))
done
echo "Left out $skipped stanzas for Ed25519ctx or Ed25519ph through Ed25519's instance." >&2

"$OPENSSL_EVP_TEST/bin/evp_test" -config "$work/openssl.cnf" -provider rind "$work"/ecx/evppkey_*.txt

# A stanza stays unless it runs a bare-digest operation, names a digest or a
# group rind does not back, or uses a key whose name is not one of the three
# curves'. Keys are named for their curves, as `ALICE_secp384r1_PUB` is.
skipped=0
for file in "$OPENSSL_EVP_TEST"/share/evp_test/evppkey_{ecc,ecdh,ecdsa,ecdsa_sigalg,mismatch}.txt; do
    awk '
    BEGIN { RS = ""; ORS = "\n\n" }
    function refused(    lines, n, i, line, key, value, parts, m, j) {
        if ($0 ~ /(^|\n)(Sign|Verify|VerifyRecover) *=/) return 1
        n = split($0, lines, "\n")
        for (i = 1; i <= n; i++) {
            line = lines[i]
            if (line ~ /^Ctrl *= *digest:/) {
                if (line !~ /digest:SHA(2-)?(256|384|512) *$/) return 1
            }
            if (line ~ /^Ctrl *= *group:/ && line !~ /group:P-(256|384|521) *$/) return 1
            if (line ~ /^(Derive|PeerKey|DigestSign|DigestVerify|OneShotDigestVerify|PrivPubKeyPair) *=/) {
                value = line
                sub(/^[^=]*= */, "", value)
                m = split(value, parts, ":")
                for (j = 1; j <= m; j++) {
                    if (toupper(parts[j]) ~ /EXPLICIT/) return 1
                    if (toupper(parts[j]) !~ /(^|[_-])(P-(256|384|521)|SECP(256|384|521)R1|PRIME256V1)([_-]|$)/) return 1
                }
            }
        }
        return 0
    }
    !refused()' "$file" >"$work/ec/${file##*/}"
    skipped=$((skipped + $(count "$file") - $(count "$work/ec/${file##*/}")))
done
echo "Left out $skipped stanzas rind refuses: bare digests, other digests, other curves." >&2

"$OPENSSL_EVP_TEST/bin/evp_test" -config "$work/openssl-ec.cnf" -provider rind "$work"/ec/evppkey_*.txt
