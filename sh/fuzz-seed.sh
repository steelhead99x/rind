#!/usr/bin/env bash
# Seed the fuzz corpora that take encoded input: `keys` from the test keys,
# each seed the loader's selector byte (see fuzz/fuzzer/keys.rs) followed by a
# key, and `verify` from Wycheproof's signatures (see fuzz/fuzzer/verify.rs).
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."

corpus=fuzz/corpus/keys
mkdir -p "$corpus"

ecdsa=rind/src/high/ecdsa
rsa=rind/src/high/rsa
asn1=rind/src/high/asn1/testdata
ring=rind-ring/tests/ring

# seed SELECTOR FILE...
seed() {
    local selector=$1
    shift
    for file in "$@"; do
        { printf %b "\\x$(printf %02x "$selector")"; cat "$file"; } >"$corpus/$selector-$(basename "$file")"
    done
}

# pkcs8_v2 SELECTOR FILE FIELD: the PKCS#8 v1 FILE as version 2, ending in
# the public key FIELD, a file of its DER, or none if FIELD is empty.
pkcs8_v2() {
    local selector=$1 file=$2 field=$3 header len
    # A long-form length of one or two bytes follows the tag.
    header=$((2 + 0x$(od -An -tx1 -j1 -N1 "$file" | tr -d ' ') - 0x80))
    len=$(($(wc -c <"$file") - header + $(wc -c <"$field")))
    {
        printf %b "\\x$(printf %02x "$selector")\\x30"
        if ((len < 0x100)); then
            printf %b "\\x81\\x$(printf %02x "$len")"
        else
            printf %b "\\x82\\x$(printf %02x $((len >> 8)))\\x$(printf %02x $((len & 0xff)))"
        fi
        printf '\x02\x01\x01'
        tail -c +$((header + 4)) "$file"
        cat "$field"
    } >"$corpus/$selector-v2-$(basename "$file")"
}

seed 0 "$ecdsa/secp256r1.pkcs8.der" "$asn1/nistp256-p8.bin"
seed 1 "$ecdsa/secp384r1.pkcs8.der"
seed 2 "$ecdsa/secp521r1.pkcs8.der"
seed 3 "$ecdsa"/secp256r1*.der "$asn1/nistp256-sec1.bin"
seed 4 "$ecdsa/secp384r1.der"
seed 5 "$ecdsa/secp521r1.der"
seed 9 "$ring/ecdsa_test_public_key_p256.der" "$asn1/spki-ec-nistp256.bin"
seed 12 "$rsa"/*.pkcs8.der
seed 13 "$rsa"/rsa{2048,2048-q-above-p,3072,4096,6144,8192}.der "$asn1/rsaprivatekey-1k.bin" \
    "$ring/signature_rsa_example_private_key.der"
for selector in 14 15 16; do
    seed "$selector" "$rsa"/*.pub.der "$asn1/rsapublickey-1k.bin" "$asn1/spki-rsa-2k.bin" \
        "$ring/rsa_test_public_key_2048.der"
done
seed 20 "$asn1"/ed25519-p8v*.bin
seed 22 "$ring/ed25519_test_public_key.der"
# An all-zero ML-KEM-768 encapsulation key passes the modulus check.
{ printf '\x17'; head -c 1184 /dev/zero; } >"$corpus/23-zero"
# Agreement scalars of each curve's length, all 0x01 bytes, which each
# curve takes, and an X25519 PKCS#8 v1 key of those bytes.
for selector_len in 24:32 25:32 26:48 27:66; do
    { printf %b "\\x$(printf %02x "${selector_len%:*}")"; head -c "${selector_len#*:}" /dev/zero | tr '\0' '\1'; } \
        >"$corpus/${selector_len%:*}-ones"
done
{ printf '\x1c\x30\x2e\x02\x01\x00\x30\x05\x06\x03\x2b\x65\x6e\x04\x22\x04\x20'; head -c 32 /dev/zero | tr '\0' '\1'; } \
    >"$corpus/28-x25519-p8v1"
# An Ed25519 seed of 0x01 bytes.
{ printf '\x2a'; head -c 32 /dev/zero | tr '\0' '\1'; } >"$corpus/42-ones"
seed 33 "$asn1/spki-rsa-2k.bin"

# unhex: decode stdin's hex, failing on odd length or a non-hex digit, which
# `xxd -r -p` would silently drop.
unhex() {
    local hex
    hex=$(cat)
    [[ $hex =~ ^([0-9A-Fa-f]{2})*$ ]] || { echo "fuzz-seed: malformed hex: $hex" >&2; exit 1; }
    xxd -r -p <<<"$hex"
}

# wycheproof SELECTOR FILE JQ: a seed for each distinct key JQ finds in the
# Wycheproof FILE, in hex: the selector byte, then the key.
wycheproof() {
    local selector=$1 file=$2 filter=$3 key
    jq -r "[$filter] | unique[]" "thirdparty/wycheproof/testvectors_v1/$file" | while read -r key; do
        printf %02x%s "$selector" "$key" | unhex >"$corpus/$selector-${file%_test.json}-${key: -16}"
    done
}

# Each curve's points, bare and in a `SubjectPublicKeyInfo`, compressed among
# them, and Ed25519's public keys.
wycheproof 29 ecdh_secp256r1_test.json '.testGroups[].tests[].public'
wycheproof 30 ecdh_secp384r1_test.json '.testGroups[].tests[].public'
wycheproof 31 ecdh_secp521r1_test.json '.testGroups[].tests[].public'
wycheproof 32 ed25519_test.json '.testGroups[].publicKeyDer'
wycheproof 34 x25519_test.json '.testGroups[].tests[].public'
wycheproof 35 ecdh_secp256r1_ecpoint_test.json '.testGroups[].tests[].public'
wycheproof 36 ecdh_secp384r1_ecpoint_test.json '.testGroups[].tests[].public'
wycheproof 37 ecdh_secp521r1_ecpoint_test.json '.testGroups[].tests[].public'
wycheproof 38 x25519_asn_test.json '.testGroups[].tests[].public'
wycheproof 39 ecdh_secp256r1_test.json '.testGroups[].tests[].public'
wycheproof 40 ecdh_secp384r1_test.json '.testGroups[].tests[].public'
wycheproof 41 ecdh_secp521r1_test.json '.testGroups[].tests[].public'
# ML-DSA's private keys as PKCS#8 and as seeds, and its public keys, raw and
# in a `SubjectPublicKeyInfo`.
for set in 0:44 1:65 2:87; do
    wycheproof $((43 + ${set%:*})) "mldsa_${set#*:}_sign_seed_test.json" '.testGroups[].privateKeyPkcs8 // empty'
    wycheproof $((46 + ${set%:*})) "mldsa_${set#*:}_sign_seed_test.json" '.testGroups[].privateSeed // empty'
    wycheproof $((49 + ${set%:*})) "mldsa_${set#*:}_verify_test.json" '.testGroups[].publicKey // empty'
    wycheproof $((52 + ${set%:*})) "mldsa_${set#*:}_verify_test.json" '.testGroups[].publicKeyDer // empty'
done

# Version 2 documents, which the ECDSA and RSA loaders refuse: one with its
# public key, one with an empty one, and two without, which aws-lc-rs takes.
field=$(mktemp)
trap 'rm -f "$field"' EXIT
{ printf '\x81\x42\x00'; tail -c 65 "$ecdsa/secp256r1.der"; } >"$field"
pkcs8_v2 0 "$ecdsa/secp256r1.pkcs8.der" "$field"
printf '\x81\x01\x00' >"$field"
pkcs8_v2 12 "$rsa/rsa2048.pkcs8.der" "$field"
: >"$field"
pkcs8_v2 2 "$ecdsa/secp521r1.pkcs8.der" "$field"
pkcs8_v2 12 "$rsa/rsa3072.pkcs8.der" "$field"

corpus=fuzz/corpus/verify
mkdir -p "$corpus"
wycheproof=thirdparty/wycheproof/testvectors_v1

# verify SELECTOR FILE [SHA]: a seed for each test in the Wycheproof FILE, or
# in its groups hashing with SHA: the selector byte, then the key and the
# signature, each after its 16-bit length, then the message.
verify() {
    local selector=$1 file=$2 sha=${3:-} id seed
    jq -r --arg selector "$(printf %02x "$selector")" --arg sha "$sha" '
        def hex16: (length / 2) as $n
            | [4096, 256, 16, 1] | map(($n / . | floor) % 16 | "0123456789abcdef"[.:. + 1]) | join("");
        .testGroups[] | select($sha == "" or .sha == $sha)
        | ((.publicKey | if type == "string" then . else .uncompressed // .pk end) // .publicKeyAsn // .keyAsn) as $key
        | .tests[]
        | "\(.tcId) \($selector + ($key | hex16) + $key + (.sig | hex16) + .sig + .msg)"
    ' "$wycheproof/$file" | while read -r id seed; do
        unhex <<<"$seed" >"$corpus/$selector-${file%_test.json}${sha:+-$sha}-$id"
    done
}

verify 0 ed25519_test.json
verify 1 ecdsa_secp256r1_sha256_test.json
verify 3 ecdsa_secp256r1_sha512_test.json
verify 4 ecdsa_secp384r1_sha256_test.json
verify 5 ecdsa_secp384r1_sha384_test.json
verify 6 ecdsa_secp384r1_sha512_test.json
verify 9 ecdsa_secp521r1_sha512_test.json
verify 10 ecdsa_secp256r1_sha256_p1363_test.json
verify 11 ecdsa_secp384r1_sha384_p1363_test.json
verify 12 ecdsa_secp521r1_sha512_p1363_test.json
for bits in 2048 3072 4096 8192; do
    verify 13 "rsa_signature_${bits}_sha256_test.json"
    verify 15 "rsa_signature_${bits}_sha512_test.json"
done
for bits in 2048 4096 8192; do
    verify 14 "rsa_signature_${bits}_sha384_test.json"
done
verify 16 rsa_pss_2048_sha256_mgf1_32_test.json
verify 16 rsa_pss_4096_sha256_mgf1_32_test.json
verify 17 rsa_pss_2048_sha384_mgf1_48_test.json
verify 17 rsa_pss_4096_sha384_mgf1_48_test.json
verify 18 rsa_pss_4096_sha512_mgf1_64_test.json
verify 19 rsa_pkcs1_2048_sig_gen_test.json SHA-1
verify 20 rsa_pkcs1_1024_sig_gen_test.json SHA-1
verify 21 rsa_pkcs1_1024_sig_gen_test.json SHA-256
verify 23 rsa_signature_3072_sha384_test.json
verify 24 rsa_pss_2048_sha256_mgf1_0_test.json
verify 25 rsa_pss_4096_sha512_mgf1_64_test.json
verify 26 rsa_pss_2048_sha256_mgf1_0_test.json
verify 26 rsa_pss_2048_sha256_mgf1_32_test.json
verify 26 rsa_pss_misc_test.json SHA-256
verify 27 rsa_pss_2048_sha384_mgf1_48_test.json
verify 27 rsa_pss_misc_test.json SHA-384
verify 28 rsa_pss_4096_sha512_mgf1_32_test.json
verify 28 rsa_pss_4096_sha512_mgf1_64_test.json
verify 28 rsa_pss_misc_test.json SHA-512
verify 29 mldsa_44_verify_test.json
verify 30 mldsa_65_verify_test.json
verify 31 mldsa_87_verify_test.json
