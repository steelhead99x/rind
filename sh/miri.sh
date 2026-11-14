#!/usr/bin/env bash
# Run the portable backend's tests under Miri for TARGET, as `just miri`
# runs it in the dev shell's `miri` shell: x86_64-unknown-linux-gnu, with the
# backend forced, or s390x-unknown-linux-gnu, which is big-endian. Miri fails
# a test on undefined behavior, such as an invalid value left for a drop, a
# misaligned or out-of-bounds pointer, or a data race.
set -euo pipefail

target=${1:-}
if [[ -z "$target" ]]; then
    echo "usage: sh/miri.sh TARGET" >&2
    exit 1
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

unfetched=$(git submodule status -- thirdparty/cavp thirdparty/cctv thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
if [[ -n "$unfetched" ]]; then
    echo "error: test vectors not checked out; run: git submodule update --init ${unfetched//$'\n'/ }" >&2
    exit 1
fi

# Tests too slow for Miri that repeat what a kept test runs: vector sets and
# long loops over inputs, RSA private-key operations beyond one for each key
# type, and many scalar multiplications. Each primitive keeps a quicker test
# that reaches the same unsafe code and builds, uses, and drops its key types,
# and the native runs keep these.
slow=(
    aead::gcm::tests::cavp
    high::agreement::tests::agrees
    high::agreement::tests::cavp_ecdh
    high::agreement::tests::decompresses_points
    high::agreement::tests::loads_in_constant_time
    high::agreement::tests::round_trips
    high::agreement::tests::wycheproof_p256
    high::agreement::tests::wycheproof_p384
    high::agreement::tests::wycheproof_p521
    high::agreement::tests::wycheproof_x25519
    high::agreement::tests::wycheproof_x25519_pkcs8
    high::blind_rsa::tests::finalize_refuses_bad_replies
    high::blind_rsa::tests::rfc9474_vectors
    high::blind_rsa::tests::round_trip
    high::blind_rsa::tests::signatures_are_bound_to_their_variant
    high::blind_rsa::tests::stays_secret
    high::curve::tests::cavp_keypair
    high::digest::tests::cavp
    high::ecdsa::tests::aws_lc_sign
    high::ecdsa::tests::aws_lc_verify
    high::ecdsa::tests::cavp_sigver
    high::ecdsa::tests::digest_signing_matches_message_signing
    high::ecdsa::tests::rfc6979_p521_test_vectors
    high::ecdsa::tests::rfc6979_test_vectors
    high::ecdsa::tests::smoke_test_ecdsa_sign
    high::ecdsa::tests::smoke_test_loading_keys
    high::hmac::tests::cavp
    high::hmac_drbg::tests::cavp
    high::hpke::tests::derives_from_any_length
    high::hpke::tests::every_suite_round_trips
    high::hpke::tests::opens_compressed_enc
    high::hpke::tests::rfc9180
    high::hpke::tests::secret_decapsulation
    high::hpke::tests::wycheproof_decrypt
    high::hpke::tests::wycheproof_sequence
    high::kem::tests::boringssl
    high::kem::tests::cctv_accumulated
    high::kem::tests::cctv_modulus
    high::kem::tests::wycheproof_decaps
    high::kem::tests::wycheproof_encaps
    high::kem::tests::wycheproof_keygen
    high::oaep::tests::every_failure_is_the_same
    high::oaep::tests::round_trip
    high::oaep::tests::stays_secret
    high::rsa::tests::key_generation_known_answer
    high::rsa::tests::loads_d_above_lcm
    high::rsa::tests::loads_q_above_p
    high::rsa::tests::loads_unbalanced_primes
    high::rsa::tests::pairwise_key_formatting
    high::rsa::tests::pairwise_odd_size_sign_verify
    high::rsa::tests::pairwise_rsa2048_sign_verify
    high::rsa::tests::pairwise_rsa2048_sign_verify_pkcs8
    high::rsa::tests::pairwise_rsa2560_sign_verify
    high::rsa::tests::pairwise_rsa3072_sign_verify
    high::rsa::tests::pairwise_rsa4096_sign_verify
    high::rsa::tests::pairwise_rsa6144_sign_verify
    high::rsa::tests::pairwise_rsa8192_sign_verify
    high::rsa::tests::pss_salt_must_fit_modulus
    high::rsa::tests::refuses_a_faulty_signature
    high::rsa::tests::refuses_mismatched_private_key
    high::rsa::tests::signs_with_crt_half_above_p
    high::rsa::tests::verify_rejects_signature_not_modulus_length
    high::signature::tests::digests_refused_as_unsupported
    high::signature::tests::ecdsa_generated_public_key_agrees_whichever_reads_first
    high::signature::tests::ecdsa_private_key_round_trips
    high::signature::tests::ecdsa_signs_and_verifies_any_digest
    high::signature::tests::ecdsa_verifies_only_under_its_algorithm
    high::signature::tests::encodings_fit_the_largest_keys
    high::signature::tests::rsa_public_key_components
    low::generic::ct_equal::tests::matches_eq
    low::generic::mldsa_poly::tests::backend_matches_port
    low::posint::tests::aws_lc_mod_exp
    low::posint::tests::aws_lc_mod_mul
    low::posint::tests::mont_exp_matches_square_and_multiply
    low::posint::tests::pub_montifier
    mid::aes::tests::cavp
    mid::aes::tests::srtp_aes_cm
    mid::mldsa::tests::wycheproof
    mid::p256::tests::base_point_precomp
    mid::p256::tests::generate_key_1
    mid::p256::tests::generate_key_2
    mid::p256::tests::multiply_matches_double_and_add
    mid::p256::tests::twin_multiply_exceptional
    mid::p384::tests::base_point_precomp_comb
    mid::p384::tests::generate_key_1
    mid::p384::tests::generate_key_2
    mid::p384::tests::generate_key_3
    mid::p384::tests::generate_key_99999999
    mid::p384::tests::multiply_matches_double_and_add
    mid::p384::tests::twin_multiply_exceptional
    mid::p521::tests::base_point_precomp_comb
    mid::p521::tests::multiplications_match_double_and_add
    mid::p521::tests::twin_multiply_exceptional
    mid::rsa_priv::generate::tests::aws_lc_miller_rabin
    mid::rsa_priv::generate::tests::test_invalid_primes
    mid::rsa_priv::generate::tests::test_phi_not_coprime_e
    mid::rsa_priv::generate::tests::test_p_q_close
    mid::rsa_priv::generate::tests::test_p_q_equal
    mid::rsa_priv::generate::tests::test_valid_primes
    mid::sha2::tests::sha256_all_lengths
    mid::sha2::tests::sha512_all_lengths
    mid::sha3::tests::cavp_shake
    mid::sha3::tests::sha3_256_all_lengths
    mid::sha3::tests::sha3_512_all_lengths
    mid::x25519::tests::rfc7748_3
)
filter=$(printf 'test(=%s) | ' "${slow[@]}")
# NIST's ACVP sample vectors are vector sets too, each test too slow for Miri.
filter="not (${filter}test(/::acvp/))"

# `--cfg rind_portable` forces the portable backend on x86_64, and dalek's
# serial backend is the one the targets that need it run. The tests read the
# vector files, which Miri's isolation forbids. `tests/zeroing.rs` reads a
# dropped value on purpose, and `tests/wycheproof.rs` and `tests/aws_lc.rs`
# are vector sets too slow for Miri, so only the unit tests and the CPU and
# Debug tests run.
export RUSTFLAGS='--cfg rind_portable --cfg curve25519_dalek_backend="serial"'
export MIRIFLAGS=-Zmiri-disable-isolation
args=(-p rind --features wipe --locked --target "$target" --lib --test cpu --test debug)

# A slow entry that names no test, such as one a rename left behind, would let
# the renamed test back into the run unnoticed. The listing builds what the
# run then reuses, under the same flags and `cfg(miri)`.
tests=$(cargo miri nextest list "${args[@]}" --message-format oneline | cut -d' ' -f2)
stale=0
for name in "${slow[@]}"; do
    if ! grep -qxF -- "$name" <<<"$tests"; then
        echo "miri: slow entry matches no test: $name" >&2
        stale=1
    fi
done
if ((stale)); then
    exit 1
fi

cargo miri nextest run "${args[@]}" --no-fail-fast -E "$filter"
