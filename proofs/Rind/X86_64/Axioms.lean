import Rind.X86_64.X25519
import Rind.X86_64.P384
import Rind.X86_64.Sha512
import Rind.X86_64.Pbkdf2
import Rind.X86_64.ChaCha20
import Rind.X86_64.AesGcm
import Rind.X86_64.GcmKey
import Rind.X86_64.Ed25519
open rind.x86_64

/-!
The axioms each theorem rests on, beyond Lean's own: s2n-bignum's contracts
in `Rind.X86_64.S2nBignum` for X25519, P-384 ECDH, and Ed25519, aws-lc's in
`Rind.X86_64.AwsLc` for the SHA-512 family, for HMAC, HKDF, and PBKDF2, which
cover SHA-384 and SHA-512, and for Ed25519's hashes, Vale's in
`Rind.X86_64.ValeAesGcm` for AES-GCM, rind's HOL Light proofs of its
constant-time compares in `Rind.X86_64.CtEqual` for HMAC's and PBKDF2's
`verify`, and nothing else. A change here is a
change to the trust base.
-/

/-- info: 'rind.x86_64.x25519_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 curve25519_x25519base_alt_spec,
 curve25519_x25519base_spec] -/
#guard_msgs in
#print axioms x25519_generate

/-- info: 'rind.x86_64.x25519_from_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 curve25519_x25519base_alt_spec,
 curve25519_x25519base_spec] -/
#guard_msgs in
#print axioms x25519_from_scalar

/-- info: 'rind.x86_64.x25519_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_public_key

/-- info: 'rind.x86_64.x25519_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_eq_spec,
 curve25519_x25519_alt_spec,
 curve25519_x25519_spec] -/
#guard_msgs in
#print axioms x25519_agree

/-- info: 'rind.x86_64.x25519_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_shared_secret

/-- info: 'rind.x86_64.p384_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 p384_montjscalarmul_alt_spec,
 p384_montjscalarmul_spec] -/
#guard_msgs in
#print axioms p384_agree

/-- info: 'rind.x86_64.p384_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p384_shared_secret

/-- info: 'rind.x86_64.sha512_family_digest' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms sha512_family_digest

/-- info: 'rind.x86_64.sha512_family_context' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms sha512_family_context

/-- info: 'rind.x86_64.key_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms key_new_spec

/-- info: 'rind.x86_64.sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms sign_spec

/-- info: 'rind.x86_64.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms verify_spec

/-- info: 'rind.x86_64.context_with_key_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms context_with_key_spec

/-- info: 'rind.x86_64.context_update_spec'' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms context_update_spec'

/-- info: 'rind.x86_64.context_sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms context_sign_spec

/-- info: 'rind.x86_64.kdf.salt_extract_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms kdf.salt_extract_spec

/-- info: 'rind.x86_64.kdf.okm_fill_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms kdf.okm_fill_spec

/-- info: 'rind.x86_64.kdf.hkdf_fill' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms kdf.hkdf_fill

/-- info: 'rind.x86_64.kdf.derive_spec' depends on axioms: [propext, Classical.choice, Quot.sound, compress_avx_spec] -/
#guard_msgs in
#print axioms kdf.derive_spec

/-- info: 'rind.x86_64.kdf.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms kdf.verify_spec

/-- info: 'rind.x86_64.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.x86_64.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask

/-- info: 'rind.x86_64.aes_gcm_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_gcm_new

/-- info: 'rind.x86_64.aes_gcm_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_encrypt_opt_spec,
 gcm256_encrypt_opt_spec] -/
#guard_msgs in
#print axioms aes_gcm_seal

/-- info: 'rind.x86_64.aes_gcm_seal_append_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_encrypt_opt_spec,
 gcm256_encrypt_opt_spec] -/
#guard_msgs in
#print axioms aes_gcm_seal_append_tag

/-- info: 'rind.x86_64.aes_gcm_seal_append_tag_vec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_encrypt_opt_spec,
 gcm256_encrypt_opt_spec] -/
#guard_msgs in
#print axioms aes_gcm_seal_append_tag_vec

/-- info: 'rind.x86_64.aes_gcm_open_separate_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms aes_gcm_open_separate_tag

/-- info: 'rind.x86_64.aes_gcm_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms aes_gcm_open

/-- info: 'rind.x86_64.gcm_key_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gcm_key_new

/-- info: 'rind.x86_64.gcm_key_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_encrypt_opt_spec,
 gcm256_encrypt_opt_spec] -/
#guard_msgs in
#print axioms gcm_key_seal

/-- info: 'rind.x86_64.gcm_key_seal_append_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_encrypt_opt_spec,
 gcm256_encrypt_opt_spec] -/
#guard_msgs in
#print axioms gcm_key_seal_append_tag

/-- info: 'rind.x86_64.gcm_key_open_separate_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms gcm_key_open_separate_tag

/-- info: 'rind.x86_64.gcm_key_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms gcm_key_open

/-- info: 'rind.x86_64.ed25519_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 edwards25519_scalarmulbase_alt_spec,
 edwards25519_scalarmulbase_spec] -/
#guard_msgs in
#print axioms ed25519_generate

/-- info: 'rind.x86_64.ed25519_from_seed_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 edwards25519_scalarmulbase_alt_spec,
 edwards25519_scalarmulbase_spec] -/
#guard_msgs in
#print axioms ed25519_from_seed_and_public_key

/-- info: 'rind.x86_64.ed25519_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_madd_n25519_alt_spec,
 bignum_madd_n25519_spec,
 bignum_mod_n25519_spec,
 compress_avx_spec,
 edwards25519_scalarmulbase_alt_spec,
 edwards25519_scalarmulbase_spec] -/
#guard_msgs in
#print axioms ed25519_sign

/-- info: 'rind.x86_64.ed25519_key_pair_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ed25519_key_pair_public_key

/-- info: 'rind.x86_64.ed25519_key_pair_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_cmp_lt_spec,
 bignum_mod_n25519_spec,
 bignum_neg_p25519_spec,
 compress_avx_spec,
 edwards25519_scalarmuldouble_alt_spec,
 edwards25519_scalarmuldouble_spec] -/
#guard_msgs in
#print axioms ed25519_key_pair_verify

/-- info: 'rind.x86_64.ed25519_public_key_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_cmp_lt_spec,
 bignum_eq_spec,
 bignum_mod_n25519_spec,
 bignum_neg_p25519_spec,
 compress_avx_spec,
 edwards25519_decode_alt_spec,
 edwards25519_decode_spec,
 edwards25519_scalarmuldouble_alt_spec,
 edwards25519_scalarmuldouble_spec] -/
#guard_msgs in
#print axioms ed25519_public_key_new
