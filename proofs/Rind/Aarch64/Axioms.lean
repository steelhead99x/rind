import Rind.Aarch64.X25519
import Rind.Aarch64.P384
import Rind.Aarch64.Sha512
import Rind.Aarch64.Pbkdf2
import Rind.Aarch64.P256
import Rind.Aarch64.ChaCha20
import Rind.Aarch64.Ed25519
import Rind.Aarch64.P256Signature
open rind.aarch64

/-!
The axioms each theorem rests on, beyond Lean's own: s2n-bignum's contracts
in `Rind.Aarch64.S2nBignum` for X25519, P-256, P-384 ECDH, and Ed25519, aws-lc's in
`Rind.Aarch64.AwsLc` for the SHA-512 family, for HMAC, HKDF, and PBKDF2,
which cover SHA-384 and SHA-512, and for Ed25519's hashes, rind's HOL Light
proofs of its constant-time compares in `Rind.Aarch64.CtEqual` for HMAC's and
PBKDF2's `verify`, and nothing else.
A change here is a change to the trust base.
-/

/-- info: 'rind.aarch64.x25519_generate' depends on axioms: [propext, Classical.choice, Quot.sound, curve25519_x25519base_spec] -/
#guard_msgs in
#print axioms x25519_generate

/-- info: 'rind.aarch64.x25519_from_scalar' depends on axioms: [propext, Classical.choice, Quot.sound, curve25519_x25519base_spec] -/
#guard_msgs in
#print axioms x25519_from_scalar

/-- info: 'rind.aarch64.x25519_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_public_key

/-- info: 'rind.aarch64.x25519_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_eq_spec,
 curve25519_x25519_spec] -/
#guard_msgs in
#print axioms x25519_agree

/-- info: 'rind.aarch64.x25519_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_shared_secret

/-- info: 'rind.aarch64.p256_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_spec,
 p256_scalarmulbase_spec] -/
#guard_msgs in
#print axioms p256_generate

/-- info: 'rind.aarch64.p256_from_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_spec,
 p256_scalarmulbase_spec] -/
#guard_msgs in
#print axioms p256_from_scalar

/-- info: 'rind.aarch64.p256_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p256_public_key

/-- info: 'rind.aarch64.p256_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_spec,
 p256_scalarmul_spec] -/
#guard_msgs in
#print axioms p256_agree

/-- info: 'rind.aarch64.p256_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p256_shared_secret

/-- info: 'rind.aarch64.p384_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_montmul_p384_spec,
 bignum_montsqr_p384_spec,
 bignum_tomont_p384_spec,
 p384_montjscalarmul_spec] -/
#guard_msgs in
#print axioms p384_agree

/-- info: 'rind.aarch64.p384_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p384_shared_secret

/-- info: 'rind.aarch64.sha512_family_digest' depends on axioms: [propext, Classical.choice, Quot.sound, compress_nohw_spec] -/
#guard_msgs in
#print axioms sha512_family_digest

/-- info: 'rind.aarch64.sha512_family_context' depends on axioms: [propext, Classical.choice, Quot.sound, compress_nohw_spec] -/
#guard_msgs in
#print axioms sha512_family_context

/-- info: 'rind.aarch64.key_new_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms key_new_spec

/-- info: 'rind.aarch64.sign_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms sign_spec

/-- info: 'rind.aarch64.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms verify_spec

/-- info: 'rind.aarch64.context_with_key_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms context_with_key_spec

/-- info: 'rind.aarch64.context_update_spec'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms context_update_spec'

/-- info: 'rind.aarch64.context_sign_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms context_sign_spec

/-- info: 'rind.aarch64.kdf.salt_extract_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms kdf.salt_extract_spec

/-- info: 'rind.aarch64.kdf.okm_fill_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms kdf.okm_fill_spec

/-- info: 'rind.aarch64.kdf.hkdf_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms kdf.hkdf_fill

/-- info: 'rind.aarch64.kdf.derive_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms kdf.derive_spec

/-- info: 'rind.aarch64.kdf.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms kdf.verify_spec

/-- info: 'rind.aarch64.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.aarch64.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask

/-- info: 'rind.aarch64.ed25519_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 edwards25519_scalarmulbase_spec] -/
#guard_msgs in
#print axioms ed25519_generate

/-- info: 'rind.aarch64.ed25519_from_seed_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_nohw_spec,
 edwards25519_scalarmulbase_spec] -/
#guard_msgs in
#print axioms ed25519_from_seed_and_public_key

/-- info: 'rind.aarch64.ed25519_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_madd_n25519_spec,
 bignum_mod_n25519_spec,
 compress_nohw_spec,
 edwards25519_scalarmulbase_spec] -/
#guard_msgs in
#print axioms ed25519_sign

/-- info: 'rind.aarch64.ed25519_key_pair_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ed25519_key_pair_public_key

/-- info: 'rind.aarch64.ed25519_key_pair_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_cmp_lt_spec,
 bignum_mod_n25519_spec,
 bignum_neg_p25519_spec,
 compress_nohw_spec,
 edwards25519_scalarmuldouble_spec] -/
#guard_msgs in
#print axioms ed25519_key_pair_verify

/-- info: 'rind.aarch64.ed25519_public_key_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_cmp_lt_spec,
 bignum_eq_spec,
 bignum_mod_n25519_spec,
 bignum_neg_p25519_spec,
 compress_nohw_spec,
 edwards25519_decode_spec,
 edwards25519_scalarmuldouble_spec] -/
#guard_msgs in
#print axioms ed25519_public_key_new

/-- info: 'rind.aarch64.p256_ecdsa_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_eq_spec,
 bignum_mod_n256_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_generate

/-- info: 'rind.aarch64.p256_ecdsa_from_scalar_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_spec,
 p256_scalarmulbase_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_from_scalar_and_public_key

/-- info: 'rind.aarch64.p256_ecdsa_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_mod_n256_spec,
 bignum_modadd_spec,
 bignum_modinv_spec,
 bignum_montmul_p256_spec,
 bignum_montmul_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_spec,
 p256_scalarmulbase_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_sign

/-- info: 'rind.aarch64.p256_ecdsa_key_pair_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_spec,
 p256_scalarmulbase_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_key_pair_public_key

/-- info: 'rind.aarch64.p256_ecdsa_key_pair_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_modinv_spec,
 bignum_montmul_p256_spec,
 bignum_montmul_spec,
 bignum_montsqr_p256_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_spec,
 p256_montjadd_spec,
 p256_montjdouble_spec,
 p256_montjmixadd_spec,
 p256_scalarmulbase_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_key_pair_verify

/-- info: 'rind.aarch64.p256_ecdsa_public_key_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_modinv_spec,
 bignum_montmul_p256_spec,
 bignum_montmul_spec,
 bignum_montsqr_p256_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_spec,
 p256_montjadd_spec,
 p256_montjdouble_spec,
 p256_montjmixadd_spec,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_public_key_new
