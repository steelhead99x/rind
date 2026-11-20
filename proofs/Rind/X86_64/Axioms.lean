import Rind.X86_64.X25519
import Rind.X86_64.P256Agree
import Rind.X86_64.P256
import Rind.X86_64.P256Base
import Rind.X86_64.P384
import Rind.X86_64.P384Keygen
import Rind.X86_64.Sha512
import Rind.X86_64.Pbkdf2
import Rind.X86_64.ChaCha20
import Rind.X86_64.AesGcm
import Rind.X86_64.ChaCha20Poly1305
import Rind.X86_64.ChaCha20Cipher
import Rind.X86_64.GcmKey
import Rind.X86_64.Ed25519
import Rind.X86_64.Ed25519Ifma
import Rind.X86_64.RsaDispatch
import Rind.X86_64.Sha3
import Rind.X86_64.AesKw
import Rind.X86_64.P256Signature
import Rind.X86_64.P384Signature
import Rind.X86_64.PointSelect
import Rind.X86_64.MlKemCoding
open rind.x86_64

/-!
The axioms each theorem rests on, beyond Lean's own: s2n-bignum's contracts
in `Rind.X86_64.S2nBignum` for X25519, P-256 key generation, ECDH, and
ECDSA, P-384, Ed25519, RSA verification, and the Keccak-f of SHA-3 and
ML-KEM's SHAKE; for the SHA-512 family, for HMAC, HKDF, and PBKDF2, which
cover SHA-384 and SHA-512, and for Ed25519's hashes, aws-lc's AVX routine's in
`Rind.X86_64.AwsLc` and rind's HOL Light proof there of OpenSSL's AVX2
routine; for SHA-256, which the theorems over every HMAC algorithm cover,
rind's HOL Light proofs of its routines for the SHA extensions in
`Rind.X86_64.Sha256Shaext`; Vale's in
`Rind.X86_64.ValeAesGcm` for AES-GCM, rind's HOL Light proofs of its
constant-time compares in `Rind.X86_64.CtEqual` for HMAC's and PBKDF2's
`verify`, AES-GCM's tag check, ChaCha20-Poly1305's and XChaCha20-Poly1305's
tag checks, RSASSA-PSS's hash compare, and key wrap's `unwrap` and
`unwrap_padded` checks; for RSA verification's public operation on AVX-512
IFMA, pyca/verified-garbage's Lean proof of its routine, which
`Rind.X86_64.VgRsa` restates; pyca/verified-garbage's for ChaCha20's
`apply_keystream` in `Rind.X86_64.VgChaCha20`, for X25519 and Ed25519 on
AVX-512 IFMA in `Rind.X86_64.VgCurve25519`, and for P-256's public key, ECDH,
and ECDSA verification in `Rind.X86_64.VgP256`, and for P-384's public key and
ECDSA verification in `Rind.X86_64.VgP384`; and nothing else.
ChaCha20-Poly1305's theorems also take aws-lc's one-pass routines as the
hypothesis `RunsChaCha20Poly1305`, which no axiom states. ChaCha20's
`apply_keystream` on a CPU without AVX2 takes aws-lc's SSSE3 routine as the
hypothesis `Ssse3`; `Rind.X86_64.ChaCha20Avx2` proves rind's two-block kernel
over `Rind.X86_64.Simd`'s models of the AVX2 intrinsics. The generator
tables' point selects rest on no axiom, only on the hand model in
`Rind.X86_64.PointSelectModel`. P-256's generator multiplication also rests
on `p256_point_add_affine_spec` in `Rind.X86_64.S2nBignum`, which restates
rind's HOL Light proofs of aws-lc's mixed addition. A change here is a
change to the trust base.
-/

/-- info: 'rind.x86_64.x25519_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 curve25519_x25519base_alt_spec,
 curve25519_x25519base_spec,
 vg_x25519_base_spec] -/
#guard_msgs in
#print axioms x25519_generate

/-- info: 'rind.x86_64.x25519_from_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 curve25519_x25519base_alt_spec,
 curve25519_x25519base_spec,
 vg_x25519_base_spec] -/
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
 curve25519_x25519_spec,
 vg_x25519_exchange_spec] -/
#guard_msgs in
#print axioms x25519_agree

/-- info: 'rind.x86_64.x25519_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_shared_secret

/-- info: 'rind.x86_64.p256_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 p256_point_add_affine_spec,
 vg_p256_public_key_spec] -/
#guard_msgs in
#print axioms p256_generate

/-- info: 'rind.x86_64.p256_from_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 p256_point_add_affine_spec,
 vg_p256_public_key_spec] -/
#guard_msgs in
#print axioms p256_from_scalar

/-- info: 'rind.x86_64.p256_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p256_public_key

/-- info: 'rind.x86_64.p256_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 p256_scalarmul_alt_spec,
 p256_scalarmul_spec,
 vg_p256_ecdh_spec] -/
#guard_msgs in
#print axioms p256_agree

/-- info: 'rind.x86_64.p256_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p256_shared_secret

/-- info: 'rind.x86_64.p384_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_mux_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 vg_p384_public_key_spec] -/
#guard_msgs in
#print axioms p384_generate

/-- info: 'rind.x86_64.p384_from_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_mux_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 vg_p384_public_key_spec] -/
#guard_msgs in
#print axioms p384_from_scalar

/-- info: 'rind.x86_64.p384_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p384_public_key

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

/-- info: 'rind.x86_64.sha512_family_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms sha512_family_digest

/-- info: 'rind.x86_64.sha512_family_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms sha512_family_context

/-- info: 'rind.x86_64.key_new_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms key_new_spec

/-- info: 'rind.x86_64.sign_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms sign_spec

/-- info: 'rind.x86_64.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms verify_spec

/-- info: 'rind.x86_64.context_with_key_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms context_with_key_spec

/-- info: 'rind.x86_64.context_update_spec'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms context_update_spec'

/-- info: 'rind.x86_64.context_sign_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms context_sign_spec

/-- info: 'rind.x86_64.kdf.salt_extract_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms kdf.salt_extract_spec

/-- info: 'rind.x86_64.kdf.prk_fill_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms kdf.prk_fill_spec

/-- info: 'rind.x86_64.kdf.hkdf_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms kdf.hkdf_fill

/-- info: 'rind.x86_64.kdf.prk_new_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms kdf.prk_new_fill

/-- info: 'rind.x86_64.kdf.derive_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms kdf.derive_spec

/-- info: 'rind.x86_64.kdf.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 finish_padded_spec,
 sha256_compress_blocks_shaext_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms kdf.verify_spec

/-- info: 'rind.x86_64.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.x86_64.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask

/-- info: 'rind.x86_64.chacha20_apply_keystream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 vg_chacha20_apply_avx2_spec,
 vg_chacha20_apply_avx512vl_spec,
 vg_chacha20_init_spec] -/
#guard_msgs in
#print axioms chacha20_apply_keystream

/-- info: 'rind.x86_64.chacha20_apply_keystream_ssse3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 vg_chacha20_apply_avx2_spec,
 vg_chacha20_apply_avx512vl_spec,
 vg_chacha20_init_spec] -/
#guard_msgs in
#print axioms chacha20_apply_keystream_ssse3

/-- info: 'rind.x86_64.avx2.kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms avx2.kernel

/-- info: 'rind.x86_64.generic.cipher_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms generic.cipher_spec

/-- info: 'rind.x86_64.chacha20_poly1305_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_poly1305_new

/-- info: 'rind.x86_64.chacha20_poly1305_seal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_poly1305_seal

/-- info: 'rind.x86_64.chacha20_poly1305_seal_append_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_poly1305_seal_append_tag

/-- info: 'rind.x86_64.chacha20_poly1305_seal_append_tag_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_poly1305_seal_append_tag_vec

/-- info: 'rind.x86_64.chacha20_poly1305_open_separate_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms chacha20_poly1305_open_separate_tag

/-- info: 'rind.x86_64.chacha20_poly1305_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms chacha20_poly1305_open

/-- info: 'rind.x86_64.randomized_nonce_key_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms randomized_nonce_key_new

/-- info: 'rind.x86_64.randomized_nonce_key_seal_append_tag_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms randomized_nonce_key_seal_append_tag_vec

/-- info: 'rind.x86_64.randomized_nonce_key_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms randomized_nonce_key_open

/-- info: 'rind.x86_64.aes_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_new

/-- info: 'rind.x86_64.aes_encrypt_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_encrypt_block

/-- info: 'rind.x86_64.aes_header_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_header_new

/-- info: 'rind.x86_64.aes_header_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aes_header_mask

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
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms aes_gcm_open_separate_tag

/-- info: 'rind.x86_64.aes_gcm_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
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
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms gcm_key_open_separate_tag

/-- info: 'rind.x86_64.gcm_key_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 counter_block_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 gcm128_decrypt_opt_spec,
 gcm256_decrypt_opt_spec] -/
#guard_msgs in
#print axioms gcm_key_open

/-- info: 'rind.x86_64.ed25519_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 edwards25519_scalarmulbase_alt_spec,
 edwards25519_scalarmulbase_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms ed25519_generate

/-- info: 'rind.x86_64.ed25519_from_seed_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 compress_avx_spec,
 edwards25519_scalarmulbase_alt_spec,
 edwards25519_scalarmulbase_spec,
 sha512_block_data_order_avx2_spec] -/
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
 edwards25519_scalarmulbase_spec,
 sha512_block_data_order_avx2_spec] -/
#guard_msgs in
#print axioms ed25519_sign

/-- info: 'rind.x86_64.ed25519_key_pair_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ed25519_key_pair_public_key

/-- info: 'rind.x86_64.ed25519_generate_ifma' depends on axioms: [propext, Classical.choice, Quot.sound, vg_ed25519_key_pair_spec] -/
#guard_msgs in
#print axioms ed25519_generate_ifma

/-- info: 'rind.x86_64.ed25519_from_seed_and_public_key_ifma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 vg_ed25519_key_pair_spec] -/
#guard_msgs in
#print axioms ed25519_from_seed_and_public_key_ifma

/-- info: 'rind.x86_64.ed25519_sign_ifma' depends on axioms: [propext, Classical.choice, Quot.sound, vg_ed25519_sign_spec] -/
#guard_msgs in
#print axioms ed25519_sign_ifma

/-- info: 'rind.x86_64.ed25519_key_pair_public_key_ifma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ed25519_key_pair_public_key_ifma

/-- info: 'rind.x86_64.ed25519_key_pair_verify_ifma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 vg_ed25519_verify_spec] -/
#guard_msgs in
#print axioms ed25519_key_pair_verify_ifma

/-- info: 'rind.x86_64.ed25519_public_key_new_ifma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_eq_spec,
 edwards25519_decode_alt_spec,
 edwards25519_decode_spec,
 vg_ed25519_verify_spec] -/
#guard_msgs in
#print axioms ed25519_public_key_new_ifma

/-- info: 'rind.x86_64.p256_ecdsa_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 p256_point_add_affine_spec,
 vg_p256_public_key_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_generate

/-- info: 'rind.x86_64.p256_ecdsa_from_scalar_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 p256_point_add_affine_spec,
 vg_p256_public_key_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_from_scalar_and_public_key

/-- info: 'rind.x86_64.p256_ecdsa_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_modadd_spec,
 bignum_modinv_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montmul_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 finish_padded_spec,
 p256_point_add_affine_spec,
 sha256_compress_blocks_shaext_spec,
 vg_p256_public_key_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_sign

/-- info: 'rind.x86_64.p256_ecdsa_key_pair_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p256_ecdsa_key_pair_public_key

/-- info: 'rind.x86_64.p256_ecdsa_key_pair_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_modinv_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montmul_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 finish_padded_spec,
 p256_montjadd_alt_spec,
 p256_montjadd_spec,
 p256_montjdouble_alt_spec,
 p256_montjdouble_spec,
 p256_montjmixadd_alt_spec,
 p256_montjmixadd_spec,
 sha256_compress_blocks_shaext_spec,
 vg_p256_verify_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_key_pair_verify

/-- info: 'rind.x86_64.p256_ecdsa_public_key_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p256_spec,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p256_spec,
 bignum_mod_n256_spec,
 bignum_modinv_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montmul_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 finish_padded_spec,
 p256_montjadd_alt_spec,
 p256_montjadd_spec,
 p256_montjdouble_alt_spec,
 p256_montjdouble_spec,
 p256_montjmixadd_alt_spec,
 p256_montjmixadd_spec,
 sha256_compress_blocks_shaext_spec,
 vg_p256_verify_spec] -/
#guard_msgs in
#print axioms p256_ecdsa_public_key_new

/-- info: 'rind.x86_64.p384_ecdsa_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_mux_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 vg_p384_public_key_spec] -/
#guard_msgs in
#print axioms p384_ecdsa_generate

/-- info: 'rind.x86_64.p384_ecdsa_from_scalar_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_mux_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 vg_p384_public_key_spec] -/
#guard_msgs in
#print axioms p384_ecdsa_from_scalar_and_public_key

/-- info: 'rind.x86_64.p384_ecdsa_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_modadd_spec,
 bignum_modinv_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montmul_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_mux_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 compress_avx_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 sha512_block_data_order_avx2_spec,
 vg_p384_public_key_spec] -/
#guard_msgs in
#print axioms p384_ecdsa_sign

/-- info: 'rind.x86_64.p384_ecdsa_key_pair_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms p384_ecdsa_key_pair_public_key

/-- info: 'rind.x86_64.p384_ecdsa_key_pair_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_modinv_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montmul_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 compress_avx_spec,
 p384_montjadd_alt_spec,
 p384_montjadd_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 sha512_block_data_order_avx2_spec,
 vg_p384_verify_spec] -/
#guard_msgs in
#print axioms p384_ecdsa_key_pair_verify

/-- info: 'rind.x86_64.p384_ecdsa_public_key_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_add_p384_spec,
 bignum_demont_p384_alt_spec,
 bignum_demont_p384_spec,
 bignum_demont_spec,
 bignum_eq_spec,
 bignum_inv_p384_spec,
 bignum_mod_n384_spec,
 bignum_modinv_spec,
 bignum_montmul_p384_alt_spec,
 bignum_montmul_p384_spec,
 bignum_montmul_spec,
 bignum_montsqr_p384_alt_spec,
 bignum_montsqr_p384_spec,
 bignum_neg_p384_spec,
 bignum_tomont_p384_alt_spec,
 bignum_tomont_p384_spec,
 compress_avx_spec,
 p384_montjadd_alt_spec,
 p384_montjadd_spec,
 p384_montjdouble_alt_spec,
 p384_montjdouble_spec,
 p384_montjmixadd_alt_spec,
 p384_montjmixadd_spec,
 sha512_block_data_order_avx2_spec,
 vg_p384_verify_spec] -/
#guard_msgs in
#print axioms p384_ecdsa_public_key_new

/-- info: 'rind.x86_64.rsa_signature_new_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_bitsize_spec,
 bignum_negmodinv_spec] -/
#guard_msgs in
#print axioms rsa_signature_new_spec

/-- info: 'rind.x86_64.rsa_signature_from_spki_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_bitsize_spec,
 bignum_negmodinv_spec] -/
#guard_msgs in
#print axioms rsa_signature_from_spki_spec

/-- info: 'rind.x86_64.rsa_signature_from_components_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_bitsize_spec,
 bignum_negmodinv_spec] -/
#guard_msgs in
#print axioms rsa_signature_from_components_spec

/-- info: 'rind.x86_64.rsa_pkcs1_sha256_verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_bitsize_spec,
 bignum_cmp_lt_spec,
 bignum_negmodinv_spec,
 finish_padded_spec,
 rsa_ifma_public_spec,
 sha256_compress_blocks_shaext_spec] -/
#guard_msgs in
#print axioms rsa_pkcs1_sha256_verify_spec

/-- info: 'rind.x86_64.rsa_pss_sha256_verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_bitsize_spec,
 bignum_cmp_lt_spec,
 bignum_negmodinv_spec,
 ct_compare_16_spec,
 ct_compare_bytes_spec,
 finish_padded_spec,
 rsa_ifma_public_spec,
 sha256_compress_blocks_shaext_spec] -/
#guard_msgs in
#print axioms rsa_pss_sha256_verify_spec

/-- info: 'rind.x86_64.rsa2048_mont_products' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_cmp_lt_spec,
 bignum_emontredc_8n_spec,
 bignum_kmul_16_32_spec,
 bignum_kmul_32_64_spec,
 bignum_ksqr_16_32_spec,
 bignum_ksqr_32_64_spec,
 bignum_optsub_spec] -/
#guard_msgs in
#print axioms rsa2048_mont_products

/-- info: 'rind.x86_64.sha3_family_digest' depends on axioms: [propext, Classical.choice, Quot.sound, sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms sha3_family_digest

/-- info: 'rind.x86_64.sha3_family_context' depends on axioms: [propext, Classical.choice, Quot.sound, sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms sha3_family_context

/-- info: 'rind.x86_64.sha3Family_fips202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha3Family_fips202

/-- info: 'rind.x86_64.sponge_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sponge_new_spec

/-- info: 'rind.x86_64.sponge_absorb_spec' depends on axioms: [propext, Classical.choice, Quot.sound, sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms sponge_absorb_spec

/-- info: 'rind.x86_64.sponge_finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sponge_finish_spec

/-- info: 'rind.x86_64.squeezing_squeeze_spec' depends on axioms: [propext, Classical.choice, Quot.sound, sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms squeezing_squeeze_spec

/-- info: 'rind.x86_64.shake128x4_new_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha3_keccak4_f1600_alt_spec,
 sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms shake128x4_new_spec

/-- info: 'rind.x86_64.shake128x4_squeeze_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha3_keccak4_f1600_alt_spec,
 sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms shake128x4_squeeze_spec

/-- info: 'rind.x86_64.shake256_batch_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha3_keccak4_f1600_alt_spec,
 sha3_keccak_f1600_spec] -/
#guard_msgs in
#print axioms shake256_batch_spec

/-- info: 'rind.x86_64.kek_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kek_new_spec

/-- info: 'rind.x86_64.kek_wrap_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kek_wrap_spec

/-- info: 'rind.x86_64.kek_unwrap_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms kek_unwrap_spec

/-- info: 'rind.x86_64.kek_wrap_padded_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kek_wrap_padded_spec

/-- info: 'rind.x86_64.kek_unwrap_padded_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms kek_unwrap_padded_spec

/-- info: 'rind.x86_64.kek_wrap_key_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms kek_wrap_key_spec

/-- info: 'rind.x86_64.kek_unwrap_key_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 ct_compare_16_spec,
 ct_compare_bytes_spec] -/
#guard_msgs in
#print axioms kek_unwrap_key_spec

/-- info: 'rind.x86_64.bignum_aff_point_select_p256_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bignum_aff_point_select_p256_spec

/-- info: 'rind.x86_64.bignum_aff_point_select_p384_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bignum_aff_point_select_p384_spec

/-- info: 'rind.x86_64.bignum_aff_point_select_p521_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bignum_aff_point_select_p521_spec

/-- info: 'rind.x86_64.bignum_aff_point_select_p384_rows16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bignum_aff_point_select_p384_rows16

/-- info: 'rind.x86_64.P256Base.tabulated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P256Base.tabulated

/-- info: 'rind.x86_64.P256Base.first_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms P256Base.first_row

/-- info: 'rind.x86_64.P256Base.jac_base_multiply_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 p256_point_add_affine_spec] -/
#guard_msgs in
#print axioms P256Base.jac_base_multiply_spec

/-- info: 'rind.x86_64.P256Base.base_multiply_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 bignum_demont_p256_alt_spec,
 bignum_demont_p256_spec,
 bignum_inv_p256_spec,
 bignum_montmul_p256_alt_spec,
 bignum_montmul_p256_spec,
 bignum_montsqr_p256_alt_spec,
 bignum_montsqr_p256_spec,
 bignum_mux_spec,
 bignum_neg_p256_spec,
 bignum_tomont_p256_alt_spec,
 bignum_tomont_p256_spec,
 p256_point_add_affine_spec] -/
#guard_msgs in
#print axioms P256Base.base_multiply_spec

/-- info: 'rind.x86_64.MlKemCoding.decompress_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MlKemCoding.decompress_spec

/-- info: 'rind.x86_64.MlKemCoding.from_message_bits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MlKemCoding.from_message_bits_spec

/-- info: 'rind.x86_64.MlKemCoding.to_message_bits_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MlKemCoding.to_message_bits_spec
