import Rind.Armv7.ChaCha20
import Rind.Armv7.X25519
import Rind.Armv7.Ed25519
import Rind.Armv7.AesNohwKey
import Rind.Armv7.GcmKey
import Rind.Armv7.GhashNeon
open rind.armv7

/-!
The axioms each theorem rests on, beyond Lean's own. X25519's and
Ed25519's rest on `Rind.Armv7.Dalek`'s restatements of Beneficial AI
Foundation's theorems about the curve25519-dalek functions they call, and
Ed25519's on `Rind.Armv7.Sha512Entry`'s restatement of the HOL Light proof of
aws-lc's NEON SHA-512 routine too; the AES and GHASH theorems' are below. A
change here is a change to the trust base.
-/

/-- info: 'rind.armv7.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.armv7.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask

/-- info: 'rind.armv7.x25519_generate' depends on axioms: [propext, Classical.choice, Quot.sound, dalek_mul_base_clamped_spec] -/
#guard_msgs in
#print axioms x25519_generate

/-- info: 'rind.armv7.x25519_from_scalar' depends on axioms: [propext, Classical.choice, Quot.sound, dalek_mul_base_clamped_spec] -/
#guard_msgs in
#print axioms x25519_from_scalar

/-- info: 'rind.armv7.x25519_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_public_key

/-- info: 'rind.armv7.x25519_agree' depends on axioms: [propext, Classical.choice, Quot.sound, dalek_mul_clamped_spec] -/
#guard_msgs in
#print axioms x25519_agree

/-- info: 'rind.armv7.x25519_shared_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms x25519_shared_secret

/-- info: 'rind.armv7.ed25519_generate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 dalek_compress_spec,
 dalek_from_bytes_mod_order_spec,
 dalek_mul_base_spec,
 sha512_block_data_order_neon_spec] -/
#guard_msgs in
#print axioms ed25519_generate

/-- info: 'rind.armv7.ed25519_from_seed_and_public_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 dalek_compress_spec,
 dalek_from_bytes_mod_order_spec,
 dalek_mul_base_spec,
 sha512_block_data_order_neon_spec] -/
#guard_msgs in
#print axioms ed25519_from_seed_and_public_key

/-- info: 'rind.armv7.ed25519_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 dalek_compress_spec,
 dalek_from_bytes_mod_order_wide_spec,
 dalek_mul_base_spec,
 dalek_scalar_add_spec,
 dalek_scalar_mul_spec,
 sha512_block_data_order_neon_spec] -/
#guard_msgs in
#print axioms ed25519_sign

/-- info: 'rind.armv7.ed25519_key_pair_public_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ed25519_key_pair_public_key

/-- info: 'rind.armv7.ed25519_key_pair_verify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 dalek_compress_spec,
 dalek_from_bytes_mod_order_wide_spec,
 dalek_from_canonical_bytes_spec,
 dalek_neg_spec,
 dalek_vartime_double_scalar_mul_basepoint_spec,
 sha512_block_data_order_neon_spec] -/
#guard_msgs in
#print axioms ed25519_key_pair_verify

/-- info: 'rind.armv7.ed25519_public_key_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 dalek_compress_spec,
 dalek_decompress_spec,
 dalek_from_bytes_mod_order_wide_spec,
 dalek_from_canonical_bytes_spec,
 dalek_neg_spec,
 dalek_vartime_double_scalar_mul_basepoint_spec,
 sha512_block_data_order_neon_spec] -/
#guard_msgs in
#print axioms ed25519_public_key_new

/-!
The bitsliced AES's theorems rest on Lean's own axioms and on the ones
`bv_decide` adds, one a call: each states that Lean's compiled LRAT checker
accepted a SAT solver's certificate for one bit-vector identity of the S-box
circuit, a round step, a key schedule step, the batch layout, or a counter or
GHASH step. `#bv_axioms` fails on any other but the ones it names after the
theorem: AES-GCM's tag check also rests on `Rind.Armv7.CtEqual`'s
restatement of rind's HOL Light proofs of its constant-time compares. So do
the AEAD API's and the custom-IV key's theorems above `AesGcm`.
-/

open Lean Elab Command in
/-- Fails unless the theorem rests only on Lean's axioms, `bv_decide`'s, and
the ones named after it. -/
elab "#bv_axioms " id:ident extra:ident* : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let allowed ← liftCoreM <| extra.toList.mapM realizeGlobalConstNoOverloadWithInfo
  let axs ← liftCoreM <| collectAxioms thm
  let other := axs.filter fun a =>
    a != ``propext && a != ``Classical.choice && a != ``Quot.sound && !allowed.contains a &&
      (a.toString.splitOn "._native.bv_decide.ax_").length != 2
  unless other.isEmpty do throwError "{thm} depends on axioms: {other}"

#bv_axioms encrypt_batch_spec
#bv_axioms encrypt_block_spec
#bv_axioms new_schedule_spec
#bv_axioms schedule_encrypt_block
#bv_axioms aes_gcm_new_spec
#bv_axioms aes_gcm_encrypt_spec
#bv_axioms aes_gcm_decrypt_spec ct_compare_16_spec ct_compare_bytes_spec
#bv_axioms aes_gcm_encrypt_any_spec
#bv_axioms aes_gcm_decrypt_any_spec ct_compare_16_spec ct_compare_bytes_spec
#bv_axioms aes_gcm_new
#bv_axioms aes_gcm_seal
#bv_axioms aes_gcm_seal_append_tag
#bv_axioms aes_gcm_seal_append_tag_vec
#bv_axioms aes_gcm_open_separate_tag ct_compare_16_spec ct_compare_bytes_spec
#bv_axioms aes_gcm_open ct_compare_16_spec ct_compare_bytes_spec
#bv_axioms gcm_key_new
#bv_axioms gcm_key_seal
#bv_axioms gcm_key_seal_append_tag
#bv_axioms gcm_key_open_separate_tag ct_compare_16_spec ct_compare_bytes_spec
#bv_axioms gcm_key_open ct_compare_16_spec ct_compare_bytes_spec

/-!
NEON GHASH's theorems also rest on `Rind.Armv7.GhashNeon`'s restatements of
rind's HOL Light proofs of `gcm_init_neon` and `gcm_ghash_neon`.
-/

#bv_axioms neon_ghashFor neon_table_ghash_spec
#bv_axioms neon_new_ghashFor neon_table_new_spec neon_table_ghash_spec
