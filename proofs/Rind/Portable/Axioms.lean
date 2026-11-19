import Rind.Portable.Sha512
import Rind.Portable.Pbkdf2
import Rind.Portable.ChaCha20
import Rind.Portable.Sha3
open rind.portable

/-!
The axioms each theorem rests on, beyond Lean's own: HACL*'s SHA-2 contracts
in `Rind.Portable.Hacl` for the SHA-512 family, and for HMAC, HKDF, and
PBKDF2, which cover SHA-256, SHA-384, and SHA-512, and nothing else. The
compares behind HMAC's and PBKDF2's `verify`, and ChaCha20's rounds, are
proven here, as is the SHA-3 sponge down to its Keccak-f, which rests on none
but Lean's. A change here is a change to the trust base.
-/

/-- info: 'rind.portable.sha512_family_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms sha512_family_digest

/-- info: 'rind.portable.sha512_family_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms sha512_family_context

/-- info: 'rind.portable.key_new_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms key_new_spec

/-- info: 'rind.portable.sign_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms sign_spec

/-- info: 'rind.portable.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms verify_spec

/-- info: 'rind.portable.context_with_key_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms context_with_key_spec

/-- info: 'rind.portable.context_update_spec'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms context_update_spec'

/-- info: 'rind.portable.context_sign_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms context_sign_spec

/-- info: 'rind.portable.kdf.salt_extract_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms kdf.salt_extract_spec

/-- info: 'rind.portable.kdf.prk_fill_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms kdf.prk_fill_spec

/-- info: 'rind.portable.kdf.hkdf_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms kdf.hkdf_fill

/-- info: 'rind.portable.kdf.prk_new_fill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms kdf.prk_new_fill

/-- info: 'rind.portable.kdf.derive_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms kdf.derive_spec

/-- info: 'rind.portable.kdf.verify_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec,
 sha512_update_nblocks_spec] -/
#guard_msgs in
#print axioms kdf.verify_spec

/-- info: 'rind.portable.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.portable.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask

/-- info: 'rind.portable.sha3_family_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha3_family_digest

/-- info: 'rind.portable.sha3_family_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha3_family_context

/-- info: 'rind.portable.sha3Family_fips202' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha3Family_fips202

/-- info: 'rind.portable.sponge_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sponge_new_spec

/-- info: 'rind.portable.sponge_absorb_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sponge_absorb_spec

/-- info: 'rind.portable.sponge_finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sponge_finish_spec

/-- info: 'rind.portable.squeezing_squeeze_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms squeezing_squeeze_spec

/-- info: 'rind.portable.shake128x4_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shake128x4_new_spec

/-- info: 'rind.portable.shake128x4_squeeze_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shake128x4_squeeze_spec

/-- info: 'rind.portable.shake256_batch_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shake256_batch_spec
