import Rind.Portable.Hmac
import Rind.Portable.DigestApi
open rind.portable

/-!
The axioms the SHA-1, SHA-256, HMAC, and digest API theorems rest on, beyond
Lean's own: HACL*'s SHA-256 contract in `Rind.Portable.Hacl` for SHA-256, and
nothing else. SHA-1's block function's contract is `Sha1Blocks`, a hypothesis
of each theorem. `Axioms` pins the theorems over every HMAC algorithm, which
rest on SHA-512's. A change here is a change to the trust base.
-/

/-- info: 'rind.portable.sha256_hash' depends on axioms: [propext, Classical.choice, Quot.sound, sha256_update_nblocks_spec] -/
#guard_msgs in
#print axioms sha256_hash

/-- info: 'rind.portable.sha1_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha1_hash

/-- info: 'rind.portable.hmac_sha256_sign' depends on axioms: [propext, Classical.choice, Quot.sound, sha256_update_nblocks_spec] -/
#guard_msgs in
#print axioms hmac_sha256_sign

/-- info: 'rind.portable.hmac_sha1_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_sha1_sign

/-- info: 'rind.portable.hmac_start_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_start_spec

/-- info: 'rind.portable.hmac_update_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_update_spec

/-- info: 'rind.portable.hmac_finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_finish_spec

/-- info: 'rind.portable.digest_spec' depends on axioms: [propext, Classical.choice, Quot.sound, sha256_update_nblocks_spec] -/
#guard_msgs in
#print axioms digest_spec

/-- info: 'rind.portable.digest_ctx_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest_ctx_new_spec

/-- info: 'rind.portable.digest_ctx_update_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec] -/
#guard_msgs in
#print axioms digest_ctx_update_spec

/-- info: 'rind.portable.digest_ctx_finish_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_update_nblocks_spec] -/
#guard_msgs in
#print axioms digest_ctx_finish_spec
