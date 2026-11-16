import Rind.Aarch64.Hmac
import Rind.Aarch64.DigestApi
open rind.aarch64

/-!
The axioms the SHA-1, SHA-256, HMAC, and digest API theorems rest on, beyond
Lean's own. SHA-1's block function's contract is `Sha1Blocks`, a hypothesis of
each theorem. SHA-256's is `Sha256Blocks`, which only asks that the CPU has the
crypto extension, and whose theorem rests on `sha256_block_data_order_hw_spec`,
rind's HOL Light proof of the routine. `Axioms` pins the theorems over every
HMAC algorithm, which rest on SHA-512's too. A change here is a change to the
trust base. `admin/prove` copies the files beside it from x86_64's, but not
this one, since each target's SHA-256 theorems rest on axioms of its own.
-/

/-- info: 'rind.aarch64.sha256_hash' depends on axioms: [propext, Classical.choice, Quot.sound, sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms sha256_hash

/-- info: 'rind.aarch64.sha1_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha1_hash

/-- info: 'rind.aarch64.hmac_sha256_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms hmac_sha256_sign

/-- info: 'rind.aarch64.hmac_sha1_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_sha1_sign

/-- info: 'rind.aarch64.hmac_start_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_start_spec

/-- info: 'rind.aarch64.hmac_update_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_update_spec

/-- info: 'rind.aarch64.hmac_finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_finish_spec

/-- info: 'rind.aarch64.digest_spec' depends on axioms: [propext, Classical.choice, Quot.sound, sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms digest_spec

/-- info: 'rind.aarch64.digest_ctx_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest_ctx_new_spec

/-- info: 'rind.aarch64.digest_ctx_update_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms digest_ctx_update_spec

/-- info: 'rind.aarch64.digest_ctx_finish_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sha256_block_data_order_hw_spec] -/
#guard_msgs in
#print axioms digest_ctx_finish_spec

