import Rind.Mcu.Hmac
import Rind.Mcu.DigestApi
open rind.mcu

/-!
The axioms the SHA-1, SHA-256, HMAC, and digest API theorems rest on, on
32-bit microcontrollers with ESP-IDF Xtensa's SHA-256: Lean's own, and nothing
else. SHA-1's block function's contract is `Sha1Blocks`, a
hypothesis of each theorem; SHA-256's is proven, and `Sha256Blocks` states
only its entry checks. `Axioms` pins
the theorems over every HMAC algorithm, which take SHA-512's too. A change
here is a change to the trust base.
-/

/-- info: 'rind.mcu.sha256_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha256_hash

/-- info: 'rind.mcu.sha1_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha1_hash

/-- info: 'rind.mcu.hmac_sha256_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_sha256_sign

/-- info: 'rind.mcu.hmac_sha1_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_sha1_sign

/-- info: 'rind.mcu.hmac_start_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_start_spec

/-- info: 'rind.mcu.hmac_update_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_update_spec

/-- info: 'rind.mcu.hmac_finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hmac_finish_spec

/-- info: 'rind.mcu.digest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest_spec

/-- info: 'rind.mcu.digest_ctx_new_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest_ctx_new_spec

/-- info: 'rind.mcu.digest_ctx_update_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest_ctx_update_spec

/-- info: 'rind.mcu.digest_ctx_finish_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest_ctx_finish_spec
