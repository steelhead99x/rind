import Rind.Mcu.Sha512
import Rind.Mcu.HmacApi
import Rind.Mcu.ChaCha20
open rind.mcu

/-!
The axioms the SHA-512 family's theorems on 32-bit microcontrollers rest on:
Lean's own, and nothing else. The rolled SHA-512 block function is proven
here; `RunsSha512`, a hypothesis of the SHA-512 family's theorems, states only
its entry checks. A change here is a change to the trust base.
-/

/-- info: 'rind.mcu.sha512_family_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha512_family_digest

/-- info: 'rind.mcu.sha512_family_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sha512_family_context

/-- info: 'rind.mcu.sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_spec

/-- info: 'rind.mcu.verify_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verify_spec

/-- info: 'rind.mcu.context_with_key_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms context_with_key_spec

/-- info: 'rind.mcu.context_update_spec'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms context_update_spec'

/-- info: 'rind.mcu.context_sign_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms context_sign_spec

/-- info: 'rind.mcu.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.mcu.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask
