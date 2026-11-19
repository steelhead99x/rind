import Rind.Armv7.ChaCha20
open rind.armv7

/-!
The axioms each theorem rests on, beyond Lean's own: none. A change here is a
change to the trust base.
-/

/-- info: 'rind.armv7.chacha20_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_new

/-- info: 'rind.armv7.chacha20_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chacha20_mask
