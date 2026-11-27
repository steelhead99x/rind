import Rind.Armv7.ChaCha20
import Rind.Armv7.X25519
import Rind.Armv7.AesNohwKey
open rind.armv7

/-!
The axioms each theorem rests on, beyond Lean's own: none but X25519's, which
rest on `Rind.Armv7.Dalek`'s restatements of Beneficial AI Foundation's
theorems about curve25519-dalek's `mul_clamped` and `mul_base_clamped`. A
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

/-!
The bitsliced AES's theorems rest on Lean's own axioms and on the ones
`bv_decide` adds, one a call: each states that Lean's compiled LRAT checker
accepted a SAT solver's certificate for one bit-vector identity of the S-box
circuit, a round step, a key schedule step, or the batch layout. `#bv_axioms` fails on any other.
-/

open Lean Elab Command in
/-- Fails unless the theorem rests only on Lean's axioms and `bv_decide`'s. -/
elab "#bv_axioms " id:ident : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms thm
  let other := axs.filter fun a =>
    a != ``propext && a != ``Classical.choice && a != ``Quot.sound &&
      (a.toString.splitOn "._native.bv_decide.ax_").length != 2
  unless other.isEmpty do throwError "{thm} depends on axioms: {other}"

#bv_axioms encrypt_batch_spec
#bv_axioms encrypt_block_spec
#bv_axioms new_schedule_spec
#bv_axioms schedule_encrypt_block
