module

public import VerifiedGarbage.TCB.Mem

/-!
# Zeroization

**Trusted** (as every file in `Spec/`). Not a cryptographic algorithm: the
wipe of a buffer that held secrets (keys, intermediate values) before its
memory is released or reused. In Rust, stores to memory that is not read
again may be removed as dead stores; a call to a generated function, whose
code the compiler cannot see, cannot be.

This file is independent of any architecture; the contract on every target
is in `Spec/Zeroize/Contract.lean`.
-/

@[expose] public section

namespace VG.Spec.Zeroize

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- `n` zero bytes. -/
def zeros (n : Nat) : List Byte := List.replicate n 0

/-- The `len` bytes at `p` hold nothing written between memories `m` (on
entry) and `m'` (on return): each is unchanged or zero. The contract of a
function given a buffer to work in (`scratch`) states it of that buffer, so
that nothing the function computed is left there, while an implementation
need wipe only the bytes it may write. -/
def scrubbed (m m' : Mem) (p : Addr) (len : Nat) : Prop :=
  ∀ a, Region.Contains ⟨p, len⟩ a 1 → m' a = m a ∨ m' a = 0

end VG.Spec.Zeroize
