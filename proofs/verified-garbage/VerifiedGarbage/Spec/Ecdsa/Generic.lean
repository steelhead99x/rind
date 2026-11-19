module

public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.TCB.Artifact

/-!
# ECDSA over any curve: its instances, on every target

**Trusted** (as every file in `Spec/`). An `Instance` is a curve as the Rust
interface has it: the curve, its name in the functions' names (in the module
`ecdsa_<name>`), and its name in their documentation. Each curve is an
`Instance` in a file of its own (`Spec/Ecdsa/P256.lean`, …), and needs
nothing else. The contracts of its functions are those of its verification
(`Spec/Ecdsa/Verify/Generic.lean`) and of its deterministic signature
(`Spec/Ecdsa/Rfc6979/Table.lean`), which take the hash function's output
itself, and the private key and the signature as `len` and `2 len` octets
read by `bytesAt`.
-/

@[expose] public section

namespace VG.Spec.Ecdsa

open Weierstrass

/-- The bytes at `p`, in increasing address order. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Working space in `u64`s. -/
def scratchWords : Nat := 1024

/-- A curve, and its names in the Rust interface. -/
structure Instance where
  curve : Curve
  /-- The name in function and module names, e.g. `p256`. -/
  name : String
  /-- The name in documentation, e.g. `P-256`. -/
  title : String

end VG.Spec.Ecdsa
