module

public import VerifiedGarbage.Spec.P192
public import VerifiedGarbage.Spec.P224
public import VerifiedGarbage.Spec.P256
public import VerifiedGarbage.Spec.P384
public import VerifiedGarbage.Spec.P521
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.Spec.BrainpoolP256r1
public import VerifiedGarbage.Spec.BrainpoolP384r1
public import VerifiedGarbage.Spec.BrainpoolP512r1

/-!
# Montgomery arithmetic modulo a curve's `p` or `n`: its moduli and working space

Not trusted: what the code of the curves' internal functions (`Rust.Internal`),
which only verified code calls, is generated from, and where it keeps its
numbers. The definitions their proofs share are in
`Proof/Weierstrass/MontContract.lean`, in these namespaces.
-/

@[expose] public section

namespace VG.Impl.Weierstrass.Mont

/-- The bytes of the working space. -/
def wsBytes : Nat := 8192

/-- The bytes of the working space that a function uses for itself, for
numbers of `k` 64-bit words. -/
def ownBytes (k : Nat) : Nat := 64 * k

/-- Where they start: they end at byte 4096. -/
def ownAt (k : Nat) : Nat := 4096 - ownBytes k

/-- A modulus: its curve's name (the functions are `vg_<curve>_*`, in the
Rust module `<curve>_mont`), which of the curve's numbers it is (`p` or
`n`), its value `m`, odd, and the count `k` of 64-bit words of the numbers,
with `m < 2^(64 k)`. -/
structure Modulus where
  curve : String
  which : String
  m : Nat
  k : Nat
  /-- How the documentation names the modulus. -/
  desc : String

namespace Modulus

variable (M : Modulus)

/-- The name of the function `op` modulo `m`. -/
def fn (op : String) : String := s!"vg_{M.curve}_{op}_mod_{M.which}"

end Modulus

/-! ## The moduli -/

def p192p : Modulus := ⟨"p192", "p", Spec.P192.p, 3, "P-192's prime `p`"⟩

def p192n : Modulus := ⟨"p192", "n", Spec.P192.n, 3, "P-192's order `n`"⟩

def p224p : Modulus := ⟨"p224", "p", Spec.P224.p, 4, "P-224's prime `p`"⟩

def p224n : Modulus := ⟨"p224", "n", Spec.P224.n, 4, "P-224's order `n`"⟩

def p256p : Modulus := ⟨"p256", "p", Spec.P256.p, 4, "P-256's prime `p`"⟩

def p256n : Modulus := ⟨"p256", "n", Spec.P256.n, 4, "P-256's order `n`"⟩

def p384p : Modulus := ⟨"p384", "p", Spec.P384.p, 6, "P-384's prime `p`"⟩

def p384n : Modulus := ⟨"p384", "n", Spec.P384.n, 6, "P-384's order `n`"⟩

def p521p : Modulus := ⟨"p521", "p", Spec.P521.p, 9, "P-521's prime `p`"⟩

def p521n : Modulus := ⟨"p521", "n", Spec.P521.n, 9, "P-521's order `n`"⟩

def secp256k1p : Modulus := ⟨"secp256k1", "p", Spec.Secp256k1.p, 4, "secp256k1's prime `p`"⟩

def secp256k1n : Modulus := ⟨"secp256k1", "n", Spec.Secp256k1.n, 4, "secp256k1's order `n`"⟩

def brainpoolp256r1p : Modulus :=
  ⟨"brainpoolp256r1", "p", Spec.BrainpoolP256r1.p, 4, "brainpoolP256r1's prime `p`"⟩

def brainpoolp256r1n : Modulus :=
  ⟨"brainpoolp256r1", "n", Spec.BrainpoolP256r1.n, 4, "brainpoolP256r1's order `n`"⟩

def brainpoolp384r1p : Modulus :=
  ⟨"brainpoolp384r1", "p", Spec.BrainpoolP384r1.p, 6, "brainpoolP384r1's prime `p`"⟩

def brainpoolp384r1n : Modulus :=
  ⟨"brainpoolp384r1", "n", Spec.BrainpoolP384r1.n, 6, "brainpoolP384r1's order `n`"⟩

def brainpoolp512r1p : Modulus :=
  ⟨"brainpoolp512r1", "p", Spec.BrainpoolP512r1.p, 8, "brainpoolP512r1's prime `p`"⟩

def brainpoolp512r1n : Modulus :=
  ⟨"brainpoolp512r1", "n", Spec.BrainpoolP512r1.n, 8, "brainpoolP512r1's order `n`"⟩

end VG.Impl.Weierstrass.Mont
