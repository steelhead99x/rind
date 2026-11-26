module

/-!
# Multiword arithmetic: the working space's layout

The layout of the working space of the RSA code, the same on every target,
so that the facts about it (`Proof/Bignum/Layout.lean`) are proven once.

The working space's first 256 bytes are a header of 32 words: slots 0–5 for
registers a target saves there, `w` (slot `sW`), `-m⁻¹ mod 2⁶⁴` (`sMinv`),
the bases of up to 8 arrays (`sArr`), and the functions' own values
(`sFn`); the arrays follow, each `w + 2` words.
-/

@[expose] public section

namespace VG.Impl.Bignum

/-- Slot 6: `w`. Slot 7: `-m⁻¹ mod 2⁶⁴`. -/
def sW : Nat := 6
def sMinv : Nat := 7
/-- Slots 8–15: the bases of up to 8 arrays. -/
def sArr (j : Nat) : Nat := 8 + j

/-- Slots 16–31: for the functions' own use. -/
def sFn (j : Nat) : Nat := 16 + j

/-- The size of the header, in bytes. -/
def hdrBytes : Nat := 256

/-! ## The arrays and slots of the public-key operation

The arrays: `m` (0), the input (1), the accumulator (2), a temporary (3),
`R² mod m` (4), the input in Montgomery form (5), the result (6) and the
number 1 (7). -/

namespace Public

def aN : Nat := 0
def aX : Nat := 1
def aAcc : Nat := 2
def aTmp : Nat := 3
def aR2 : Nat := 4
def aXm : Nat := 5
def aY : Nat := 6
def aOne : Nat := 7

/-- Header slots of the arguments and counters. -/
def sOut : Nat := sFn 0
def sN : Nat := sFn 1
def sK : Nat := sFn 2
def sE : Nat := sFn 3
def sElen : Nat := sFn 4
def sIn : Nat := sFn 5
def sMask : Nat := sFn 6
def sI : Nat := sFn 7
def sBit : Nat := sFn 8
def sV : Nat := sFn 9
def sCnt : Nat := sFn 10

/-- Whether the exponentiation from precomputed values has met a set bit of
`e`: 0 or 1. -/
def sStarted : Nat := sFn 11

end Public

end VG.Impl.Bignum
