module

public import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Multiword arithmetic: the layout of the private-key operation

`vg_rsa_private_crt` keeps three workspaces, each with the layout of
`Layout.lean`, in its working space: `n`'s at `scratch`, then `p`'s and
`q`'s, each followed by room for its exponentiation's table of 32 entries. These
are the header slots and arrays it uses besides the public-key operation's,
the same on every target.
-/

@[expose] public section

namespace VG.Impl.Bignum.Crt

/-! ## `n`'s header

`n`'s workspace keeps the public-key operation's `sOut`, `sN`, `sK`, `sIn`,
`sMask` and `sCnt`, and the key's pointers and lengths. -/

def sP : Nat := sFn 3
def sPlen : Nat := sFn 4
def sQ : Nat := sFn 7
def sQlen : Nat := sFn 8
def sDp : Nat := sFn 9
def sDq : Nat := sFn 11
def sQinv : Nat := sFn 12
/-- The bases of `p`'s and `q`'s workspaces. -/
def sWsP : Nat := sFn 13
def sWsQ : Nat := sFn 14
/-- The exponent `E - 64 w` of `G`. -/
def sD : Nat := sFn 15

/-! ## A prime's header

The base of `n`'s workspace, the exponent's pointer and length, its byte
index, its windows left in the byte, its byte, the words left and the
source of `redc`, and the mask. -/

def sLink : Nat := sFn 0
def sExp : Nat := sFn 1
def sExpLen : Nat := sFn 2
def sI : Nat := sFn 3
def sBit : Nat := sFn 4
def sV : Nat := sFn 5
def sRem : Nat := sFn 6
def sSrc : Nat := sFn 7
def sMaskX : Nat := sFn 8
/-- The window's table: its first entry, the entry being written or read,
the window's value and the entry's index. -/
def sTab : Nat := sFn 9
def sEnt : Nat := sFn 10
def sNib : Nat := sFn 11
def sJ : Nat := sFn 12

/-- The arrays of `p`'s and `q`'s workspaces, besides `X` (`aN`), the
accumulator and the temporary: `redc`'s chunk and `qInv` (1), `x R_X`
(4), the product `Y X` (5), `Y` (6) and the number 1 (7). -/
def aChunk : Nat := 1
def aXc : Nat := 4
def aT : Nat := 5

end VG.Impl.Bignum.Crt
