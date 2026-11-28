module

public import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
public import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-KEM on x86-64: `NTT` in two passes, on registers

`nttR d` is `NTT` of the 256 `u32`s at `rdi` to the 256 `u32`s at `d`
(which may be `rdi`), with 512 bytes of working space at `rsi + oS` (`S`),
on sixteen words at a time in AVX2 registers:

* Pass A (`passA`): the layer `len = 128`, on the blocks of sixteen
  coefficients `i` and `i + 8`, each packed from `u32`s to words as it is
  loaded (`vpackssdw`, then `vpermq` to put the words back in order), and
  stored as words to `S`.
* Pass B (`passB H`), for each half `H` of `S`: its eight blocks in eight
  registers, the layers `len = 64`, `32` and `16` on whole registers, then
  the layers `len = 8`, `4` and `2` on each pair of registers, each after
  exchanging their halves (`vperm2i128`), quadwords (`vpunpck{l,h}qdq`) and
  doublewords (`vpsllq`, `vpsrlq`, `vpblendd`), so that the two words of each
  butterfly are in the same lane of the two registers. Then each word is
  reduced to its value (Montgomery multiplication by `2¹⁶ mod q`, then `q`
  added to the negative ones), the doublewords of each pair of registers
  interleaved back (`vpunpck{l,h}dq`), which leaves in each register two runs
  of eight coefficients, and these stored as `u32`s (`vpermq`, then
  `vpunpck{l,h}wd` with zero).

The butterflies reduce lazily, with the
zetas `ζ · 2¹⁶ mod q` and `ζ · 2¹⁶ · q⁻¹ mod q mod 2¹⁶` of every word read
from a table of constants the instructions carry (`vmovdquTbl`, `zetaTbl`):
`vpmullw t, b, ζ'; vpmulhw b, b, ζ; vpmulhw t, t, q; vpsubw b, b, t` is
`vmont`, and `vpsubw u, a, b; vpaddw a, a, b` the butterfly. A register
freed by a butterfly or an exchange takes the next result (`Alloc`), so that
no value is moved between registers.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

namespace NttR

/-! ## The table of zetas -/

/-- The index of the zeta of lane `i` of entry `v` of `NTT`'s part of the
table: `0` (`2¹⁶ mod q`, for the reduction) and `1` (`len = 128`), then for
each half `H`, from `2 + 19 H`: `len = 64`, `32` (two), `16` (four), and `8`,
`4`, `2` (four each, one per pair of registers). -/
def fwdIdx (v i : Nat) : Nat :=
  if v = 0 then 0 else if v = 1 then 1 else
  let H := (v - 2) / 19
  let e := (v - 2) % 19
  if e = 0 then 2 + H
  else if e < 3 then 4 + 2 * H + (e - 1)
  else if e < 7 then 8 + 4 * H + (e - 3)
  else if e < 11 then 16 + 8 * H + 2 * (e - 7) + i / 8
  else if e < 15 then 32 + 16 * H + 4 * (e - 11) + i / 4
  else 64 + 32 * H + 8 * (e - 15) + i / 2

/-- The distance of the butterflies of entry `42 + 19 H + e` of `NTT⁻¹`. -/
def invLen (e : Nat) : Nat :=
  if e < 4 then 2 else if e < 8 then 4 else if e < 12 then 8 else if e < 16 then 16 else if e < 18 then 32 else 64

/-- The entry of `NTT`'s part whose lanes hold the same blocks as entry
`42 + 19 H + e` of `NTT⁻¹` (the same register pair, at the same distance). -/
def invFwdE (e : Nat) : Nat :=
  if e < 4 then 15 + e else if e < 8 then 7 + e else if e < 12 then e - 1 else if e < 16 then e - 9
  else if e < 18 then e - 15 else 0

/-- The index of the zeta of lane `i` of entry `v`: `NTT`'s (`fwdIdx`) below
40; then for `NTT⁻¹`, `40` (`len = 128`), `41` (the scaling, not a zeta), and
for each half `H`, from `42 + 19 H`: `len = 2`, `4`, `8`, `16` (four entries
each, one per pair of registers), `32` (two) and `64`. A block whose zeta is
`ζ^BitRev₇(128 / len + c)` in `NTT` takes `ζ^BitRev₇(256 / len - 1 - c)` in
`NTT⁻¹`. -/
def zetaIdx (v i : Nat) : Nat :=
  if v < 40 then fwdIdx v i
  else if v < 42 then 1
  else
    let H := (v - 42) / 19
    let e := (v - 42) % 19
    384 / invLen e - 1 - fwdIdx (2 + 19 * H + invFwdE e) i

/-- The number of entries of the table. -/
def nEntries : Nat := 80

/-- The constant of lane `i` of entry `v`: `512` (`2¹⁶ · 3303 · 2¹⁶ mod q`,
`NTT⁻¹`'s scaling by Montgomery multiplication) in entry 41, the zeta
`ζ · 2¹⁶ mod q` of `zetaIdx` in the others. -/
def zetaLane (v i : Nat) : Nat := if v = 41 then 512 else zmTab (zetaIdx v i)

/-- Word `j` of entry `v`: the constants of its sixteen lanes, then each
times `q⁻¹ mod 2¹⁶`. -/
def zetaWord (v j : Nat) : Nat :=
  if j < 16 then zetaLane v j else zetaLane v (j - 16) * 62209 % 65536

/-- Quadword `w` of the table, four words, the first in the low bits. -/
def zetaQword (w : Nat) : BitVec 64 :=
  let v := w / 8
  let j := 4 * (w % 8)
  BitVec.ofNat 64 (zetaWord v j + zetaWord v (j + 1) * 2 ^ 16 + zetaWord v (j + 2) * 2 ^ 32 +
    zetaWord v (j + 3) * 2 ^ 48)

/-- The name of the table. -/
def tblName : String := "VG_MLKEM_NTT_ZETAS"

/-- The table: entry `v` at byte `64 v`. -/
def zetaTbl : List (BitVec 64) := (List.range (8 * nEntries)).map zetaQword

/-- The zetas `ζ` of entry `v` to `ymm z`, and `ζ'` to `ymm z'`. -/
def zv (z z' : XReg) (v : Nat) : List Instr :=
  [.vmovdquTbl z (at_ .r8 (64 * v)) tblName zetaTbl, .vmovdquTbl z' (at_ .r8 (64 * v + 32)) tblName zetaTbl]

/-! ## Registers -/

/-- `vop d, a, b` on 256-bit registers. -/
def yb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- The six instructions of the butterfly of `a` and `b`, with the zetas in
`z` and `z'`, a temporary `t` and the difference to `u`: `a ← a + ζ b`,
`u ← a - ζ b` (`b` is lost). -/
def bfly (a b z z' t u : XReg) : List Instr :=
  [yb .vpmullw t b z', yb .vpmulhw b b z, yb .vpmulhw t t .xmm15, yb .vpsubw b b t,
    yb .vpsubw u a b, yb .vpaddw a a b]

/-- The six instructions of the Gentleman–Sande butterfly of `a` and `b`,
with the zetas in `z` and `z'`, a temporary `t` and the difference to `u`:
`a ← a + b`, `u ← ζ (b - a)` (`b` is lost). -/
def gsfly (a b z z' t u : XReg) : List Instr :=
  [yb .vpsubw u b a, yb .vpaddw a a b, yb .vpmullw t u z', yb .vpmulhw u u z, yb .vpmulhw t t .xmm15,
    yb .vpsubw u u t]

/-- The registers of pass B: the physical register of each of its eight
blocks, those free, and the code so far. -/
structure Alloc where
  regs : List XReg
  free : List XReg
  code : Array Instr

namespace Alloc

def reg (A : Alloc) (i : Nat) : XReg := A.regs.getD i .xmm0

def emit (A : Alloc) (is : List Instr) : Alloc := { A with code := A.code ++ is.toArray }

/-- A free register, and the rest. -/
def take (A : Alloc) : XReg × Alloc := (A.free.headD .xmm0, { A with free := A.free.tail })

def give (A : Alloc) (r : XReg) : Alloc := { A with free := A.free ++ [r] }

/-- The zetas of entry `v`, in two free registers. -/
def zetas (A : Alloc) (v : Nat) : XReg × XReg × Alloc :=
  let (z, A) := A.take
  let (z', A) := A.take
  (z, z', A.emit (zv z z' v))

/-- The butterflies of the blocks `i` and `j` of each pair, with the zetas of
entry `v`, their instructions interleaved: the difference of each pair goes to
a free register, which becomes block `j`'s; `j`'s old register and the
temporary are freed. -/
def bflys (A : Alloc) (v : Nat) (ps : List (Nat × Nat))
    (bf : XReg → XReg → XReg → XReg → XReg → XReg → List Instr := bfly) : Alloc :=
  let (z, z', A) := A.zetas v
  let (ts, A) := ps.foldl (fun (acc : List (Nat × Nat × XReg × XReg) × Alloc) (p : Nat × Nat) =>
      let (t, B) := acc.2.take
      let (u, B) := B.take
      (acc.1 ++ [(p.1, p.2, t, u)], B)) ([], A)
  let A := (List.range 6).foldl (fun A k => A.emit (ts.flatMap fun (i, j, t, u) =>
    [(bf (A.reg i) (A.reg j) z z' t u).getD k (.vop .vzeroupper)])) A
  let A := ts.foldl (fun A (_, j, t, u) => { (A.give t |>.give (A.reg j)) with regs := A.regs.set j u }) A
  (A.give z).give z'

/-- The exchange of the halves (`kind = 8`), quadwords (`4`) or doublewords
(`2`) of blocks `i` and `j`: block `i` to a free register, `j` in place, and
`i`'s old register freed. -/
def exch (A : Alloc) (kind i j : Nat) : Alloc :=
  let a := A.reg i
  let b := A.reg j
  let (t, A) := A.take
  let A := A.emit <|
    if kind = 8 then [.vop (.vperm2i128 t a b 0x20), .vop (.vperm2i128 b a b 0x31)]
    else if kind = 4 then [yb .vpunpcklqdq t a b, yb .vpunpckhqdq b a b]
    else [.vop (.vshift .psllq .l256 t b 32), .vop (.vpblendd .l256 t a t 0xAA),
      .vop (.vshift .psrlq .l256 a a 32), .vop (.vpblendd .l256 b a b 0xAA)]
  { A.give a with regs := A.regs.set i t }

/-- The interleaving of the doublewords of blocks `i` and `j` back: `i` to a
free register, `j` in place. -/
def unexch (A : Alloc) (i j : Nat) : Alloc :=
  let a := A.reg i
  let b := A.reg j
  let (t, A) := A.take
  let A := A.emit [yb .vpunpckldq t a b, yb .vpunpckhdq b a b]
  { A.give a with regs := A.regs.set i t }

/-- `lo` and `hi` of blocks `i` and `j` (`vpunpckl*` and `vpunpckh*`): `lo`
to a free register, which becomes `i`'s, `hi` to `j` in place, and `i`'s old
register freed. -/
def unpk (A : Alloc) (lo hi : VBinOp) (i j : Nat) : Alloc :=
  let a := A.reg i
  let b := A.reg j
  let (t, A) := A.take
  let A := A.emit [yb lo t a b, yb hi b a b]
  { A.give a with regs := A.regs.set i t }

end Alloc

/-! ## The passes -/

/-- The sixteen `u32`s at `[rdi + off]` as words in order in `ymm d`, through `ymm t`. -/
def loadW (d t : XReg) (off : Nat) : List Instr :=
  [.vmovdquLoad .l256 d (at_ .rdi off), .vmovdquLoad .l256 t (at_ .rdi (off + 32)),
    yb .vpackssdw d d t, .vop (.vpermq d d 0xD8)]

/-- Pass A: the blocks `i` and `i + 8` of `rdi`, packed, the layer `len = 128`
on them, and both stored to `S`. -/
def passA : List Instr :=
  zv .xmm12 .xmm13 1 ++ (List.range 8).flatMap fun i =>
    loadW .xmm4 .xmm3 (64 * i) ++ loadW .xmm5 .xmm3 (64 * (i + 8)) ++ bfly .xmm4 .xmm5 .xmm12 .xmm13 .xmm2 .xmm6 ++
    [.vmovdquStore .l256 (at_ .rsi (oS + 32 * i)) .xmm4, .vmovdquStore .l256 (at_ .rsi (oS + 32 * (i + 8))) .xmm6]

/-- `passA` of `u16`s: each block of sixteen words one load. -/
def passA16 : List Instr :=
  zv .xmm12 .xmm13 1 ++ (List.range 8).flatMap fun i =>
    [.vmovdquLoad .l256 .xmm4 (at_ .rdi (32 * i)), .vmovdquLoad .l256 .xmm5 (at_ .rdi (32 * (i + 8)))] ++
      bfly .xmm4 .xmm5 .xmm12 .xmm13 .xmm2 .xmm6 ++
    [.vmovdquStore .l256 (at_ .rsi (oS + 32 * i)) .xmm4, .vmovdquStore .l256 (at_ .rsi (oS + 32 * (i + 8))) .xmm6]

/-- The first entry of the table of half `H`. -/
def base (H : Nat) : Nat := 2 + 19 * H

/-- The block in `ymm r` times `2¹⁶ mod q` by Montgomery multiplication (the
zetas in `c`, `c'`), reduced to `[0, q)` (`vcadd`), with a temporary `t`. -/
def red (r c c' t : XReg) : List Instr :=
  [yb .vpmullw t r c', yb .vpmulhw r r c, yb .vpmulhw t t .xmm15, yb .vpsubw r r t,
    .vop (.vshift .psraw .l256 t r 15), yb .vpand t t .xmm15, yb .vpaddw r r t]

/-- The words of `ymm r`, two runs of eight coefficients, stored as `u32`s to
`[d + off]` and `[d + off + 64]` (zero in `ymm z`, a temporary `t`). -/
def storeU (d : Reg) (r z t : XReg) (off : Nat) : List Instr :=
  [.vop (.vpermq r r 0xD8), yb .vpunpckhwd t r z, yb .vpunpcklwd r r z,
    .vmovdquStore .l256 (at_ d off) r, .vmovdquStore .l256 (at_ d (off + 64)) t]

/-- Pass B on half `H` of `S`, its words reduced, before they are stored:
in each pair of registers `2p`, `2p + 1`, the two words of each butterfly of
`len = 2` in the same lane. -/
def passBRed (H : Nat) : Alloc :=
  let A : Alloc := ⟨[.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7],
    [.xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14], #[]⟩
  let A := A.emit ((List.range 8).map fun i =>
    Instr.vmovdquLoad .l256 (A.reg i) (at_ .rsi (oS + 256 * H + 32 * i)))
  let b := base H
  -- len = 64, 32, 16
  let A := (A.bflys b [(0, 4), (1, 5)]).bflys b [(2, 6), (3, 7)]
  let A := (A.bflys (b + 1) [(0, 2), (1, 3)]).bflys (b + 2) [(4, 6), (5, 7)]
  let A := (List.range 4).foldl (fun A p => A.bflys (b + 3 + p) [(2 * p, 2 * p + 1)]) A
  -- len = 8, 4, 2
  let A := [(8, 7), (4, 11), (2, 15)].foldl (fun A (kind, e) =>
    let A := (List.range 4).foldl (fun A p => A.exch kind (2 * p) (2 * p + 1)) A
    (List.range 4).foldl (fun A p => A.bflys (b + e + p) [(2 * p, 2 * p + 1)]) A) A
  -- the reduction
  let (c, c', A) := A.zetas 0
  let A := (List.range 8).foldl (fun A i =>
    let (t, A) := A.take
    (A.emit (red (A.reg i) c c' t)).give t) A
  (A.give c).give c'

/-- Pass B on half `H` of `S`, its `u32`s to `d`. -/
def passBAlloc (d : Reg) (H : Nat) : Alloc :=
  let A := passBRed H
  -- back, and stored
  let A := (List.range 4).foldl (fun A p => A.unexch (2 * p) (2 * p + 1)) A
  let (z, A) := A.take
  let A := A.emit [yb .vpxor z z z]
  (List.range 4).foldl (fun A p =>
    let (t, A) := A.take
    let o := 4 * (128 * H + 32 * p)
    let A := A.emit (storeU d (A.reg (2 * p)) z t o ++ storeU d (A.reg (2 * p + 1)) z t (o + 32))
    A.give t) A

def passB (d : Reg) (H : Nat) : List Instr := (passBAlloc d H).code.toList

/-- Pass B on half `H` of `S`, its words to the accumulator at `d`
(`accIdx`, `KpkeAccY.lean`): the 32 coefficients of each pair of registers,
`32 (4H + p)` on, are block `4H + p` of the accumulator, their even
coefficients at `d + 64 (4H + p)` and their odd ones 32 bytes on, which
`vpunpck{l,h}wd`, `vpunpck{l,h}dq`, `vpunpck{l,h}qdq` and `vpermq` put in
its order. -/
def passBAccAlloc (d : Reg) (H : Nat) : Alloc :=
  let A := passBRed H
  (List.range 4).foldl (fun A p =>
    let A := A.unpk .vpunpcklwd .vpunpckhwd (2 * p) (2 * p + 1)
    let A := A.unpk .vpunpckldq .vpunpckhdq (2 * p) (2 * p + 1)
    let A := A.unpk .vpunpcklqdq .vpunpckhqdq (2 * p) (2 * p + 1)
    let a := A.reg (2 * p)
    let b := A.reg (2 * p + 1)
    let o := 256 * H + 64 * p
    A.emit [.vop (.vpermq a a 0xD8), .vop (.vpermq b b 0xD8), .vmovdquStore .l256 (at_ d o) a,
      .vmovdquStore .l256 (at_ d (o + 32)) b]) A

def passBAcc (d : Reg) (H : Nat) : List Instr := (passBAccAlloc d H).code.toList

/-- `q` in every word of `ymm15`, and the table's address to `r8`. -/
def pro : List Instr := yconst .xmm15 0x0D010D01 ++ [.leaSym .r8 tblName]

/-- Pass B on both halves, the `u32`s to `d`. -/
def passBs (d : Reg) : List Instr := passB d 0 ++ passB d 1

/-- Pass B storing to `r10`, for the functions that inline the NTT. -/
def passBsR10 : List Instr := passBs .r10

/-- Pass B on both halves, the words to the accumulator at `r10`. -/
def passBsAccR10 : List Instr := passBAcc .r10 0 ++ passBAcc .r10 1

/-! ## `NTT⁻¹` -/

/-- The first entry of the table of half `H` of `NTT⁻¹`. -/
def ibase (H : Nat) : Nat := 42 + 19 * H

/-- The block in `ymm r` times `2¹⁶ mod q` by Montgomery multiplication (the
zetas in `c`, `c'`), in `(-q, q)`, with a temporary `t`. -/
def redM (r c c' t : XReg) : List Instr :=
  [yb .vpmullw t r c', yb .vpmulhw r r c, yb .vpmulhw t t .xmm15, yb .vpsubw r r t]

/-- Every block reduced (`redM`), with the zetas of entry 0. -/
def Alloc.redAll (A : Alloc) : Alloc :=
  let (c, c', A) := A.zetas 0
  let A := (List.range 8).foldl (fun A i =>
    let (t, A) := A.take
    (A.emit (redM (A.reg i) c c' t)).give t) A
  (A.give c).give c'

/-- How pass B of `NTT⁻¹` reads its input: the 256 words of an accumulator
(`KpkeAccY.lean`'s order). -/
inductive InvIn
  | acc
  deriving DecidableEq

/-- The 32 coefficients `32 (4 H + p)` to `32 (4 H + p) + 31` of the input at
`rdi` into blocks `2 p` and `2 p + 1`, as `vpunpck{l,h}wd` of the two
registers of an accumulator's iteration, leave them: in each lane `l`, coefficients `4 l + {0, …, 3}`
and `8 + 4 l + {0, …, 3}` of the first sixteen, and the same of the next
sixteen. -/
def Alloc.loadI (A : Alloc) (src : InvIn) (H p : Nat) : Alloc :=
  let a := A.reg (2 * p)
  let b := A.reg (2 * p + 1)
  match src with
  | .acc =>
    let o := 256 * H + 64 * p
    let (t, A) := A.take
    let A := A.emit [.vmovdquLoad .l256 a (at_ .rdi o), .vmovdquLoad .l256 b (at_ .rdi (o + 32)),
      yb .vpunpcklwd t a b, yb .vpunpckhwd b a b]
    { A.give a with regs := A.regs.set (2 * p) t }

/-- Pass B of `NTT⁻¹` on half `H`: its 128 coefficients from `rdi`
(`loadI`), in the order of `NTT`'s layer `len = 2` after one exchange of
halves and one of doublewords, the layers `len = 2`, `4` and `8` on each pair
of registers, each followed by the exchange that undoes its order, the
reduction, the layers `len = 16` and `32` on whole registers, the reduction,
the layer `len = 64`, and the blocks stored as words to `S`. -/
def passIBAlloc (src : InvIn) (H : Nat) : Alloc :=
  let A : Alloc := ⟨[.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7],
    [.xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14], #[]⟩
  let A := (List.range 4).foldl (fun A p => A.loadI src H p) A
  let A := (List.range 4).foldl (fun A p => A.exch 8 (2 * p) (2 * p + 1)) A
  let A := (List.range 4).foldl (fun A p => A.exch 2 (2 * p) (2 * p + 1)) A
  let b := ibase H
  -- len = 2, 4, 8
  let A := [(2, 0), (4, 4), (8, 8)].foldl (fun A (kind, e) =>
    let A := (List.range 4).foldl (fun A p => A.bflys (b + e + p) [(2 * p, 2 * p + 1)] gsfly) A
    (List.range 4).foldl (fun A p => A.exch kind (2 * p) (2 * p + 1)) A) A
  let A := A.redAll
  -- len = 16, 32, 64
  let A := (List.range 4).foldl (fun A p => A.bflys (b + 12 + p) [(2 * p, 2 * p + 1)] gsfly) A
  let A := (A.bflys (b + 16) [(0, 2), (1, 3)] gsfly).bflys (b + 17) [(4, 6), (5, 7)] gsfly
  let A := A.redAll
  let A := (A.bflys (b + 18) [(0, 4), (1, 5)] gsfly).bflys (b + 18) [(2, 6), (3, 7)] gsfly
  A.emit ((List.range 8).map fun i => Instr.vmovdquStore .l256 (at_ .rsi (oS + 256 * H + 32 * i)) (A.reg i))

def passIB (src : InvIn) (H : Nat) : List Instr := (passIBAlloc src H).code.toList

/-- The block in `ymm r` times `c` by Montgomery multiplication (`c'` its
product with `q⁻¹`), reduced to `[0, q)` (`vcadd`), with a temporary `t`. -/
def scaleC (r c c' t : XReg) : List Instr :=
  redM r c c' t ++ [.vop (.vshift .psraw .l256 t r 15), yb .vpand t t .xmm15, yb .vpaddw r r t]

/-- Pass A of `NTT⁻¹`: the blocks `i` and `i + 8` of `S`, the layer
`len = 128` on them, each scaled by `3303` (Montgomery multiplication by
`512`) and reduced, and stored as `u32`s to `rdi`. -/
def passIA : List Instr :=
  zv .xmm12 .xmm13 40 ++ zv .xmm10 .xmm11 41 ++ [yb .vpxor .xmm9 .xmm9 .xmm9] ++ (List.range 8).flatMap fun i =>
    [.vmovdquLoad .l256 .xmm4 (at_ .rsi (oS + 32 * i)), .vmovdquLoad .l256 .xmm5 (at_ .rsi (oS + 32 * (i + 8)))] ++
    gsfly .xmm4 .xmm5 .xmm12 .xmm13 .xmm7 .xmm6 ++
    scaleC .xmm4 .xmm10 .xmm11 .xmm7 ++ scaleC .xmm6 .xmm10 .xmm11 .xmm7 ++
    [.vop (.vpermq .xmm4 .xmm4 0xD8), yb .vpunpckhwd .xmm7 .xmm4 .xmm9, yb .vpunpcklwd .xmm4 .xmm4 .xmm9,
      .vmovdquStore .l256 (at_ .rdi (64 * i)) .xmm4, .vmovdquStore .l256 (at_ .rdi (64 * i + 32)) .xmm7,
      .vop (.vpermq .xmm6 .xmm6 0xD8), yb .vpunpckhwd .xmm7 .xmm6 .xmm9, yb .vpunpcklwd .xmm6 .xmm6 .xmm9,
      .vmovdquStore .l256 (at_ .rdi (64 * (i + 8))) .xmm6, .vmovdquStore .l256 (at_ .rdi (64 * (i + 8) + 32)) .xmm7]

/-- Pass B of `NTT⁻¹` on both halves. -/
def passIBs (src : InvIn) : List Instr := passIB src 0 ++ passIB src 1

/-- Pass B reading an accumulator, for the functions that inline `NTT⁻¹`. -/
def passIBsAcc : List Instr := passIBs .acc

end NttR

open NttR in
/-- `NTT` of the `u32`s at `rdi` to the `u32`s at `d` (`passBs`), with `S` at `rsi + oS`. -/
def nttR (pb : List Instr) : Prog isa := .block (pro ++ passA ++ pb ++ [.vop .vzeroupper])

open NttR in
/-- `nttR` of the `u16`s at `rdi`. -/
def nttR16 (pb : List Instr) : Prog isa := .block (pro ++ passA16 ++ pb ++ [.vop .vzeroupper])

open NttR in
/-- `NTT⁻¹` of the input at `rdi` (`pb`: pass B reading an accumulator) to the
`u32`s at `rdi`, with `S` at `rsi + oS`. -/
def nttIR (pb : List Instr) : Prog isa := .block (pro ++ pb ++ passIA ++ [.vop .vzeroupper])

end VG.Impl.MlKem.X86_64
