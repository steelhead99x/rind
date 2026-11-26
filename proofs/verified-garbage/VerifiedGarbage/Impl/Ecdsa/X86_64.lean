module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Inv
public import VerifiedGarbage.Impl.Weierstrass.X86_64.TCombJ
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Spec.Ecdsa
public import VerifiedGarbage.Impl.Weierstrass.Layout.Mul
public import VerifiedGarbage.Impl.Weierstrass.Layout.Inverse
public import VerifiedGarbage.Impl.Weierstrass.Layout.CheckPoint

/-!
# ECDSA signing on x86-64

`vg_ecdsa_<curve>_sign(out = rdi, d = rsi, digest = rdx, k = rcx,
scratch = r8) -> eax`, for a curve whose field elements and scalars are `n`
64-bit words (`n = 4` for the 256-bit curves, at most 6), from the code of
`Impl/Weierstrass/X86_64.lean`:

1. the callee-saved registers are saved in the working space, whose base is
   then `rdi`, and `out` is kept in `rsi`, which the multiplications leave
   (those of six words use every register from `r8` to `r15`); `k`, `d` and
   the hash are read big-endian into slots,
   and the constants (the moduli, `a`, `3b`, `G` and Montgomery's ones in
   Montgomery form, `R² mod n`, and the exponents `p - 2` and `n - 2`) are
   stored as immediates;
2. the bits of `k`, `p - 2` and `n - 2` are expanded into tables;
3. `R = [k]G` by the fixed-base comb from the curve's tables in a `static`
   (`Impl/Weierstrass/X86_64/TComb.lean`, its additions those for `a = -3`,
   with `b R mod p` in `EM`), for a curve that has them, else
   by the ladder from `R = O = (0 : 1 : 0)`, then
   `x = X Z^(p-2)` (Montgomery's form left by a multiplication by 1) and
   `r = x mod n` (a conditional subtraction, as `x < p < 2n`);
4. `s = k^(n-2) (e + r d) mod n`, in Montgomery form modulo `n`, then left;
   the powers `Z^(p-2)` and `k^(n-2)` are inverses by divsteps
   (`Impl/Weierstrass/X86_64/Inv.lean`) for a curve of up to nine words
   (`k^(n-2)` if `fastN`), their working area past the tables of bits, else
   powers from the tables of the exponents' bits (`pPow`, `nPow`);
5. the flag: `d` and `k` in `[1, n-1]`, `r ≠ 0` and `s ≠ 0`, as a mask, which
   selects `r ‖ s` or zeros for `out` (big-endian), and is returned as 0 or 1.

`R = O` (impossible for `k` in `[1, n-1]`) gives `Z = 0`, so `x = 0` and
`r = 0`, as the specification says. Everything is computed whatever the
flag, and only the pointers may affect timing.
-/

@[expose] public section

namespace VG.Impl.Ecdsa.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass

/-- `-m⁻¹ mod 2⁶⁴`, for odd `m`, by Newton's iteration. -/
def minv (m : Nat) : Nat :=
  let inv := (List.range 6).foldl (fun x _ => x * ((2 + 2 ^ 64 - m * x % 2 ^ 64) % 2 ^ 64) % 2 ^ 64) 1
  (2 ^ 64 - inv) % 2 ^ 64

/-- The working space: the saved registers in bytes `[0, 48)`, then
slots of `n` words (`slot n i`), then the tables of bits (`bitsAt`). -/
def slot (n i : Nat) : Nat := 64 + 8 * n * i

/-! Slot numbers. -/
def MP := 0
def MN := 1
def TMP := 2
def ZERO := 3
def ONE := 4
def ONEP := 5
def AP := 6
def B3P := 7
def GX := 8
def GY := 9
def R2N := 10
def ONEN := 11
def EXPP := 12
def EXPN := 13
def RX := 14
def RY := 15
def RZ := 16
def DX := 17
def DY := 18
def DZ := 19
def TX := 20
def TY := 21
def TZ := 22
def T0 := 23
def T1 := 24
def T2 := 25
def T3 := 26
def T4 := 27
def T5 := 28
def ACC := 29
def PT := 30
def K := 31
def D := 32
def E := 33
def XM := 34
def X := 35
def RR := 36
def KM := 37
def RM := 38
def DM := 39
def EM := 40
def TT := 41
def SM := 42
def SS := 43
def FLAG := 44
/-- The number of slots. -/
def nslots := 45

/-- The table of the bits of `k` (`j = 0`), `p - 2` (1) and `n - 2` (2): `64 n`
bytes each, and a word of zeros past them that the comb's last digit may
read. -/
def bitsAt (n j : Nat) : Nat := slot n nslots + (64 * n + 8) * j

/-- The window method's slots, past the tables of bits (over the inversion's
working area, which each inversion initializes): `k + offset J`
(`n + 1` words, two slots), the table of its bits (`64 (n + 1)` bytes, ten
slots) and, past slot `83` (the temporary area for six words, `sl`), the
table of points `[1 … 8]P` (24 slots), below `8192` bytes for up to nine
words. -/
def WK : Nat := 71
def WB : Nat := 73
def WT : Nat := 84

/-- A fixed-base comb for `G`: its digits' width `w`, its tables
(`tbl[j][m - 1]` is `[m 2^(w j)]G`, affine, for `j < combJ` and
`m = 1 … 2^(w-1)`), its starting point `[2^(w-1) Σ_j 2^(wj)]G`, and the
name of the `static` holding the tables (`Artifact.consts`). -/
structure CombData where
  w : Nat
  tbl : List (List (Nat × Nat))
  start : Nat × Nat
  tsym : String
  /-- Whether the comb adds Booth's digits by Jacobian mixed additions
  (`TCombCfg.combJ`), else by the complete ones (`TCombCfg.comb`). -/
  jac : Bool := false
  /-- Whether that comb selects each window's entry during the previous
  window's addition, where it selects with AVX2 (`TCombCfg.pipe`). -/
  pipe : Bool := false

/-- A curve as the code has it: `n` words, its parameters, and the comb for
`G`, if it has one (else `[k]G` is by the ladder). -/
structure Cfg where
  n : Nat
  C : Spec.Weierstrass.Curve
  comb : Option CombData := none
  /-- Use the variable-base window formulas for `a = -3`; otherwise use
  the general complete-addition ladder. -/
  windows : Bool := true
  /-- Whether `k^(n-2)` is by divsteps (the proofs need `n` prime), else by the power. -/
  fastN : Bool := false
  /-- Whether to multiply modulo `p` and `n` with BMI2 and ADX (`Mod.adx`). -/
  adx : Bool := false
  /-- Whether the comb selects its entries 32 bytes at a time, with AVX2
  (`TCombCfg.avx2`). -/
  avx2 : Bool := false
  /-- Whether verification reads the comb's entries for `[u]G` by direct,
  public lookups (`u` is public) and compares `x mod n` with `r` in
  projective coordinates, without inverting `Z` (which needs `n < p ≤ 2n`). -/
  pubVerify : Bool := false
  /-- The table of `[m]G`, `m = 1 … 2^(w-1)`, that verification's generator
  digits of width `w = d.w` index, when they do not index the comb's first
  row: a comb of one window (`d.tbl` its one row), in the tables of constants
  (`combConsts`). -/
  gtab : Option CombData := none
  /-- Whether the loops that run the most products modulo `p`, the comb's
  and the joint verifier's, write them out (`Mod.inl`, `MH`) where the
  others call the function computing them. -/
  hot : Bool := false
  /-- The curve whose function `vg_<curve>_mul_base`
  (`Proof/Weierstrass/MulBaseContract.lean`) computes `[k]G` (`mulBaseFn`), which the
  signature and public key derivation call, with the table of `k`'s bits it
  makes; else they run them inline. -/
  mulBase : Option Impl.Weierstrass.MulBase.Curve := none
  /-- For a curve without a comb, the curve whose `vg_<curve>_mul`
  (`Proof/Weierstrass/MulContract.lean`) computes `[k]Q` by the ladder (`mulFn`),
  which the signature, the public key, ECDH and verification call, if any. -/
  mul : Option Impl.Weierstrass.Mul.Curve := none
  /-- The curve whose functions `vg_<curve>_inv_mod_p` and
  `vg_<curve>_inv_mod_n` (`Proof/Weierstrass/InverseContract.lean`) compute `Z^(p-2)`
  and `k^(n-2)` (`invFn`), which every function calls (`pPow`, `nPow`);
  else they run them inline. -/
  inverse : Option Impl.Weierstrass.Inverse.Curve := none
  /-- The curve whose function `vg_<curve>_check_point`
  (`Proof/Weierstrass/CheckPointContract.lean`) checks the public point and selects
  the point ECDH and verification multiply (`Ecdh.X86_64.Cfg.check`); else
  they run it inline. -/
  checkPoint : Option Impl.Weierstrass.CheckPoint.Curve := none
  /-- The bits the window method's scalars have: `8 len`, but for a curve
  whose `n` has fewer bits than its `len` bytes (P-521's `n < 2⁵²¹`, in 66
  bytes), as many as `n` has. ECDH reduces its `d` below `2^nbits` before
  the window method (`Impl.Ecdh.X86_64.Cfg.maskK`); a `d` it changes is out
  of range, and its result is discarded. -/
  nbits : Nat := 8 * C.len

/-- The bits of `e < 2^k`: the least `j ≤ k` with `e < 2^j`. -/
def bitLen (e : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if e < 2 ^ k then bitLen e k else k + 1

namespace Cfg

variable (c : Cfg)

/-- `R = 2^(64 n)`. -/
def R : Nat := 2 ^ (64 * c.n)

/-- The bits of the hash's `len` bytes that are not `e`'s: `8 len - N`, for
`N` the bits of `n` (0 but for P-521's 7). -/
def sh : Nat := 8 * c.C.len - Spec.Ecdsa.nBits c.C

/-- `x R mod p`. -/
def mont (x : Nat) : Nat := x * c.R % c.C.p

/-- Slot `i`; for nine words (P-521) and six (P-384), whose products modulo
`p` are calls of a function (`Mont.callOf`), the temporary area (`TMP`) is in
that function's own working space, which a call changes: for nine words in
slot `55`'s place (`Mont.fnTmp`), over the table of the bits of `p - 2`
(`bitsAt 1`), which only the power `pow` reads, for more than nine words; for
six in slot `83`'s (`Mont.fnTmp6`), between the window method's table of bits
and its table of points. Slot `55` or `83` (which nothing uses) is in its
place, so that distinct slots stay apart. -/
def sl (i : Nat) : Nat :=
  slot c.n (if c.n = 9 then (if i = TMP then 55 else if i = 55 then TMP else i)
    else if c.n = 6 then (if i = TMP then 83 else if i = 83 then TMP else i) else i)

def MP' : Mod :=
  { n := c.n, mo := c.sl MP, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.p), red := Red.ofModulus c.n c.C.p,
    adx := c.adx, sparse := sparseOk c.n c.C.p }
/-- `MP'`, but written out in the loops that run the most products (`hot`). -/
def MH : Mod := { c.MP' with inl := c.hot }
def MN' : Mod :=
  { n := c.n, mo := c.sl MN, tmp := c.sl TMP, minv := BitVec.ofNat 64 (minv c.C.n), adx := c.adx,
    fnN := fnNOk c.n c.C.n }


/-- Shared products use the high temporary slot after the order inversion has
consumed its exponent table: for eight words, slot 62 overlaps that table.
Scalar multiplication and inversion retain their original scratch layout. -/
def sharedMod (M : Mod) (m : Nat) : Mod :=
  { M with tmp := if c.n = 8 then c.sl 62 else M.tmp, fnMod := some m }

def MPS : Mod := c.sharedMod c.MP' c.C.p
def MNS : Mod := c.sharedMod c.MN' c.C.n

/-- Field products after inversion: share eight-word multiplication. -/
def mulPS (o a b : Nat) : Prog isa :=
  if c.n = 8 then opProg c.MPS (.mul o a b) else .block (Mont.X86_64.mul c.MPS o a b)

def pt (x y z : Nat) : Pt := ⟨c.sl x, c.sl y, c.sl z⟩

def rcbSlots : RcbSlots := ⟨c.sl AP, c.sl B3P, c.sl T0, c.sl T1, c.sl T2, c.sl T3, c.sl T4, c.sl T5⟩

def ladderCfg : LadderCfg where
  M := c.MP'
  S := c.rcbSlots
  G := c.pt GX GY ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := c.pt TX TY TZ
  bits := bitsAt c.n 0
  nbits := 64 * c.n

/-- The comb's digits: `combJ` of `w` bits cover the scalar's `64 n`. -/
def combJ (w : Nat) : Nat := (64 * c.n + w - 1) / w

/-- The comb for `[k]G`, into `R`, from the table of the bits of `k` and the
curve's tables of constants, the `static` `d.tsym` (`Artifact.consts`), with
`b R mod p` in `EM` (free until `scalar`). Its addition for `a = -3` does
not read `a`, whose slot is `EM`'s too, so that the comb reads only `p`,
zero and what it writes itself (`vg_<curve>_mul_base`). -/
def combCfg (d : CombData) : TCombCfg where
  M := c.MH
  S := { c.rcbSlots with a := c.sl EM, b3 := c.sl EM }
  A := c.pt RX RY RZ
  E := c.pt TX TY TZ
  D := c.pt DX DY DZ
  neg := c.sl PT
  zero := c.sl ZERO
  bits := bitsAt c.n 0
  kbytes := 64 * c.n
  tsym := d.tsym
  w := d.w
  J := c.combJ d.w
  start := (c.mont d.start.1, c.mont d.start.2)
  one := c.mont 1
  avx2 := c.avx2
  pipe := d.pipe && c.avx2

/-- The comb's tables, in memory (`Artifact.consts`). -/
def combWords (d : CombData) : List (BitVec 64) := tcombWords c.n c.R c.C.p d.tbl

/-- The tables of constants of the functions that run the comb
(`Artifact.consts`): none without one. -/
def combConsts : List (String × List (BitVec 64)) :=
  match c.comb, c.gtab with
  | some d, none => [(d.tsym, c.combWords d)]
  | none, none => []
  | some d, some g => [(d.tsym, c.combWords d), (g.tsym, c.combWords g)]
  | none, some g => [(g.tsym, c.combWords g)]

/-- `R = [k]G`, from the table of the bits of `k`: by the comb (with `b R mod p`
in `EM` for its complete addition for `a = -3`), or the ladder.
`publicLookup` permits direct table lookup only for public scalars. -/
def gMul (publicLookup : Bool := false) : Prog isa :=
  match c.comb with
  | some d => .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) (TCombCfg.comb (c.combCfg d) publicLookup)
  | none => ladder c.ladderCfg

/-- `R = [k]G` for a secret `k`: as `gMul`, but by the comb with Booth's digits
and Jacobian mixed additions (`TCombCfg.combJ`) for a curve whose comb has
them (`jac`). -/
def gMulK : Prog isa :=
  match c.comb with
  | some d => if d.jac then .seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) (TCombCfg.combJ (c.combCfg d))
      else c.gMul
  | none => c.gMul

def powP : PowCfg := ⟨c.MP', c.sl ACC, c.sl PT, c.sl RZ, c.sl ONEP, bitsAt c.n 1, 64 * c.n⟩
/-- The power mod `n` from the top bit of `n - 2` (its `bitLen` bits), not of its
`64 n` bits' table. -/
def powN : PowCfg := ⟨c.MN', c.sl ACC, c.sl PT, c.sl KM, c.sl ONEN, bitsAt c.n 2, bitLen (c.C.n - 2) (64 * c.n)⟩

/-- The inversions by divsteps, their working area past the tables of bits. -/
def invP : InvCfg := .ofMod c.MP' (c.sl ACC) (c.sl RZ) (bitsAt c.n 3) c.C.p
def invN : InvCfg := .ofMod c.MN' (c.sl ACC) (c.sl KM) (bitsAt c.n 3) c.C.n

/-- The window method's digits, for scalars below `2^nbits` (ECDH's `d`
reduced by `maskK`, or verification's `v < n`): `⌈(nbits + 2) / 4⌉`, enough
for the recoding's carry; `2 len + 1` when `nbits = 8 len`. -/
def winJ : Nat := (c.nbits + 5) / 4

/-- The window method's areas. -/
def winK : Nat := c.sl WK
def winBits : Nat := c.sl WB
def winTbl : Nat := c.sl WT

/-- The window method for `[k]P`, `P` at `px`, `py`, `ONEP`, into `R`, from the
scalar at `k`'s slot, with `b R mod p` at `bm` for the complete addition for
`a = -3`. -/
def winCfg (px py bm : Nat) : WinCfg where
  M := c.MH
  S := { c.rcbSlots with b3 := c.sl bm }
  P := c.pt px py ONEP
  R := c.pt RX RY RZ
  E := c.pt TX TY TZ
  D := c.pt DX DY DZ
  neg := c.sl PT
  zero := c.sl ZERO
  bits := c.winBits
  tbl := c.winTbl
  J := c.winJ
  one := c.mont 1

/-- `k + offset J` and its bits, from the slot at `k`. -/
def winPrep (k : Nat) : Prog isa :=
  .seq (.block (WinCfg.addConst c.n k c.winK (WinCfg.offset c.winJ)))
    (bits c.winK c.winBits (8 * (c.n + 1)))

/-- `Z^(p-2)` and `k^(n-2)` into `ACC`, inline: by divsteps for up to nine
words (`k^(n-2)` only if `fastN`), else by the powers. -/
def pPowI : Prog isa := if c.n ≤ 9 then InvCfg.inv c.invP else pow c.powP
def nPowI : Prog isa := if c.fastN ∧ c.n ≤ 9 then InvCfg.inv c.invN else pow c.powN

/-- The callee-saved registers, and where they are saved. -/
def saved : List (Reg × Nat) := [(.rbx, 0), (.rbp, 8), (.r12, 16), (.r13, 24), (.r14, 32), (.r15, 40)]

/-- Where `vg_<curve>_inv_mod_p` and `_n` keep the callee-saved registers,
which they change: `PT`'s slot, part of their own working space. -/
def invSaved : List (Reg × Nat) := saved.map fun (r, d) => (r, c.sl PT + d)

/-- The inversion `body` between saving the callee-saved registers in `PT`'s
slot and restoring them: for six words or more, whose slot holds them. -/
def invFnS (body : Prog isa) : Prog isa :=
  .seq (.block (c.invSaved.map fun p => .store { base := .rdi, disp := p.2 } p.1)) <|
  .seq body <|
  .block (c.invSaved.map fun p => .mov p.1 (.mem { base := .rdi, disp := p.2 }))

/-- The callee-saved registers, and the `xmm` register each is kept in by
the functions of four words, which write no vector register. -/
def invKeptX : List (Reg × XReg) :=
  [(.rbx, .xmm0), (.rbp, .xmm1), (.r12, .xmm2), (.r13, .xmm3), (.r14, .xmm4), (.r15, .xmm5)]

/-- A function's `body` between copying the callee-saved registers into
`xmm0`–`xmm5` and back: for four words. -/
def invFnX (body : Prog isa) : Prog isa :=
  .seq (.block (invKeptX.map fun (r, x) => .xop (.movq x r))) <|
  .seq body <|
  .block (invKeptX.map fun (r, x) => .movqR r x)

/-- `vg_<curve>_inv_mod_p` or `_n` (`_adx` with BMI2 and ADX): the inversion
`body`, keeping the callee-saved registers in `PT`'s slot (`invFnS`), or in
`xmm` registers for fewer than six words (`invFnX`). -/
def invFn (body : Prog isa) : Prog isa := if c.n < 6 then invFnX body else c.invFnS body

/-- The suffix of the functions' names: `_adx` with BMI2 and ADX. -/
def fnSuffix : String := if c.adx then "_adx" else ""

/-- The suffix of `vg_<curve>_inv_mod_n`'s name: `fnSuffix`, but none for nine
words, whose products modulo `n` use neither BMI2 nor ADX (`Mont.X86_64.mul`),
so that both configurations call the one function. -/
def nSuffix : String := if c.n = 9 then "" else c.fnSuffix

/-- `Z^(p-2)` and `k^(n-2)` into `ACC`: calls of `vg_<curve>_inv_mod_p` and
`_n` (`invFn`), else inline (`pPowI`, `nPowI`). -/
def pPow : Prog isa :=
  match c.inverse with
  | some C => .call (s!"vg_{C.curve}_inv_mod_p" ++ c.fnSuffix) (c.invFn c.pPowI)
  | none => c.pPowI
def nPow : Prog isa :=
  match c.inverse with
  | some C => .call (s!"vg_{C.curve}_inv_mod_n" ++ c.nSuffix) (c.invFn c.nPowI)
  | none => c.nPowI

/-- The constants, and `R = (0 : 1 : 0)`: slots and values. -/
def consts : List (Nat × Nat) :=
  [(MP, c.C.p), (MN, c.C.n), (ZERO, 0), (ONE, 1), (ONEP, c.mont 1), (AP, c.mont c.C.a),
    (B3P, c.mont (3 * c.C.b)), (GX, c.mont c.C.gx), (GY, c.mont c.C.gy), (R2N, c.R * c.R % c.C.n),
    (ONEN, c.R % c.C.n), (EXPP, c.C.p - 2), (EXPN, c.C.n - 2), (RX, 0), (RY, c.mont 1), (RZ, 0)]

/-- Slot `hs`, if any, shifted right by `sh`. -/
def shiftCode (hs : Option Nat) : List Instr :=
  match hs with
  | some i => if c.sh = 0 then [] else shrWords c.n (c.sl i) c.sh
  | none => []

/-- Saves them, with the working space in `r8`, which then goes to `rdi`
(`out` going to `r14` meanwhile); reads `k`, `d` and the hash, and shifts
the number in slot `hs`, if any, right by `sh`, the bits of a hash that are
not `e`'s; stores the constants; sets `R = (0 : 1 : 0)` and the flag to all
ones; and keeps `out` in `rsi`, which nothing after it writes (the
multiplications of six words use `r14`). -/
def setupWith (hs : Option Nat) : List Instr :=
  saved.map (fun (r, d) => .store { base := .r8, disp := (d : Int) } r) ++
  ([.mov .r14 (.reg .rdi), .mov .rdi (.reg .r8)] : List Instr) ++
  loadBytes c.C.len c.n (c.sl K) .rcx ++ loadBytes c.C.len c.n (c.sl D) .rsi ++
  loadBytes c.C.len c.n (c.sl E) .rdx ++
  c.shiftCode hs ++
  c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  setConst 1 (c.sl FLAG) (2 ^ 64 - 1) ++ ([.mov .rsi (.reg .r14)] : List Instr)

/-- The signature's setup: the hash, `e`, in slot `E`. -/
def setup : List Instr := c.setupWith (some E)

/-- The mask `rdx` of `[a] ≠ 0` (all ones if it is not zero). -/
def nonzero (a : Nat) : List Instr :=
  ([.mov .rdx (.mem (sc a))] : List Instr) ++ ((List.range (c.n - 1)).map fun j => .alu .or .rdx (.mem (sc (a + 8 * (j + 1))))) ++
  ([.mov32 .rcx (.imm 0), .alu .sub .rcx (.reg .rdx), .alu .sbb .rdx (.reg .rdx)] : List Instr)

/-- The mask `rax` of `[a] < n` (all ones if it is), through `rdx`. -/
def ltN (a : Nat) : List Instr :=
  ((List.range c.n).flatMap fun j =>
    [.mov .rdx (.mem (sc (a + 8 * j))), .alu (if j = 0 then .sub else .sbb) .rdx (.mem (sc (c.sl MN + 8 * j)))]) ++
  ([.alu .sbb .rax (.reg .rax)] : List Instr)

/-- The flag `&=` the mask `rdx`. -/
def andFlag : List Instr :=
  [.mov .rax (.mem (sc (c.sl FLAG))), .alu .and .rax (.reg .rdx), .store (sc (c.sl FLAG)) .rax]

/-- `[a]` is in `[1, n-1]`: the flag `&=` both masks. -/
def checkRange (a : Nat) : List Instr :=
  c.ltN a ++ ([.mov .rbp (.reg .rax)] : List Instr) ++ c.nonzero a ++ ([.alu .and .rdx (.reg .rbp)] : List Instr) ++ c.andFlag

/-- `[a] ≠ 0`: the flag `&=` its mask. -/
def checkNonzero (a : Nat) : List Instr := c.nonzero a ++ c.andFlag

/-- A product modulo `p` of the signature's and the public key's finish: a call of
`vg_<curve>_mul_mod_p` where `opProg` makes one, but inline for P-521, whose
signature and public key measured slower with the calls. -/
def mulPF (o a b : Nat) : Prog isa :=
  if c.n = 9 then .block (Mont.X86_64.mul c.MP' o a b) else opProg c.MP' (.mul o a b)

/-- `x = X Z⁻¹`, `r = x mod n`, `k R mod n`, and the checks of `d`, `k`, `r`. -/
def middle : Prog isa :=
  progs [c.mulPF (c.sl XM) (c.sl RX) (c.sl ACC),
    c.mulPF (c.sl X) (c.sl XM) (c.sl ONE),
    .block (Mont.X86_64.add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO)),
    opProg c.MN' (.mul (c.sl KM) (c.sl K) (c.sl R2N)),
    .block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))]

/-- `r ‖ s` (or zeros) to `out`, the flag's low bit to `rax`, and the
callee-saved registers restored. -/
def finish : List Instr :=
  ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
  storeBytes c.C.len c.n .rsi 0 (c.sl RR) ++ storeBytes c.C.len c.n .rsi c.C.len (c.sl SS) ++
  ([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
  saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- `s = k⁻¹ (e + r d) mod n`, with `k⁻¹ R` in `ACC`, and its check. -/
def scalar : Prog isa :=
  progs [opProg c.MNS (.mul (c.sl RM) (c.sl RR) (c.sl R2N)),
    opProg c.MNS (.mul (c.sl DM) (c.sl D) (c.sl R2N)),
    opProg c.MNS (.mul (c.sl EM) (c.sl E) (c.sl R2N)),
    opProg c.MNS (.mul (c.sl TT) (c.sl RM) (c.sl DM)),
    .block (Mont.X86_64.add c.MN' (c.sl TT) (c.sl TT) (c.sl EM)),
    opProg c.MNS (.mul (c.sl SM) (c.sl ACC) (c.sl TT)),
    opProg c.MNS (.mul (c.sl SS) (c.sl SM) (c.sl ONE)),
    .block (c.checkNonzero (c.sl SS) ++ c.finish)]

/-- `vg_<curve>_mul_base`'s body: the table of `k`'s bits, then `[k]G` into
`R` (`gMulK`). -/
def mulBaseBody : Prog isa := .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) c.gMulK

/-- Where `vg_<curve>_mul_base` keeps the callee-saved registers, which it
changes: `ACC`'s slot, part of its own working space, and for fewer than six
words, which it cannot hold, the rest in `TT`'s, also its own. -/
def mulBaseSaved : List (Reg × Nat) :=
  saved.map fun (r, d) => (r, if d < 8 * c.n then c.sl ACC + d else c.sl TT + (d - 8 * c.n))

/-- The slots `vg_<curve>_mul_base` writes besides `gMulK`'s: where it keeps
the callee-saved registers (`mulBaseSaved`). -/
def mulBaseSlots : List Nat := if c.n < 6 then [ACC, TT] else [ACC]

/-- `vg_<curve>_mul_base` (`_adx` with BMI2 and ADX): its body, between
saving the callee-saved registers in `ACC`'s slot and restoring them. -/
def mulBaseFn : Prog isa :=
  .seq (.block (c.mulBaseSaved.map fun p => .store { base := .rdi, disp := p.2 } p.1)) <|
  .seq c.mulBaseBody <|
  .block (c.mulBaseSaved.map fun p => .mov p.1 (.mem { base := .rdi, disp := p.2 }))

/-- The ladder of `vg_<curve>_mul`: the signature's, with its point at `ACC`,
`PT` (its copy of `Q`), `ONEP`. -/
def mulLadder : LadderCfg := { c.ladderCfg with G := c.pt ACC PT ONEP }

/-- `vg_<curve>_mul`'s body: the table of `k`'s bits, `Q` (in `R`'s first two
slots) copied to `ACC` and `PT`, `R` the point at infinity (from zero and
one), then `R = [k]Q` by the ladder, with the formulas for `a = 0` if the
curve's `a` is zero (`Q` is affine). -/
def mulBody : Prog isa :=
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (.block (copy c.n (c.sl ACC) (c.sl RX) ++ copy c.n (c.sl PT) (c.sl RY) ++
    copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO)))
    (ladder c.mulLadder (c.C.a == 0))

/-- `vg_<curve>_mul`: its body, which writes no vector register, between
copying the callee-saved registers to `xmm0`–`xmm5` and back (`invFnX`). -/
def mulFn : Prog isa := Cfg.invFnX c.mulBody

/-- The signature and the public key call a function that makes the table of
`k`'s bits: `vg_<curve>_mul_base` or `vg_<curve>_mul`. -/
def callsMul : Bool := c.mulBase.isSome || c.mul.isSome

/-- The table of `k`'s bits, but nothing if `skip`. -/
def kBitsIf (skip : Bool) : Prog isa :=
  if skip then .block [] else bits (c.sl K) (bitsAt c.n 0) (8 * c.n)

/-- The table of `k`'s bits, unless `vg_<curve>_mul_base` or `vg_<curve>_mul`
makes it. -/
def kBits : Prog isa := c.kBitsIf c.callsMul

/-- `R = [k]G` for a secret `k`, from the table of its bits made by `kBits`:
a call of `vg_<curve>_mul_base` (or `_adx`) or `vg_<curve>_mul` (with `G`
copied to `R`'s slots), which make the table themselves, else inline
(`gMulK`). -/
def gMulKC : Prog isa :=
  match c.mulBase, c.mul with
  | some C, _ => .call (s!"vg_{C.curve}_mul_base" ++ if c.adx then "_adx" else "") c.mulBaseFn
  | none, some C => .seq (.block (copy c.n (c.sl RX) (c.sl GX) ++ copy c.n (c.sl RY) (c.sl GY)))
      (.call s!"vg_{C.curve}_mul" c.mulFn)
  | none, none => c.gMulK

/-- `vg_ecdsa_<curve>_sign`. -/
def sign : Prog isa :=
  .seq (.block c.setup) <|
  .seq c.kBits <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) <|
  .seq c.gMulKC <|
  .seq c.pPow <|
  .seq c.middle <|
  .seq c.nPow c.scalar

end Cfg

end VG.Impl.Ecdsa.X86_64
