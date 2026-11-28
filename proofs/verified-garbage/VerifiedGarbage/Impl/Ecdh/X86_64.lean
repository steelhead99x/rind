module

public import VerifiedGarbage.Impl.Ecdsa.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacA
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOddP
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowJ

/-!
# ECDH on x86-64

`vg_ecdh_<curve>(out = rdi, d = rsi, peer = rdx, scratch = rcx) -> eax`,
for a curve of `n` 64-bit words, from the code of ECDSA's signature
(`Impl/Ecdsa/X86_64.lean`), whose layout of the working space it uses:

1. `scratch` to `r8`, `peer` to `r9`, `d`'s pointer to `rcx` (the
   signature's `k`) and `peer + 1` to `rdx` (its hash); then the
   signature's setup and tables of bits, unchanged: `d` is read into the
   slots of `k` and `d`, the peer's `x` into that of the hash;
2. `R² mod p` and `b R mod p` to slots of their own, the peer's `y` to
   another, and into the flag the masks of the peer's first byte being
   `04`, `x < p` and `y < p`;
3. `x` and `y` into Montgomery's form, and the mask of `y² = x³ + a x + b`
   into the flag;
4. the peer's point, or `G` if the flag is clear (so the scalar
   multiplication always runs on a point of the curve), to the slots it takes
   its point from;
5. `[d]P` by signed 4-bit windows for up to nine words (`WinCfg.window`, its
   table of `[1 … 8]P` past the tables of bits, with `b R mod p`
   for the complete addition for `a = -3`), else by the signature's ladder,
   and `Z^(p-2)` by its inversion (or power);
6. `x = X Z^(p-2)`, out of Montgomery's form, and the masks of `d` in
   `[1, n-1]` and `Z ≠ 0` into the flag, which selects `x` or zeros for
   `out` (big-endian) and is returned as 0 or 1.

Everything is computed whatever the flag, and only the pointers may affect
timing (the contract would let the peer's public key affect it too).
-/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64

/-! Slots of the signature's layout, as ECDH uses them. The hash's slot `E`
holds the peer's `x`. -/

/-- The peer's `y`. -/
def QY : Nat := RR
/-- `R² mod p`. -/
def R2P : Nat := DM
/-- `b R mod p`. -/
def BP : Nat := EM
/-- `x R mod p`. -/
def QXM : Nat := XM
/-- `y R mod p`. -/
def QYM : Nat := X
/-- Temporaries of the check that the peer's point is on the curve. -/
def W0 : Nat := KM
def W1 : Nat := TT
def W2 : Nat := SM
def W3 : Nat := RM
/-- The point the ladder multiplies: the peer's, or `G`. -/
def PX : Nat := RM
def PY : Nat := SS

namespace Cfg

variable (c : Impl.Ecdsa.X86_64.Cfg)

/-- `scratch` to `r8`, `peer` to `r9`, `d`'s pointer to `rcx` and
`peer + 1` to `rdx`: the signature's arguments, with `k` and `d` both `d`
and the hash the peer's `x`. -/
def args : List Instr :=
  [.mov .r8 (.reg .rcx), .mov .r9 (.reg .rdx), .mov .rcx (.reg .rsi), .alu .add .rdx (.imm 1)]

/-- The signature's setup, shifting slot `hs` if any (`none` here; the
hash's slot in signature verification), and tables of bits. -/
def prefix' (hs : Option Nat) : Prog isa :=
  .seq (.block (c.setupWith hs)) <|
  .seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) <|
  .seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) <|
  .seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])

/-- The constants ECDH adds to the signature's. -/
def consts : List (Nat × Nat) := [(R2P, c.R * c.R % c.C.p), (BP, c.mont c.C.b)]

/-- The mask `rax` of `[a] < p` (all ones if it is), through `rdx`. -/
def ltP (a : Nat) : List Instr :=
  ((List.range c.n).flatMap fun j =>
    [.mov .rdx (.mem (sc (a + 8 * j))), .alu (if j = 0 then .sub else .sbb) .rdx (.mem (sc (c.sl MP + 8 * j)))]) ++
  ([.alu .sbb .rax (.reg .rax)] : List Instr)

/-- `[a] < p`: the flag `&=` its mask. -/
def checkLtP (a : Nat) : List Instr := ltP c a ++ ([.mov .rdx (.reg .rax)] : List Instr) ++ c.andFlag

/-- The mask `rdx` of `[a] = 0` (all ones if it is). -/
def zero (a : Nat) : List Instr :=
  ([.mov .rdx (.mem (sc a))] : List Instr) ++ ((List.range (c.n - 1)).map fun j => .alu .or .rdx (.mem (sc (a + 8 * (j + 1))))) ++
  ([.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr)

/-- `[a] = 0`: the flag `&=` its mask. -/
def checkZero (a : Nat) : List Instr := zero c a ++ c.andFlag

/-- The peer's first byte is `04`: the flag `&=` its mask. -/
def checkLead : List Instr :=
  ([.movzx8 .rdx { base := .r9 }, .alu .xor .rdx (.imm 4), .alu .cmp .rdx (.imm 1),
    .alu .sbb .rdx (.reg .rdx)] : List Instr) ++ c.andFlag

/-- The constants, the peer's `y`, and the check of its first byte. -/
def peer : List Instr :=
  (consts c).flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
  ([.mov .rdx (.reg .r9), .alu .add .rdx (.imm (BitVec.ofNat 32 (1 + c.C.len)))] : List Instr) ++
  loadBytes c.C.len c.n (c.sl QY) .rdx ++ checkLead c

/-- `y² - (x³ + a x + b)`, from `x R` and `y R`, to `W1`. -/
def curveOps : List FOp :=
  [.mul (c.sl W0) (c.sl QYM) (c.sl QYM), .mul (c.sl W1) (c.sl QXM) (c.sl QXM),
    .mul (c.sl W2) (c.sl W1) (c.sl QXM), .mul (c.sl W1) (c.sl AP) (c.sl QXM),
    .add (c.sl W3) (c.sl W2) (c.sl W1), .add (c.sl W2) (c.sl W3) (c.sl BP),
    .sub (c.sl W1) (c.sl W0) (c.sl W2)]

/-- The point to the ladder's slots: the peer's if the flag is set, else
`G`. -/
def select : List Instr :=
  ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
  sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)

/-- `x` and `y` into Montgomery's form, the check that the point is on the
curve, and the point the ladder multiplies. -/
def validate : Prog isa :=
  blocks ([Mont.X86_64.mul c.MP' (c.sl QXM) (c.sl E) (c.sl R2P),
    Mont.X86_64.mul c.MP' (c.sl QYM) (c.sl QY) (c.sl R2P)] ++
    (curveOps c).map (opCode c.MP') ++ [checkZero c (c.sl W1) ++ select c])

/-- The checks of `x < p` and `y < p`, and `validate`: the body of
`vg_<curve>_check_point` (`Proof/Weierstrass/CheckPointContract.lean`). -/
def checkBody : Prog isa :=
  .seq (.block (checkLtP c (c.sl E) ++ checkLtP c (c.sl QY))) (validate c)

/-- `checkBody`: a call of `vg_<curve>_check_point` (`_adx` with BMI2 and
ADX), which keeps the callee-saved registers in `xmm0`–`xmm5` (`invFnX`),
if the curve has it (`Cfg.checkPoint`), else inline. -/
def check : Prog isa :=
  match c.checkPoint with
  | some C => .call (s!"vg_{C.curve}_check_point" ++ c.fnSuffix) (Impl.Ecdsa.X86_64.Cfg.invFnX (checkBody c))
  | none => checkBody c

/-- The ladder of the signature, from the point at `PX`, `PY`, `ONEP`. -/
def ladderQ : LadderCfg := { c.ladderCfg with G := c.pt PX PY ONEP }

/-- `d` at `K` below `2^nbits` (`Cfg.nbits`), where its `len` bytes hold
more bits: the bits of its top word from `nbits - 64 (n - 1)` cleared,
through `r8`. -/
def maskK : List Instr :=
  if c.nbits < 8 * c.C.len then
    [.mov .r8 (.mem (sc (c.sl K + 8 * (c.n - 1)))),
      .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ (c.nbits - 64 * (c.n - 1)) - 1))),
      .store (sc (c.sl K + 8 * (c.n - 1))) .r8]
  else []

/-- `[d]P` into `R`, for `d` at `K` and `P` at `PX`, `PY`, `ONEP`: by windows for
up to nine words when enabled (`d` reduced below `2^nbits` first), else by the ladder,
calling `vg_<curve>_mul` if the curve has it. -/
def mulQ : Prog isa :=
  if c.n ≤ 9 ∧ c.windows = true then .seq (.block (maskK c)) (.seq (c.winPrep (c.sl K)) (WinCfg.window (c.winCfg PX PY BP)))
  else match c.mul with
    | some C => .seq (.block (copy c.n (c.sl RX) (c.sl PX) ++ copy c.n (c.sl RY) (c.sl PY)))
        (.call s!"vg_{C.curve}_mul" c.mulFn)
    | none => ladder (ladderQ c)

/-- `x` (or zeros) to `out`, the flag's low bit to `rax`, and the
callee-saved registers restored. -/
def finish : List Instr :=
  ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++ storeBytes c.C.len c.n .rsi 0 (c.sl X) ++
  ([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
  Impl.Ecdsa.X86_64.Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- `x = X Z⁻¹`, with `Z⁻¹ R` in `ACC`, out of Montgomery form, the checks
of `d` and `Z`, and the result. -/
def middle : Prog isa :=
  progs [opProg c.MP' (.mul (c.sl XM) (c.sl RX) (c.sl ACC)),
    opProg c.MP' (.mul (c.sl X) (c.sl XM) (c.sl ONE)),
    .block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ finish c)]

/-! ## Windows of 5 bits in Jacobian coordinates, for a curve of prime order -/

/-- The digits of the Jacobian window method, for scalars below `2^nbits`:
`⌈(nbits + 2) / 5⌉`, enough for the recoding's carry. -/
def jwinJ : Nat := (c.nbits + 6) / 5

/-- The Jacobian window method's areas: its scalar and bits where the other
window method's are, its table where that one's starts (16 entries of five
coordinates), and the selected entry past it. -/
def jwinCfg : JacWinCfg where
  M := c.MP'
  S := c.rcbSlots
  P := c.pt PX PY ONEP
  R := c.pt RX RY RZ
  D := c.pt DX DY DZ
  T := c.winTbl + 16 * (40 * c.n)
  neg := c.sl PT
  zero := c.sl ZERO
  bits := c.winBits
  tbl := c.winTbl
  J := jwinJ c
  one := c.mont 1
  avx2 := c.MP'.adx

/-- `d + offset J` and its bits, from the slot of `d`. -/
def jwinPrep : Prog isa :=
  .seq (.block (WinCfg.addConst c.n (c.sl K) c.winK (JacWinCfg.offset (jwinJ c))))
    (bits c.winK c.winBits (8 * (c.n + 1)))

/-- The odd window method's configuration: `jwinCfg`, its windows read from
bit 1 of its table of bits (`JacWinCfg.windowO`). -/
def jwinCfgO : JacWinCfg := { jwinCfg c with bits := c.winBits + 1 }

/-- `k = d` if `d` is odd, else `n - d` (`oddScalar`, in `d`'s slot, through
the window's), then `k + 32^J - 1` and its bits, from the slot of `d`. -/
def jwinPrepO : Prog isa :=
  .seq (.block (oddScalar c.n c.C.n (c.sl K) c.winK ++
      WinCfg.addConst c.n (c.sl K) c.winK (32 ^ jwinJ c - 1)))
    (bits c.winK c.winBits (8 * (c.n + 1)))

/-- `R`'s `y` negated if `d` is even, as `R` is then `[n - d]P = -[d]P`:
`-y` into `PT`'s slot, selected by the mask of `d`'s low bit, from its table
of bits: `b_0 - 1`. -/
def fixSign : List Instr :=
  Mont.X86_64.sub c.MP' (c.sl PT) (c.sl ZERO) (c.sl RY) ++
    [.movzx8 .rcx (sc (bitsAt c.n 0)), .alu .sub .rcx (.imm 1)] ++
    sel c.n (c.sl RY) (c.sl RY) (c.sl PT)

/-- `[d]P` into `R` by odd windows (of `d`, or of `n - d` and then `R`
negated), `dbl` doubling a point in place, each window's selection woven
into the addition before it where that applies (`JacWinCfg.windowOW`). -/
def mulQJO (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block (maskK c)) (.seq (jwinPrepO c) (.seq ((jwinCfgO c).windowOW dbl) (.block (fixSign c))))

/-- The inversion of `mulQJA`'s table: `R.z^(p-2)` into the selected entry's
`X` (`E.x`), its working area that of `invWin`. -/
def invJA : InvCfg := .ofMod c.MP' (jwinCfg c).E.x (c.sl RZ) (bitsAt c.n 2) c.C.p

/-- The words of the window's table of bits within the working area of
`vg_<curve>_inv_mod_p` (`bitsAt c.n 3`, `64 n + 64` bytes), which the call
keeps in the table of the bits of `n - 2`, which ECDH does not read. -/
def invJAWords : Nat := (bitsAt c.n 3 + (64 * c.n + 64) - c.sl WB) / 8

/-- Where the call keeps `PT`'s slot, which `vg_<curve>_inv_mod_p` writes:
past those words. -/
def invJAPt : Nat := bitsAt c.n 2 + 8 * invJAWords c

/-- `invJA` by a call of `vg_<curve>_inv_mod_p` (`Cfg.pPow`, `[ACC] =
[RZ]^(p-2)`), keeping the bytes of the window's slots and table of bits that
the function's own working space covers, then `ACC` into `E.x`. -/
def invJACall : Prog isa :=
  .seq (.block (copy (invJAWords c) (bitsAt c.n 2) (c.sl WB) ++ copy c.n (invJAPt c) (c.sl PT))) <|
  .seq c.pPow <|
  .block (copy c.n (jwinCfg c).E.x (c.sl ACC) ++ copy c.n (c.sl PT) (invJAPt c) ++
    copy (invJAWords c) (c.sl WB) (bitsAt c.n 2))

/-- The inversion of `mulQJA`'s table: a call if the curve has six words and
inversion functions (`Cfg.inverse`), else written out. -/
def invJAProg : Prog isa :=
  if c.n = 6 ∧ c.inverse.isSome then invJACall c else InvCfg.inv (invJA c)

/-- `[d]P` into `R` by the Jacobian window method with the table made affine
(`JacWinCfg.windowA`), `dbl` doubling a point in place. -/
def mulQJA (dbl : Pt → Prog isa) : Prog isa :=
  .seq (.block (maskK c)) (.seq (jwinPrep c) ((jwinCfg c).windowA (invJAProg c) dbl))

/-! ## Windows of 4 bits in Jacobian coordinates, for a curve of prime order

`mulQ`'s windows, but the accumulator in Jacobian coordinates and the table
made affine by one inversion (`WinCfg.windowJ`): for nine words, whose
16-entry table of the 5-bit windows would not fit in the working space. -/

/-- The inversion of `mulQJ4`'s table: `R.z^(p-2)` into the entry's `x`
(`TX`), its working area over the table of the bits of `n - 2`, which ECDH
does not read (and which ends below the window's table of bits for three
words or more). -/
def invWin : InvCfg := .ofMod c.MP' (c.sl TX) (c.sl RZ) (bitsAt c.n 2) c.C.p

/-- `[d]P` into `R` by 4-bit windows with a Jacobian accumulator and an
affine table (`d` reduced below `2^nbits` first). -/
def mulQJ4 : Prog isa :=
  .seq (.block (maskK c))
    (.seq (c.winPrep (c.sl K)) (WinCfg.windowJ (c.winCfg PX PY BP) (InvCfg.inv (invWin c))))

/-- `vg_ecdh_<curve>`, with `mq` computing `[d]P` into `R`. -/
def exchangeWith (mq : Prog isa) : Prog isa :=
  .seq (.block (args)) <| .seq (prefix' c none) <| .seq (.block (peer c)) <| .seq (check c) <|
  .seq mq <| .seq c.pPow (middle c)

/-- `vg_ecdh_<curve>` by odd windows in Jacobian coordinates (`mulQJO`), for
a curve of prime order with `n mod 64 < 33`. -/
def exchangeJO (dbl : Pt → Prog isa) : Prog isa := exchangeWith c (mulQJO c dbl)

/-- `vg_ecdh_<curve>` by the Jacobian window method with an affine table, for
a curve of prime order. -/
def exchangeJA (dbl : Pt → Prog isa) : Prog isa := exchangeWith c (mulQJA c dbl)

/-- `vg_ecdh_<curve>` by 4-bit windows with a Jacobian accumulator
(`mulQJ4`). -/
def exchangeJ4 : Prog isa := exchangeWith c (mulQJ4 c)

/-- `vg_ecdh_<curve>`. -/
def exchange : Prog isa := exchangeWith c (mulQ c)

end Cfg

end VG.Impl.Ecdh.X86_64
