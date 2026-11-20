module
public import VerifiedGarbage.TCB.X86_64.Isa


/-!
# ML-KEM on x86-64: SSE2 code as AVX2 code

The AVX2 code of ML-KEM computes on sixteen words at a time, eight in each
128-bit lane of a `ymm` register, and in each lane does what the SSE2 code
does to an `xmm` register (`Vec.lean`): it is the SSE2 code with each
instruction replaced by its VEX.256 form, and a move to a register followed
by an instruction on it merged into one three-operand instruction (`toY`):
`movdqa d, a; op d, b` becomes `vop d, a, b` (unless `b` is `d`).

`yconst r v` sets each doubleword of `ymm r` to `v`, through `rax`.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The VEX-encoded instruction that does to each lane what an SSE
instruction does, if there is one. -/
def vexOf : XBinOp → Option VBinOp
  | .paddd => some .vpaddd | .paddq => some .vpaddq | .pxor => some .vpxor | .por => some .vpor
  | .pand => some .vpand | .pandn => some .vpandn | .pshufb => some .vpshufb | .pmuludq => some .vpmuludq
  | .punpckldq => some .vpunpckldq | .punpckhdq => some .vpunpckhdq
  | .punpcklqdq => some .vpunpcklqdq | .punpckhqdq => some .vpunpckhqdq
  | .paddw => some .vpaddw | .psubw => some .vpsubw | .psubd => some .vpsubd | .pmullw => some .vpmullw
  | .pmulhw => some .vpmulhw | .packssdw => some .vpackssdw | .punpcklwd => some .vpunpcklwd
  | .punpckhwd => some .vpunpckhwd | .psubq => some .vpsubq | .pmaddwd => some .vpmaddwd
  | .pmulhrsw => some .vpmulhrsw
  | _ => none

/-- `op d, b` in VEX.256 form on `a` (`vop d, a, b`), if it has one. -/
def ybin (op : XBinOp) (d a b : XReg) : Instr :=
  match (vexOf op) with
  | some v => .vop (.vbin v .l256 d a b)
  | none => .xop (.bin op d b)

/-- A pending `movdqa d, a`, as AVX2 code. -/
def flushY : Option (XReg × XReg) → List Instr
  | none => []
  | some (d, a) => [.vop (.vmovdqa .l256 d a)]

/-- One SSE2 instruction as AVX2 code, after the pending move `p`, if any:
the new pending move and the code. -/
def stepY (p : Option (XReg × XReg)) : Instr → Option (XReg × XReg) × List Instr
  | .xop (.bin .movdqa d a) => (some (d, a), flushY p)
  | .xop (.bin op d b) =>
    match p with
    | some (d', a) => if (vexOf op).isSome ∧ d' = d ∧ b ≠ d then (none, [ybin op d a b])
      else (none, flushY p ++ [ybin op d d b])
    | none => (none, [ybin op d d b])
  | .xop (.shift op d n) =>
    match p with
    | some (d', a) => if d' = d then (none, [.vop (.vshift op .l256 d a n)])
      else (none, flushY p ++ [.vop (.vshift op .l256 d d n)])
    | none => (none, [.vop (.vshift op .l256 d d n)])
  | .xop (.pshufd d a o) => (none, flushY p ++ [.vop (.vpshufd .l256 d a o)])
  | i => (none, flushY p ++ [i])

/-- `toY` after the pending move `p`. -/
def toYAux : Option (XReg × XReg) → List Instr → List Instr
  | p, [] => flushY p
  | p, i :: rest => (stepY p i).2 ++ toYAux (stepY p i).1 rest

/-- SSE2 code on `xmm` registers as AVX2 code on each lane of `ymm` registers. -/
def toY (is : List Instr) : List Instr := toYAux none is

/-- Each doubleword of `ymm r` set to `v`, through `rax`. -/
def yconst (r : XReg) (v : BitVec 32) : List Instr :=
  [.mov32 .rax (.imm v), .vop (.vmovq r .rax), .vop (.vpbroadcastd .l256 r r)]

/-- `q` in the words of `ymm15` and `q⁻¹ mod 2¹⁶` in those of `ymm14`. -/
def yconsts : List Instr := yconst .xmm15 0x0D010D01 ++ yconst .xmm14 0xF301F301

end VG.Impl.MlKem.X86_64
