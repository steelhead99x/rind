module

public import VerifiedGarbage.Impl.Sha3.X86_64

/-!
# Keccak-f[1600] on four states at once, in registers: x86-64 with AVX-512VL

The four interleaved states of `X4.lean` (lane `j` of state `k` the `u64`
at byte `32 j + 8 k` of the 800 bytes at `rdi`), held in the thirty-two
`ymm` registers of AVX-512 (`VReg`) for the 24 rounds: each lane in a
register of its own (`lreg`), the five column parities `C[x]` of θ in
`ymm10`–`ymm14` (`creg`) and a temporary in `ymm15` (`T`), with the
EVEX-encoded instructions of `TCB/X86_64/Evex.lean`, each on 256 bits (four
64-bit elements, one per state). A register is copied with `vmovdqa`
(`copy`), which a processor does as it renames registers, without executing
anything; its VEX encoding names only `ymm0`–`ymm15`, so the ten lanes that
are copied (`lowLanes`) are in `ymm0`–`ymm9`, with `creg` and `T` their
destinations, and the other fifteen in `ymm16`–`ymm30`. `permute4R` loads the 25 lanes, runs the rounds, one per iteration
of its loop, and stores them back; it reads the table of round constants
at `rdx` (each in the four elements of a `u256`, as `X4.rcTable` stores it)
up to `rcx`, and so has the interface of `X4.permute4` (it does not use the
second buffer at `rsi`).

A round:

* θ: `C[x]` (a copy of one lane of the column, `colRows`, then
  `vpternlogq` with `0x96`, the XOR of its three operands, twice), then, for
  each `x`, `ROTL¹(C[x + 1])` into `T` (`vprorq` by 63) and each lane
  `(x, y)` XORed with it and `C[x - 1]` (`vpternlogq`, `0x96`);
* ρ and π at once: π is a cycle of the 24 lanes but `(0, 0)` (`piChain`),
  and each of them takes the value of the next, rotated: `T` keeps the
  first, and each `vprorq` writes the rotation of a lane to the register of
  the lane π moves it to, after that one's own value has been moved on;
* χ: in each plane `y`, two lanes, `x = 2y mod 5` and the next (`chiStart`),
  copied to `creg 0` and `creg 1`, and each lane `B[x]`, from the first of
  them on, becomes `B[x] ⊕ (¬B[x+1] ∧ B[x+2])` in place (`vpternlogq` with
  `0xD2`), reading the copies for the lanes already written;
* ι: the round constant at `rdx`, loaded into `T`, XORed into lane 0.

It writes only `rdx`, the flags and the vector registers. Every address is
a pointer plus a constant, and the only branch is the round loop's, so only
the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64.X4R

open VG.X86_64
open VG.Impl.Sha3 (rhoOff piSrc)
open VG.Impl.Sha3.X86_64 (at_)

/-- `ymm i`, for `i < 32`. -/
def vreg (i : Nat) : VReg :=
  match i with
  | 0 => .lo .xmm0 | 1 => .lo .xmm1 | 2 => .lo .xmm2 | 3 => .lo .xmm3 | 4 => .lo .xmm4 | 5 => .lo .xmm5
  | 6 => .lo .xmm6 | 7 => .lo .xmm7 | 8 => .lo .xmm8 | 9 => .lo .xmm9 | 10 => .lo .xmm10
  | 11 => .lo .xmm11 | 12 => .lo .xmm12 | 13 => .lo .xmm13 | 14 => .lo .xmm14 | 15 => .lo .xmm15
  | 16 => .hi .xmm16 | 17 => .hi .xmm17 | 18 => .hi .xmm18 | 19 => .hi .xmm19 | 20 => .hi .xmm20
  | 21 => .hi .xmm21 | 22 => .hi .xmm22 | 23 => .hi .xmm23 | 24 => .hi .xmm24 | 25 => .hi .xmm25
  | 26 => .hi .xmm26 | 27 => .hi .xmm27 | 28 => .hi .xmm28 | 29 => .hi .xmm29 | 30 => .hi .xmm30
  | _ => .hi .xmm31

/-- The lanes that are copied: by χ, two of each plane, of which θ copies one
of each column and ρ and π lane 1. -/
def lowLanes : List Nat := [0, 1, 7, 8, 14, 10, 16, 17, 23, 24]

/-- The number of the register of lane `i`: `lowLanes` in `ymm0`–`ymm9`, the
other lanes in `ymm16`–`ymm30`. -/
def lnum (i : Nat) : Nat :=
  [0, 1, 16, 17, 18, 19, 20, 2, 3, 21, 5, 22, 23, 24, 4, 25, 6, 7, 26, 27, 28, 29, 30, 8, 9].getD i 0

/-- The register of lane `i`. -/
def lreg (i : Nat) : VReg := vreg (lnum i)

/-- The register of `C[x]`, and, in χ, of the copies. -/
def creg (x : Nat) : VReg := vreg (10 + x)

/-- The temporary. -/
def T : VReg := vreg 15

/-- `op d, a, b`. -/
def eb (op : EBinOp) (d a b : VReg) : Instr := .eop (.bin op d a b)

/-- `vpternlogq d, a, b, imm`. -/
def tern (d a b : VReg) (imm : BitVec 8) : Instr := .eop (.vpternlogq d a b imm)

/-- `vprorq d, a, n`. -/
def ror (d a : VReg) (n : Nat) : Instr := .eop (.vprorq d a (BitVec.ofNat 8 n))

/-- `d := a`: `vmovdqa` between two of `ymm0`–`ymm15` (every copy of
`round`), and otherwise `vporq` of `a` with itself. -/
def copy (d a : VReg) : Instr :=
  match d, a with
  | .lo d, .lo a => .vop (.vmovdqa .l256 d a)
  | _, _ => eb .vporq d a a

/-- The rows of column `x` in the order `column` reads its lanes: first the
one it copies, which is one of `lowLanes`. -/
def colRows (x : Nat) : List Nat :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [1, 0, 2, 3, 4], [1, 0, 2, 3, 4], [2, 0, 1, 3, 4]].getD x []

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`. -/
def column (x : Nat) : List Instr :=
  let l (j : Nat) : VReg := lreg (x + 5 * (colRows x).getD j 0)
  [copy (creg x) (l 0), tern (creg x) (l 1) (l 2) 0x96, tern (creg x) (l 3) (l 4) 0x96]

/-- Each lane of column `x` XORed with `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]`. -/
def dcol (x : Nat) : List Instr :=
  ror T (creg ((x + 1) % 5)) 63 :: (List.range 5).map fun y => tern (lreg (x + 5 * y)) (creg ((x + 4) % 5)) T 0x96

/-- The 24 lanes but `(0, 0)`, each the lane π moves the next one to: lane
`piChain[j]` of `π(A)` is lane `piChain[j + 1]` of `A`, and lane 1 that of
lane `piChain[23]`. -/
def piChain : List Nat := [1, 6, 9, 22, 14, 20, 2, 12, 13, 19, 23, 15, 4, 24, 21, 8, 16, 5, 3, 18, 17, 11, 7, 10]

/-- `ROTR^(64 - ρ)`, the rotation of ρ of lane `i` (none is 0 but lane 0's). -/
def rhoR (i : Nat) : Nat := 64 - rhoOff i

/-- ρ and π. -/
def rhoPi : List Instr :=
  copy T (lreg 1) ::
    ((List.range 23).map fun j => ror (lreg (piChain.getD j 0)) (lreg (piChain.getD (j + 1) 0))
      (rhoR (piChain.getD (j + 1) 0))) ++
    [ror (lreg 10) T (rhoR 1)]

/-- The first lane of plane `y` that χ writes: it and the next are those of
the plane among `lowLanes`. -/
def chiStart (y : Nat) : Nat := 2 * y % 5

/-- χ on plane `y`, from its lane `a` on. -/
def chiAt (y a : Nat) : List Instr :=
  let l (x : Nat) : VReg := lreg (5 * y + (a + x) % 5)
  [copy (creg 0) (l 0), copy (creg 1) (l 1), tern (l 0) (l 1) (l 2) 0xD2, tern (l 1) (l 2) (l 3) 0xD2,
    tern (l 2) (l 3) (l 4) 0xD2, tern (l 3) (l 4) (creg 0) 0xD2, tern (l 4) (creg 0) (creg 1) 0xD2]

/-- χ on plane `y`. -/
def chi (y : Nat) : List Instr := chiAt y (chiStart y)

/-- ι, and the next round constant (setting ZF after the last). -/
def iota : List Instr :=
  [.evLoad T (at_ .rdx 0), eb .vpxorq (lreg 0) (lreg 0) T, .alu .add .rdx (.imm 32), .alu .cmp .rdx (.reg .rcx)]

/-- One round. -/
def round : List Instr :=
  (List.range 5).flatMap column ++ (List.range 5).flatMap dcol ++ rhoPi ++ (List.range 5).flatMap chi ++ iota

/-- The 25 lanes of the four states at `rdi` into their registers. -/
def load : List Instr := (List.range 25).map fun i => .evLoad (lreg i) (at_ .rdi (32 * i))

/-- The 25 lanes back to the four states at `rdi`. -/
def store : List Instr := (List.range 25).map fun i => .evStore (at_ .rdi (32 * i)) (lreg i)

/-- The 24 rounds on the four states at `rdi`, with the table at `rdx` and
its end in `rcx`. -/
def permute4R : Prog isa := .seq (.block load) (.seq (.loop (.block round) .ne) (.block store))

end VG.Impl.Sha3.X86_64.X4R
