module

public import VerifiedGarbage.Impl.Sha3.X86_64.X4Reg

/-!
# Keccak-f[1600] on four states at once: x86-64 with AVX2

Four states in one buffer of 800 bytes, interleaved: lane `j` of state `k`
is the `u64` at byte `32 j + 8 k`, so that lane `j` of the four is one
256-bit value, and each instruction on `ymm` registers computes the same on
the four states, one in each 64-bit element.

`permute4` is a fragment (not a function: its callers inline it), with
`rdi` pointing at the states, `rsi` at a second buffer of 800 bytes, and
`rdx` at a table of the 24 round constants, each in the four elements of a
`u256` (768 bytes; `rcTable` stores it, through `rax` and `ymm0`), and `rcx` past its
end. As the scalar implementation (`Impl/Sha3/X86_64.lean`), a round reads
one buffer (`src`, `rdi`) and writes the other (`dst`, `rsi`), then swaps
them; the loop runs two rounds per iteration, so that after the 24 rounds
the result is back at `rdi`. A round starts with the five column parities
`C[x]` (θ) of its input in `ymm11`–`ymm15`: `cols` computes those of the
first round's from memory, and each round those of the next's as it writes
them. It computes `D[x]` into `ymm5`–`ymm9`; then, for each plane `y` of the
output, the five lanes `B[x]` of `π(ρ(θ(A)))` in that plane into
`ymm0`–`ymm4` (a rotation left by `n` is `vpsllq`, `vpsrlq` by `64 - n` and
`vpor`, with `ymm10`), and stores `B[x] ⊕ (¬B[x+1] ∧ B[x+2])` (χ, `vpandn`,
and ι for lane 0, from the table) to `dst`: for plane 0 computed in the
register of `C[x]`, which then accumulates the column parity of the output,
and for the others in `ymm10`, which it adds to that parity. It
(`permute4M`) writes only `rax`, `rdx`, `rdi`, `rsi`, the flags and
`ymm0`–`ymm15`.

`permute4 true` is `X4R.permute4R` (`X4Reg.lean`) instead, with the same
interface, which keeps the four states in the thirty-two registers of
AVX-512VL for the 24 rounds.

Every address is a pointer plus a constant, and the only branch is the
round loop's, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64.X4

open VG.X86_64
open VG.Impl.Sha3 (rhoOff piSrc)

/-- `op d, a, b` on 256 bits. -/
def vb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- `op d, a, n` (a shift of each 64-bit element) on 256 bits. -/
def vsh (op : XShiftOp) (d a : XReg) (n : Nat) : Instr := .vop (.vshift op .l256 d a (BitVec.ofNat 8 n))

/-- Lane `i` of the four states at `b`, to `d`. -/
def ld (d : XReg) (b : Reg) (i : Nat) : Instr := .vmovdquLoad .l256 d (at_ b (32 * i))

/-- `r` to lane `i` of the four states at `b`. -/
def st (b : Reg) (i : Nat) (r : XReg) : Instr := .vmovdquStore .l256 (at_ b (32 * i)) r

/-- The register of `C[x]`, and then of `B[x]`. -/
def creg (x : Nat) : XReg := [XReg.xmm0, .xmm1, .xmm2, .xmm3, .xmm4].getD x .xmm0

/-- The register of `D[x]`. -/
def dreg (x : Nat) : XReg := [XReg.xmm5, .xmm6, .xmm7, .xmm8, .xmm9].getD x .xmm5

/-- The register of the column parity `C[x]` of a round's input, and then
of its output. -/
def preg (x : Nat) : XReg := [XReg.xmm11, .xmm12, .xmm13, .xmm14, .xmm15].getD x .xmm11

/-- The temporary. -/
def T : XReg := .xmm10

/-- `op d, a, [b + 32 i]` on 256 bits. -/
def vbl (op : VBinOp) (d a : XReg) (b : Reg) (i : Nat) : Instr := .vbinLoad op .l256 d a (at_ b (32 * i))

/-- `C[x] = A[x, 0] ⊕ … ⊕ A[x, 4]`, from the states at `rdi`. -/
def column (x : Nat) : List Instr :=
  [ld (preg x) .rdi x, vbl .vpxor (preg x) (preg x) .rdi (x + 5), vbl .vpxor (preg x) (preg x) .rdi (x + 10),
    vbl .vpxor (preg x) (preg x) .rdi (x + 15), vbl .vpxor (preg x) (preg x) .rdi (x + 20)]

/-- The column parities of the first round's input. -/
def cols : List Instr := (List.range 5).flatMap column

/-- `D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1]`. -/
def dcol (x : Nat) : List Instr :=
  [vsh .psllq T (preg ((x + 1) % 5)) 1, vsh .psrlq (dreg x) (preg ((x + 1) % 5)) 63, vb .vpor (dreg x) (dreg x) T,
    vb .vpxor (dreg x) (dreg x) (preg ((x + 4) % 5))]

/-- `B[x] = ROTL^ρ(A[piSrc x y] ⊕ D[(x + 3y) mod 5])` for plane `y`. -/
def laneB (x y : Nat) : List Instr :=
  [ld (creg x) .rdi (piSrc x y), vb .vpxor (creg x) (creg x) (dreg ((x + 3 * y) % 5))] ++
    if rhoOff (piSrc x y) = 0 then []
    else [vsh .psllq T (creg x) (rhoOff (piSrc x y)), vsh .psrlq (creg x) (creg x) (64 - rhoOff (piSrc x y)),
      vb .vpor (creg x) (creg x) T]

/-- Lane `(x, y)` of the output: `B[x] ⊕ (¬B[x+1] ∧ B[x+2])`, and for lane 0
the round constant at `rdx`; for plane 0 computed in the register of `C[x]`,
and for the others in `T` and added to it. -/
def chi (x y : Nat) : List Instr :=
  if y = 0 then
    [vb .vpandn (preg x) (creg ((x + 1) % 5)) (creg ((x + 2) % 5)), vb .vpxor (preg x) (preg x) (creg x)] ++
      (if x = 0 then [vbl .vpxor (preg x) (preg x) .rdx 0] else []) ++ [st .rsi x (preg x)]
  else
    [vb .vpandn T (creg ((x + 1) % 5)) (creg ((x + 2) % 5)), vb .vpxor T T (creg x), st .rsi (x + 5 * y) T,
      vb .vpxor (preg x) (preg x) T]

/-- Plane `y` of the output. -/
def plane (y : Nat) : List Instr :=
  (List.range 5).flatMap (fun x => laneB x y) ++ (List.range 5).flatMap (fun x => chi x y)

/-- One round from `rdi` to `rsi`; then swap them, and advance to the next
round constant (setting ZF after the last). -/
def round : List Instr :=
  (List.range 5).flatMap dcol ++ (List.range 5).flatMap plane ++
    ([.mov .rax (.reg .rdi), .mov .rdi (.reg .rsi), .mov .rsi (.reg .rax),
      .alu .add .rdx (.imm 32), .alu .cmp .rdx (.reg .rcx)] : List Instr)

/-- The 24 rounds, from `rdi` (and back to it), with the table at `rdx`
and its end in `rcx`. -/
def permute4M : Prog isa := .seq (.block cols) (.loop (.block (round ++ round)) .ne)

/-- `permute4M`, or with `fast` (AVX-512VL) `X4R.permute4R`. -/
def permute4 (fast : Bool := false) : Prog isa := bif fast then X4R.permute4R else permute4M

/-- The table of the round constants from lane `i` at `b` (byte `32 i`),
each in the four elements, through `rax` and `ymm0`. -/
def rcTable (b : Reg) (i : Nat) : List Instr :=
  (List.range 24).flatMap fun k =>
    [.movImm64 .rax (Spec.Sha3.RC k), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      st b (i + k) .xmm0]

end VG.Impl.Sha3.X86_64.X4
