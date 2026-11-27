module

public import VerifiedGarbage.Spec.Sha3
public import VerifiedGarbage.Impl.Sha3.Tables
public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Keccak-f[1600]: x86-64 implementation

`vg_keccak_f1600(state = rdi, scratch = rsi)`.

The rounds follow Andy Polyakov's CRYPTOGAMS `keccak1600-x86_64` (the
"lane complementing" implementation of the Keccak team's implementation
overview, with the column parities and `D` in registers).

**Lane complementing.** While the rounds run, the lanes `1, 2, 8, 12, 17, 20`
(`complLanes`) of the state are kept complemented: that turns most of χ's
`¬a ∧ b` into an `∧` or an `∨` of the lanes as they are, so that χ needs one
NOT per plane instead of five. The prologue complements those lanes and the
epilogue complements them back.

`scratch` (512 bytes) is laid out as:

* `[0, 200)`: a second state, which the rounds alternate with `state`: the
  first round of each iteration reads `state` (`rdi`) and writes the second
  state (`rsi`), the second the other way round, so after the 24 rounds the
  result is back in `state`;
* `[200, 392)`: the 24 round constants, stored by the prologue;
* `[392, 440)`: the saved `rbx, rbp, r12–r15`.

A round from `s` to `d` has lanes `20–24` of its input (row 4) in
`rax, rbx, rcx, rdx, rbp` on entry, and leaves those of its output there.
It computes the column parities `C[x]` in those registers (θ), then the
`D[x]` in place, and for each plane `y` of the output the five lanes `B[x]`
of `π(ρ(θ(A)))` in `r8–r12`, from which it stores
`B[x] ⊕ (¬B[x+1] ∧ B[x+2])` (χ, with ι for lane 0), using `r13` and `r14` as
temporaries, and loading the lanes of the next plane as registers free up.
The round constant of round `2i + k` is at `[rsi + r15 + 392 + 8k]`, where
`r15 = 16i - 192` counts up to 0, which ends the loop.

Every address is a pointer plus a constant (or plus `r15`), and the only
branch is the round loop's, so only the pointers can affect timing.
-/

@[expose] public section

namespace VG.Impl.Sha3.X86_64

open VG.X86_64
open VG.Impl.Sha3 (complLanes)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- Lane `i` of the state at `b`. -/
def lane (b : Reg) (i : Nat) : MemOp := at_ b (8 * i)

/-! ## Instructions of a round -/

/-- `r = A[i]` (lane `i` of the state at `b`). -/
def ld (r b : Reg) (i : Nat) : Instr := .mov r (.mem (lane b i))
/-- `r ^= A[i]`. -/
def xl (r b : Reg) (i : Nat) : Instr := .alu .xor r (.mem (lane b i))
/-- Lane `i` of the state at `b` is set to `r`. -/
def st (b : Reg) (i : Nat) (r : Reg) : Instr := .store (lane b i) r
def mv (r q : Reg) : Instr := .mov r (.reg q)
def xr (r q : Reg) : Instr := .alu .xor r (.reg q)
def an (r q : Reg) : Instr := .alu .and r (.reg q)
def orr (r q : Reg) : Instr := .alu .or r (.reg q)
/-- A rotation left by `0 < n < 64`. -/
def rol (r : Reg) (n : Nat) : Instr := .shift .ror r (64 - n)
/-- `r = ¬r` (an XOR with the sign-extended immediate `-1`). -/
def nt (r : Reg) : Instr := .alu .xor r (.imm 0xffffffff)

/-- A round from the state at `s`, up to ι: θ, the `B[x]` of plane 0 and
the first lane of its χ. -/
def roundA (s : Reg) : List Instr := [
    -- C[x] = A[x, 4] ⊕ … ⊕ A[x, 0], loading A[0, 0], A[1, 1], A[2, 2], A[3, 3] (sources of
    -- plane 0) into r8–r11 and A[4, 4] into r12 on the way
    ld .r8 s 0, ld .r9 s 6, ld .r10 s 12, ld .r11 s 18,
    xl .rcx s 2, xl .rdx s 3, xr .rax .r8, xl .rbx s 1,
    xl .rcx s 7, xl .rax s 5, mv .r12 .rbp, xl .rbp s 4,
    xr .rcx .r10, xl .rax s 10, xl .rdx s 8, xr .rbx .r9,
    xl .rbp s 9, xl .rcx s 17, xl .rax s 15, xl .rdx s 13,
    xl .rbx s 11, xl .rbp s 14,
    -- D[x] = ROTL¹(C[x + 1]) ⊕ C[x - 1], in place: D[1] in rcx, D[4] in rax, D[2] in rdx,
    -- D[0] in rbx, D[3] in rbp
    mv .r13 .rcx, rol .rcx 1,
    xr .rcx .rax, xr .rdx .r11, rol .rax 1, xr .rax .rdx,
    xl .rbx s 16, rol .rdx 1, xr .rdx .rbx, xl .rbp s 19,
    rol .rbx 1, xr .rbx .rbp, rol .rbp 1, xr .rbp .r13,
    -- plane 0: B[x] = ROTL^ρ(A[x, x] ⊕ D[x]) in r8–r12, and lane 0 of χ in r9
    xr .r9 .rcx, xr .r10 .rdx, rol .r9 44, xr .r11 .rbp,
    xr .r12 .rax, rol .r10 43, xr .r8 .rbx, mv .r13 .r9,
    rol .r11 21, orr .r9 .r10, xr .r9 .r8, rol .r12 14]

/-- The rest of the round from the state at `s` to the state at `d`, after ι. -/
def roundB (s d : Reg) : List Instr := [
    -- the rest of plane 0's χ, loading plane 1's sources
    mv .r14 .r12, an .r12 .r11, st d 0 .r9, xr .r12 .r10,
    nt .r10, st d 2 .r12, orr .r10 .r11, ld .r12 s 22,
    xr .r10 .r13, st d 1 .r10, an .r13 .r8, ld .r9 s 9,
    xr .r13 .r14, ld .r10 s 10, st d 4 .r13, orr .r14 .r8,
    ld .r8 s 3, xr .r14 .r11, ld .r11 s 16, st d 3 .r14,
    -- plane 1
    xr .r8 .rbp, xr .r12 .rdx, rol .r8 28, xr .r11 .rcx,
    xr .r9 .rax, rol .r12 61, rol .r11 45, xr .r10 .rbx,
    rol .r9 20, mv .r13 .r8, orr .r8 .r12, rol .r10 3,
    xr .r8 .r11, st d 8 .r8, mv .r14 .r9, an .r9 .r13,
    ld .r8 s 1, xr .r9 .r12, nt .r12, st d 9 .r9,
    orr .r12 .r11, ld .r9 s 7, xr .r12 .r10, st d 7 .r12,
    an .r11 .r10, ld .r12 s 20, xr .r11 .r14, st d 6 .r11,
    orr .r14 .r10, ld .r10 s 13, xr .r14 .r13, ld .r11 s 19,
    st d 5 .r14,
    -- plane 2
    xr .r10 .rbp, xr .r11 .rax, rol .r10 25,
    xr .r9 .rdx, rol .r11 8, xr .r12 .rbx, rol .r9 6,
    xr .r8 .rcx, rol .r12 18, mv .r13 .r10, an .r10 .r11,
    rol .r8 1, nt .r11, xr .r10 .r9, st d 11 .r10,
    mv .r14 .r12, an .r12 .r11, ld .r10 s 11, xr .r12 .r13,
    st d 12 .r12, orr .r13 .r9, ld .r12 s 23, xr .r13 .r8,
    st d 10 .r13, an .r9 .r8, xr .r9 .r14, st d 14 .r9,
    orr .r14 .r8, ld .r9 s 5, xr .r14 .r11, ld .r11 s 17,
    st d 13 .r14,
    -- plane 3
    ld .r8 s 4, xr .r10 .rcx, xr .r11 .rdx,
    rol .r10 10, xr .r9 .rbx, rol .r11 15, xr .r12 .rbp,
    rol .r9 36, xr .r8 .rax, rol .r12 56, mv .r13 .r10,
    orr .r10 .r11, rol .r8 27, nt .r11, xr .r10 .r9,
    st d 16 .r10, mv .r14 .r12, orr .r12 .r11, xr .r12 .r13,
    st d 17 .r12, an .r13 .r9, xr .r13 .r8, st d 15 .r13,
    orr .r9 .r8, xr .r9 .r14, st d 19 .r9, an .r8 .r14,
    xr .r8 .r11, st d 18 .r8,
    -- plane 4, its B[x] computed in place in the registers of D, which are no longer needed
    xl .rdx s 2, xl .rbp s 8,
    rol .rdx 62, xl .rcx s 21, rol .rbp 55, xl .rax s 14,
    rol .rcx 2, xl .rbx s 15, rol .rax 39, rol .rbx 41,
    mv .r13 .rdx, an .rdx .rbp, nt .rbp, xr .rdx .rcx,
    st d 24 .rdx, mv .r14 .rax, an .rax .rbp, xr .rax .r13,
    st d 20 .rax, orr .r13 .rcx, xr .r13 .rbx, st d 23 .r13,
    an .rcx .rbx, xr .rcx .r14, st d 22 .rcx, orr .rbx .r14,
    xr .rbx .rbp, st d 21 .rbx,
    -- row 4 of the output back in rax, rbx, rcx, rdx, rbp
    mv .rbp .rdx, mv .rdx .r13]

/-- The round constant of the `k`-th round of an iteration. -/
def rcOp (k : Nat) : MemOp := { base := .rsi, index := some .r15, disp := 392 + 8 * k }

/-- ι in the `k`-th round of an iteration: the round constant, XORed into
lane 0 of the output. -/
def iota (k : Nat) : Instr := .alu .xor .r9 (.mem (rcOp k))

/-- A round from the state at `s` to the state at `d`. -/
def round (s d : Reg) (k : Nat) : List Instr := roundA s ++ iota k :: roundB s d

/-- Two rounds, from `state` to the second state and back, and the next pair
of round constants (setting ZF after the last). -/
def body : List Instr := round .rdi .rsi 0 ++ round .rsi .rdi 1 ++ ([.alu .add .r15 (.imm 16)] : List Instr)

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 392), (.rbp, 400), (.r12, 408), (.r13, 416), (.r14, 424), (.r15, 432)]

/-- Complement the lanes `complLanes` of the state at `rdi`. -/
def complement : List Instr :=
  complLanes.flatMap fun i => [ld .rax .rdi i, nt .rax, st .rdi i .rax]

/-- Load row 4 of the state at `rdi`, after `complement`, which leaves
lane 20 (the last it complements) in `rax`. -/
def loadRow : List Instr := [ld .rbx .rdi 21, ld .rcx .rdi 22, ld .rdx .rdi 23, ld .rbp .rdi 24]

/-- Save the registers, store the round constants and set `r15`. -/
def setup : List Instr :=
  saved.map (fun (r, d) => .store (at_ .rsi d) r) ++
  (List.range 24).flatMap (fun k => [.movImm64 .rax (Spec.Sha3.RC k), .store (at_ .rsi (200 + 8 * k)) .rax]) ++
  ([.mov .r15 (.imm (-192))] : List Instr)

/-- Restore the registers. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .rsi d))

def permute : Prog isa :=
  .seq (.block (setup ++ complement ++ loadRow))
    (.seq (.loop (.block body) .ne) (.block (complement ++ restore)))

end VG.Impl.Sha3.X86_64
