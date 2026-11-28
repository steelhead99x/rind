module

public import VerifiedGarbage.Impl.MlKem.X86_64.Common
public import VerifiedGarbage.Impl.Sha3.X86_64.Stream

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt`

`sampleNTT(seed = rdi, a = rsi, scratch = rdx) -> eax` keeps `scratch` in
`rbx` and `a` in `rbp`, whose caller's values it saves in
`scratch[1680..1696)` (the functions it calls preserve them), and `seed`
in `scratch[1696..1704)`. `scratch` holds, from byte 0, the Keccak state
(200 bytes), the working space of the sponge functions (640 bytes) and the
XOF output (840 bytes).

`snSample n` runs `n` iterations of `SampleNTT`'s loop on the first `3 n`
bytes of the XOF output: it zeroes the state (the empty message), absorbs
the 34 bytes of the seed with `vg_keccak_absorb` (rate 168), pads it with
`vg_keccak_pad` (SHAKE's suffix `0x1f`), squeezes `3 n` bytes with
`vg_keccak_squeeze`, and loops `n` times, with `rsi` at the 3 bytes of the
iteration, `rdi` = `j`, the number of coefficients sampled, and `rcx`
counting down: while `j < 256`, each of the two 12-bit values `d₁`, `d₂`
of the 3 bytes (in `r9` and `r8`) is stored to `a[j]` (at `rbp + 4 rdi`, or
`rbp + 2 rdi` as a 16-bit coefficient for `vg_mlkem16_sample_ntt`),
and `j` incremented by the carry of its comparison with `q`, 1 if it is
less than `q` (`d₂` only if `j < 256` still). A value not counted is
overwritten by the next, or lies past the coefficients sampled; without a
branch on each value, the loop does not mispredict one in five of them.

The function runs `snSample 168`, which samples 256 coefficients but for
about one seed in 120 (168 iterations sample 273 values less than `q` on
average); only if `j < 256` then does it run `snSample 280` from the
start, as the specification's loop. It returns `j >> 8`: 1 if `j = 256`,
and 0 otherwise.

The loop's branches and the addresses of its stores, and whether the
function runs `snSample 280`, depend on the XOF output, a function of the
seed, and on nothing else; every other address and branch depends only on
the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `a[j]`: `[rbp + 4 rdi]`, or `[rbp + 2 rdi]` for 16-bit coefficients (`h`). -/
def aJ (h : Bool := false) : MemOp := { base := .rbp, index := some .rdi, scale := if h then 2 else 4 }

/-- The 25 lanes of the state at `b + off`, zeroed (with `rax` = 0). -/
def zeroSt (b : Reg) (off : Nat) : List Instr := (List.range 25).flatMap fun i => [.store (at_ b (off + 8 * i)) .rax]

/-- Zero the state (with `rax` = 0), and the arguments of `absorb`, with `seed` in `rcx`. -/
def snAbs : List Instr :=
  [.mov32 .rax (.imm 0)] ++ zeroSt .rbx 0 ++
    [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 168), .mov32 .rdx (.imm 0), .mov32 .r8 (.imm 34),
      .mov .r9 (.reg .rbx), .alu .add .r9 (.imm 200)]

/-- Save `rbx`, `rbp` and `seed`, keep the pointers, and `snAbs`. -/
def snPro : List Instr :=
  [.store (at_ .rdx 1680) .rbx, .store (at_ .rdx 1688) .rbp, .store (at_ .rdx 1696) .rdi, .mov .rbx (.reg .rdx),
    .mov .rbp (.reg .rsi), .mov .rcx (.reg .rdi)] ++ snAbs

/-- The arguments of `pad`. -/
def snPadArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 168), .mov32 .rdx (.imm 34), .mov32 .rcx (.imm 0x1f),
    .mov .r8 (.reg .rbx), .alu .add .r8 (.imm 200)]

/-- The arguments of `squeeze`: `len` bytes from position 0. -/
def snSqzArgs (len : BitVec 32) : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 168), .mov32 .rdx (.imm 0), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm 840), .mov32 .r8 (.imm len), .mov .r9 (.reg .rbx), .alu .add .r9 (.imm 200)]

/-- The 3 bytes at `rsi`: `d₁` in `r9` and `d₂` in `r8`, and `j < 256` in CF. -/
def snLoad : List Instr :=
  [.movzx8 .rax (at_ .rsi 0), .movzx8 .rdx (at_ .rsi 1), .movzx8 .r8 (at_ .rsi 2), .mov32 .r9 (.reg .rdx),
    .alu32 .and .r9 (.imm 15), .shift32 .ror .r9 24, .alu32 .add .r9 (.reg .rax), .shift32 .shr .rdx 4,
    .shift32 .ror .r8 28, .alu32 .add .r8 (.reg .rdx), .alu .cmp .rdi (.imm 256)]

/-- Store the value in `r` to `a[j]`, and count it (add 1 to `j`) if it is
less than `q`: CF of the comparison. A value not counted is overwritten by
the next one. -/
def snTry (r : Reg) (h : Bool := false) : List Instr :=
  [if h then .store16 (aJ h) r else .store32 (aJ h) r, .alu32 .cmp r (.imm qImm), .alu .adc .rdi (.imm 0)]

def snBody (h : Bool := false) : Prog isa :=
  .seq (.block snLoad)
    (.seq (.ite .b (.seq (.block (snTry .r9 h)) (.seq (.block [.alu .cmp .rdi (.imm 256)])
        (.ite .b (.block (snTry .r8 h)) (.block []))))
        (.block []))
      (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]))

/-- `n` iterations of the loop, from the XOF output at `scratch + 840`, and `j` = 0. -/
def snLoop (n : BitVec 32) (h : Bool := false) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)])
    (.seq (.block [.mov32 .rcx (.imm n)]) (.loop (snBody h) .ne))

/-- From the arguments of `absorb`: `n` iterations of the loop on the first
`3 n` bytes of the XOF output. -/
def snSample (n : BitVec 32) (h : Bool := false) : Prog isa :=
  .seq (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb)
    (.seq (.block snPadArgs)
      (.seq (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad)
        (.seq (.block (snSqzArgs (3 * n)))
          (.seq (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) (snLoop n h)))))

/-- If `j < 256`, the 280 iterations from the start. -/
def snMore (h : Bool := false) : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 256)])
    (.ite .b (.seq (.block (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs)) (snSample 280 h)) (.block []))

/-- The return value, and `rbx`, `rbp` restored. -/
def snEpi : List Instr :=
  [.mov .rax (.reg .rdi), .shift .shr .rax 8, .mov .rbp (.mem (at_ .rbx 1688)), .mov .rbx (.mem (at_ .rbx 1680))]

/-- `vg_mlkem_sample_ntt`, or `vg_mlkem16_sample_ntt` storing 16-bit
coefficients (`h`): the same code, but for the stores of `snTry`. -/
def sampleNTTW (h : Bool) : Prog isa :=
  .seq (.block snPro) (.seq (snSample 168 h) (.seq (snMore h) (.block snEpi)))

def sampleNTT : Prog isa := sampleNTTW false

def sampleNTT16 : Prog isa := sampleNTTW true

end VG.Impl.MlKem.X86_64
