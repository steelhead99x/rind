module

public import VerifiedGarbage.Impl.Bignum.X86_64.R2Words
public import VerifiedGarbage.Impl.Rsa.X86_64.WordIO

/-!
# RSA with a precomputed modulus on x86-64

`vg_rsa_public_precompute` writes what Montgomery multiplication needs of a
modulus, `m` and `R² mod m`, once per key; `vg_rsa_public_precomputed`
computes RSAEP from them. Both use the working space, header and arrays of
`vg_rsa_public` (`Impl/Bignum/X86_64.lean`), and Montgomery multiplication
`mul o a b` (`[o] = [a] [b] R⁻¹ mod m`): the baseline `mm`, or one for other
CPU features (`Impl/Bignum/X86_64/Adx.lean`).
-/

@[expose] public section

namespace VG.Impl.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- `w` words (`r12`) from `[rsi]` to `[rbx]`. -/
def copyWords : Prog isa :=
  wordLoop 0 [.mov .rax (.mem (ix .rsi .r14)), .store (ix .rbx .r14) .rax]

/-- `w` (`r12`) times 8 into `rax`. -/
def eightW : List Instr :=
  [.mov .rax (.reg .r12), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax)]

/-- `w := ⌈k / 8⌉` (`k` from the header) into `r12` and its slot, the
arrays' bases, then the base of `m`'s array into `rbx` and the pointer in
slot `sN` into `rsi`. -/
def head : List Instr :=
  ([.mov .rcx (.mem (hdr sK)), .mov .r12 (.reg .rcx), .alu .add .r12 (.imm 7),
    .shift .shr .r12 3, .store (hdr sW) .r12] : List Instr) ++ setBases ++
  ([.mov .rsi (.mem (hdr sN)), .mov .rbx (.mem (hdr (sArr aN)))] : List Instr)

/-! ## `vg_rsa_public_precompute`

`(pre, pre_len, n, n_len, scratch, scratch_len)`, all in registers: `pre`
in slot `sOut`, `n` in `sN` and `n_len` in `sK`. -/

namespace Precompute

variable (mul : Nat → Nat → Nat → Prog isa)

/-- Save the callee-saved registers and the arguments in the header at
`scratch` (`r8`), with its base in `rdi`. -/
def entry : List Instr :=
  (saved.zipIdx.map fun (r, i) => .store { base := .r8, disp := 8 * i } r) ++
  ([.store { base := .r8, disp := 8 * sOut } .rdi, .store { base := .r8, disp := 8 * sN } .rdx,
    .store { base := .r8, disp := 8 * sK } .rcx, .mov .rdi (.reg .r8)] : List Instr)

/-- Zeros to the `16 ⌈k / 8⌉` bytes of `pre`, and 0 returned. -/
def fail : Prog isa :=
  .seq (.block [.mov .rsi (.mem (hdr sOut)), .mov .rcx (.mem (hdr sK)), .alu .add .rcx (.imm 7),
      .shift .shr .rcx 3, .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
      .alu .add .rcx (.reg .rcx), .mov32 .rax (.imm 0)])
    (.seq (.loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne)
      (.block exit))

/-- The computation, once `m` is known valid: `m` into its array (eight bytes
at a time when its length is a multiple of eight: `WordIO.load`), `-m⁻¹`,
`R² mod m` (`r2`: `R2Words.choice`, or another computation of it, such as
`R2Adx.choice` with ADX), then `m` and `R² mod m` to `pre`, and 1 returned. -/
def main (r2 : Prog isa := R2Words.choice mul) : Prog isa := seqs [
  .block head,
  WordIO.load,
  .block (([.mov .r10 (.reg .rbx), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .rbx))] : List Instr) ++
    minv ++ ([.store (hdr sMinv) .r15] : List Instr)),
  -- `R² mod m`, by word steps when `m`'s top bit is set and `w` a multiple of 4.
  r2,
  -- `m`, then `R² mod m`, to `pre`.
  .block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))), .mov .rbx (.mem (hdr sOut))],
  copyWords,
  .block (eightW ++ ([.alu .add .rbx (.reg .rax), .mov .rsi (.mem (hdr (sArr aR2)))] : List Instr)),
  copyWords,
  .block (([.mov32 .rax (.imm 1)] : List Instr) ++ exit)]

/-- `vg_rsa_public_precompute`. -/
def code (r2 : Prog isa := R2Words.choice mul) : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite .ne fail (main mul r2))

end Precompute

/-! ## `vg_rsa_public_precomputed`

`(out, out_len, pre, pre_len, e, e_len, input, input_len, scratch,
scratch_len)`, as `vg_rsa_public`'s with `pre` for `n` and the modulus'
length `k = out_len`: `pre` in slot `sN` and `out_len` in `sK`. -/

namespace Precomputed

variable (mul : Nat → Nat → Nat → Prog isa)

-- Whether the exponentiation has met a set bit of `e` (`Impl/Bignum/Layout.lean`).
export VG.Impl.Bignum.Public (sStarted)

/-- Save the callee-saved registers and the arguments in the header, with
the working space's base in `rdi`. -/
def entry : List Instr :=
  ([.mov .r11 (.mem { base := .rsp, disp := 24 })] : List Instr) ++
  (saved.zipIdx.map fun (r, i) => .store { base := .r11, disp := 8 * i } r) ++
  ([.store { base := .r11, disp := 8 * sOut } .rdi, .store { base := .r11, disp := 8 * sN } .rdx,
    .store { base := .r11, disp := 8 * sK } .rsi, .store { base := .r11, disp := 8 * sE } .r8,
    .store { base := .r11, disp := 8 * sElen } .r9, .mov .rax (.mem { base := .rsp, disp := 8 }),
    .store { base := .r11, disp := 8 * sIn } .rax, .mov .rdi (.reg .r11)] : List Instr)

/-- `m` and `R² mod m` from `pre` into their arrays, then ZF set unless `m`
is odd, its top word is not zero and `R² mod m < m`: the values of no
modulus are refused before any arithmetic on them. -/
def loadWith (cmp : Prog isa) : List (Prog isa) := [
  .block head,
  copyWords,
  .block (eightW ++ ([.alu .add .rsi (.reg .rax), .mov .rbx (.mem (hdr (sArr aR2)))] : List Instr)),
  copyWords,
  .block [.mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)],
  cmp,
  .block [.mov .rax (.mem (at0 .r10)), .alu .and .rax (.imm 1), .alu .and .rax (.reg .rbp),
    .mov .rdx (.mem (ix .r10 .r12 (-8))), .alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx),
    .alu .add .rdx (.imm 1), .alu .and .rax (.reg .rdx), .alu .test .rax (.reg .rax)]]

/-- Whether the exponentiation has started, into ZF (clear if it has). -/
def startedTest : List Instr := [.mov .rax (.mem (hdr sStarted)), .alu .test .rax (.reg .rax)]

/-- `Y := X` (the input in Montgomery form), and the exponentiation started. -/
def start : Prog isa :=
  .seq (.block [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm))), .mov .rbx (.mem (hdr (sArr aY)))])
    (.seq copyWords (.block [.mov32 .rax (.imm 1), .store (hdr sStarted) .rax]))

/-- One bit of `e`, once started: `Y := Y²`; then if the bit is set,
`Y := Y X` once started, or `Y := X` and started. Before the first set bit
`Y` is not used, and squaring 1 is skipped. -/
def expBit : Prog isa :=
  .seq (.block startedTest) (.seq (.ite .ne (mul aY aY aY) (.block []))
    (.seq (.block bitTest)
      (.seq (.ite .ne (.seq (.block startedTest) (.ite .ne (mul aY aY aXm) start)) (.block []))
        (.block bitNext))))

/-- `byteHead` (`Impl/Bignum/X86_64.lean`), with bit 0 of the last byte of
`e` cleared, by the mask `-1`, or `-2` for the last byte, without a branch:
the exponentiation is by `e - 1` for an odd `e`, and the last
multiplication, by the input itself, both adds the last bit and leaves
Montgomery form (`Folded.lean`). -/
def byteHeadEven : List Instr :=
  [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI)), .movzx8 .rax { base := .rax, index := some .rcx },
    .alu .add .rcx (.imm 1), .alu .sub .rcx (.mem (hdr sElen)), .alu .cmp .rcx (.imm 1),
    .alu .sbb .rcx (.reg .rcx), .alu .sub .rcx (.imm 1), .alu .and .rax (.reg .rcx),
    .store (hdr sV) .rax, .mov32 .rax (.imm 8), .store (hdr sBit) .rax]

/-- The exponentiation by `e` with bit 0 of its last byte cleared, over the
bytes of `e` and their bits, most significant first. -/
def expLoop : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (hdr sI) .rax, .store (hdr sStarted) .rax])
    (.loop (.seq (.block byteHeadEven) (.seq (.loop (expBit mul) .ne) (.block byteNext))) .ne)

end Precomputed

end VG.Impl.Rsa.X86_64
