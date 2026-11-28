module

public import VerifiedGarbage.Impl.MlKem.X86_64.Encode12

/-!
# ML-KEM on x86-64: the key check (`vg_mlkem768_check_ek`, `vg_mlkem1024_check_ek`)

`checkEkK k (ek = rdi) -> rax`, for the rank `k`, runs over the `128k` groups
of 3 bytes of `ek[0 : 384k]`, with `rcx` counting down, splitting each into
its two 12-bit fields as `decode12` does. `cmp field, q` sets CF exactly when
the field is less than `q`, and `adc r8, 0` counts the fields that are. The
key passes the modulus check exactly when all `256k` are: `cmp r8, 256k` sets
CF exactly when one is not, and `sbb rax, rax; add rax, 1` returns `1 - CF`,
without a branch. Every address and branch depends only on the pointer.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

def checkEkBody : List Instr :=
  dec12Load ++ [.mov32 .rdx (.reg .rax), .alu32 .and .rax (.imm 0xfff), .shift32 .shr .rdx 12,
    .alu32 .cmp .rax (.imm qImm), .alu .adc .r8 (.imm 0), .alu32 .cmp .rdx (.imm qImm),
    .alu .adc .r8 (.imm 0), .alu .add .rdi (.imm 3), .alu .sub .rcx (.imm 1)]

/-- The check of the `128k` groups of `ek[0 : 384k]`, for the rank `k`. -/
def checkEkK (k : Nat) : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 0)])
    (.seq (.seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 (128 * k)))]) (.loop (.block checkEkBody) .ne))
      (.block [.alu .cmp .r8 (.imm (BitVec.ofNat 32 (256 * k))), .alu .sbb .rax (.reg .rax), .alu .add .rax (.imm 1)]))

/-- `vg_mlkem768_check_ek`. -/
abbrev checkEk : Prog isa := checkEkK 3

end VG.Impl.MlKem.X86_64
