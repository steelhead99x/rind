module

public import VerifiedGarbage.TCB.X86_64.Isa

/-!
# A call that wipes part of a buffer afterwards (x86-64)

`callWipe r n name body zname zcode` calls the function `name`, whose code is
`body`, with the arguments its caller was given, all in registers, then zeroes
the first `n` bytes of the buffer whose address was passed in `r` by calling
the zeroize function `zname`, whose code is `zcode`, and returns what `name`
returned. It allocates a frame of 16 bytes: the buffer's address at
`rsp + 8`, saved before the first call, and `name`'s result at `rsp`, saved
across the second.
-/

@[expose] public section

namespace VG.Impl.CallWipe.X86_64

open VG.X86_64

/-- `mov [rsp + 8], r`: save the buffer's address. -/
def saveArg (r : Reg) : List Instr := [.store { base := .rsp, disp := 8 } r]

/-- `mov [rsp], rax; mov rdi, [rsp + 8]; mov esi, n`: save the result, and
pass the buffer's address and `n` to the zeroize function. -/
def zeroArgs (n : Nat) : List Instr :=
  [.store { base := .rsp } .rax, .mov .rdi (.mem { base := .rsp, disp := 8 }),
    .mov32 .rsi (.imm (BitVec.ofNat 32 n))]

/-- `mov rax, [rsp]`: restore the result. -/
def restoreRet : List Instr := [.mov .rax (.mem { base := .rsp })]

/-- A call of `name`, whose code is `body`, then of the zeroize function
`zname`, whose code is `zcode`, on the first `n` bytes of the buffer whose
address is in `r` on entry, returning `name`'s result. -/
def callWipe (r : Reg) (n : Nat) (name : String) (body : Prog isa) (zname : String)
    (zcode : Prog isa) : Prog isa :=
  .frame (.alloc 16)
    (.seq (.block (saveArg r))
      (.seq (.call name body)
        (.seq (.block (zeroArgs n))
          (.seq (.call zname zcode) (.block restoreRet)))))
    (.free 16)

end VG.Impl.CallWipe.X86_64
