module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! Four word stores (32 bytes) at a time, then word stores, then a byte
tail. Unaligned stores are permitted on x86-64.

`zeroizeAvx` (`vg_zeroize_avx`, for CPUs with AVX) stores 64 bytes at a time
instead, from `ymm0` zeroed by `vpxor xmm0` (whose `VEX.128` form zeroes
bits 255:128 too), then up to seven words and seven bytes as `zeroize`
does, and clears the upper halves of the vector registers before returning
(`vzeroupper`), for the SSE code its callers may run next. -/

@[expose] public section

namespace VG.Impl.Zeroize.X86_64
open VG.X86_64

def step (word : Bool) : List Instr :=
  [if word then .store { base := .rdi } .rax else .store8 { base := .rdi } .rax,
   .alu .add .rdi (.imm (if word then 8 else 1)), .alu .sub .rdx (.imm 1)]

/-- Four words, at `rdi`, `rdi + 8`, `rdi + 16` and `rdi + 24`. -/
def wideStep : List Instr :=
  [.store { base := .rdi } .rax, .store { base := .rdi, disp := 8 } .rax,
   .store { base := .rdi, disp := 16 } .rax, .store { base := .rdi, disp := 24 } .rax,
   .alu .add .rdi (.imm 32), .alu .sub .rdx (.imm 1)]

/-- `body` `rdx` times. -/
def loopOf (body : List Instr) : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm 0)])
    (.ite .e (.block []) (.loop (.block body) .ne))

def loop (word : Bool) : Prog isa := loopOf (step word)

def zeroize : Prog isa :=
  .seq (.block [.mov .rax (.imm 0), .mov .rdx (.reg .rsi), .shift .shr .rdx 5])
    (.seq (loopOf wideStep)
    (.seq (.block [.mov .rdx (.reg .rsi), .shift .shr .rdx 3, .alu .and .rdx (.imm 3)])
    (.seq (loop true) (.seq (.block [.mov .rdx (.reg .rsi), .alu .and .rdx (.imm 7)]) (loop false)))))
/-- 64 bytes from `ymm0`, at `rdi` and `rdi + 32`. -/
def wideStepY : List Instr :=
  [.vmovdquStore .l256 { base := .rdi } .xmm0, .vmovdquStore .l256 { base := .rdi, disp := 32 } .xmm0,
   .alu .add .rdi (.imm 64), .alu .sub .rdx (.imm 1)]

def zeroizeAvx : Prog isa :=
  .seq (.block [.vop (.vbin .vpxor .l128 .xmm0 .xmm0 .xmm0), .mov .rax (.imm 0), .mov .rdx (.reg .rsi),
      .shift .shr .rdx 6])
    (.seq (loopOf wideStepY)
    (.seq (.block [.mov .rdx (.reg .rsi), .shift .shr .rdx 3, .alu .and .rdx (.imm 7)])
    (.seq (loop true) (.seq (.block [.mov .rdx (.reg .rsi), .alu .and .rdx (.imm 7)])
    (.seq (loop false) (.block [.vop .vzeroupper]))))))
end VG.Impl.Zeroize.X86_64
