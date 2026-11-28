import RindIsa.X86_64

/-!
# rind's structured copy of aws-lc's `poly_hash_ad_internal`

rind's naked function `low::x86_64::chacha20poly1305::poly_hash_ad_internal`,
which aws-lc's one-pass `chacha20_poly1305_{seal,open}` call to hash the AAD
into the Poly1305 accumulator they keep in `r10`, `r11`, and `r12`: the AAD
is `r8` bytes at `rcx`, and `r` the two clamped words at `rbp`. Each 16-byte
block, the last one zero-padded, is added with a one bit above it, then the
accumulator is multiplied by `r` and partly reduced modulo 2^130 - 5
(`mul`, aws-lc's `poly_mul`). A 13-byte AAD, TLS 1.2's, loads its one block
directly.

aws-lc's text (`crypto/cipher_extra/asm/chacha20_poly1305_x86_64.pl`) jumps
where VG's structured `Code` cannot: the 13-byte path returns from the middle
of the function, and the block loop tests at its top and jumps back from its
bottom. This copy, `rind/src/low/x86_64/poly_hash_ad.s`, is aws-lc's
instructions in this structure, which `layout` lays out: the 13-byte path
jumps to the function's one return, and the block loop tests again at its
bottom; the byte loads are `movzbl`, VG's form of aws-lc's `movzbq`.
`admin/prove lean` checks that `function prog repRet` is its bytes as rind's
Linux release build emits it.
-/

namespace Rind.X86_64.PolyHashAd

open VG VG.X86_64

/-- `[b + d]` -/
def m (b : Reg) (d : Int) : MemOp := { base := b, disp := d }

/-- Zero the accumulator, and compare the AAD's length with 13. -/
def init : List Instr :=
  [.vg (.alu .xor .r10 (.reg .r10)),
   .vg (.alu .xor .r11 (.reg .r11)),
   .vg (.alu .xor .r12 (.reg .r12)),
   .vg (.alu .cmp .r8 (.imm 13))]

/-- Multiply the accumulator `(r10, r11, r12)` by `r`, the words at `rbp`,
into `(r13, r14, r15, r9)`, then add five times all of it above bit 130 to
the rest: aws-lc's `poly_mul`. -/
def mul : List Instr :=
  [.vg (.mov .rax (.mem (m .rbp 0))),
   .vg (.mov .r15 (.reg .rax)),
   .vg (.mul .r10),
   .vg (.mov .r13 (.reg .rax)),
   .vg (.mov .r14 (.reg .rdx)),
   .vg (.mov .rax (.mem (m .rbp 0))),
   .vg (.mul .r11),
   .vg (.imul .r15 .r12),
   .vg (.alu .add .r14 (.reg .rax)),
   .vg (.alu .adc .r15 (.reg .rdx)),
   .vg (.mov .rax (.mem (m .rbp 8))),
   .vg (.mov .r9 (.reg .rax)),
   .vg (.mul .r10),
   .vg (.alu .add .r14 (.reg .rax)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.mov .r10 (.reg .rdx)),
   .vg (.mov .rax (.mem (m .rbp 8))),
   .vg (.mul .r11),
   .vg (.alu .add .r15 (.reg .rax)),
   .vg (.alu .adc .rdx (.imm 0)),
   .vg (.imul .r9 .r12),
   .vg (.alu .add .r15 (.reg .r10)),
   .vg (.alu .adc .r9 (.reg .rdx)),
   .vg (.mov .r10 (.reg .r13)),
   .vg (.mov .r11 (.reg .r14)),
   .vg (.mov .r12 (.reg .r15)),
   .vg (.alu .and .r12 (.imm 3)),
   .vg (.mov .r13 (.reg .r15)),
   .vg (.alu .and .r13 (.imm (-4))),
   .vg (.mov .r14 (.reg .r9)),
   .shrd .r15 .r9 2,
   .vg (.shift .shr .r9 2),
   .vg (.alu .add .r15 (.reg .r13)),
   .vg (.alu .adc .r9 (.reg .r14)),
   .vg (.alu .add .r10 (.reg .r15)),
   .vg (.alu .adc .r11 (.reg .r9)),
   .vg (.alu .adc .r12 (.imm 0))]

/-- The 13-byte AAD as the accumulator: its bytes 0 to 7 and 8 to 12, the
second word read from byte 5 and shifted, with the one bit above. -/
def load13 : List Instr :=
  [.vg (.mov .r10 (.mem (m .rcx 0))),
   .vg (.mov .r11 (.mem (m .rcx 5))),
   .vg (.shift .shr .r11 24),
   .vg (.mov .r12 (.imm 1))]

/-- The 13-byte AAD, times `r`. -/
def fast : List Instr := load13 ++ mul

/-- Add the 16-byte block at `rcx`, with the one bit above. -/
def addBlock : List Instr :=
  [.vg (.alu .add .r10 (.mem (m .rcx 0))),
   .vg (.alu .adc .r11 (.mem (m .rcx 8))),
   .vg (.alu .adc .r12 (.imm 1))]

/-- Step to the next block, and compare what is left with 16 bytes. -/
def next : List Instr :=
  [.lea .rcx (m .rcx 16),
   .vg (.alu .sub .r8 (.imm 16)),
   .vg (.alu .cmp .r8 (.imm 16))]

/-- A 16-byte block, with the one bit above, times `r`; then the next block,
and whether 16 bytes are left. -/
def block : List Instr := addBlock ++ mul ++ next

/-- The last, partial block: clear `(r13, r14)` and point `rcx` past it. -/
def tailInit : List Instr :=
  [.vg (.alu .xor .r13 (.reg .r13)),
   .vg (.alu .xor .r14 (.reg .r14)),
   .vg (.alu .xor .r15 (.reg .r15)),
   .vg (.alu .add .rcx (.reg .r8))]

/-- Shift `(r13, r14)` up a byte and put the byte before `rcx` in its low
byte, from the last byte down. -/
def tailByte : List Instr :=
  [.vg (.shld .r14 .r13 8),
   .vg (.shift .shl .r13 8),
   .vg (.movzx8 .r15 (m .rcx (-1))),
   .vg (.alu .xor .r13 (.reg .r15)),
   .dec .rcx,
   .dec .r8]

/-- Add the partial block in `(r13, r14)`, with the one bit above. -/
def addTail : List Instr :=
  [.vg (.alu .add .r10 (.reg .r13)),
   .vg (.alu .adc .r11 (.reg .r14)),
   .vg (.alu .adc .r12 (.imm 1))]

/-- The partial block, with the one bit above, times `r`. -/
def tailHash : List Instr := addTail ++ mul

/-- Any AAD but 13 bytes: the whole blocks, then the partial one, if any. -/
def general : Prog isa :=
  .seq (.block [.vg (.alu .cmp .r8 (.imm 16))]) <|
  .seq (.ite (.vg .b) (.block []) (.loop (.block block) (.vg .ae))) <|
  .seq (.block [.vg (.alu .cmp .r8 (.imm 0))]) <|
  .ite (.vg .e) (.block []) (.seq (.block tailInit) (.seq (.loop (.block tailByte) (.vg .ne)) (.block tailHash)))

def prog : Prog isa :=
  .seq (.block init) (.ite (.vg .ne) general (.block fast))

end Rind.X86_64.PolyHashAd
