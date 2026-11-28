import RindIsa.X86_64

/-!
# BoringSSL's `gcm_init_vpclmulqdq_avx2`

rind's naked function `low::x86_64::aes_gcm_vaes::gcm_init_vpclmulqdq_avx2`,
BoringSSL's key setup for its AVX2 AES-GCM routines
(`crypto/fipsmodule/aes/asm/aes-gcm-avx2-x86_64.pl`), in rind's model of
x86_64: `gcm_init_vpclmulqdq_avx2(Htable = rdi, H = rsi)`. It loads the
GHASH key from the two words at `rsi`, high first, multiplies it by `x`
(`shift_key_1`), and writes its powers H^8 down to H^1 to the table's first
128 bytes and, for Karatsuba multiplication, each power's two halves XORed
to the next 64, two powers to a 256-bit multiply (`mul`), each a
schoolbook product folded twice by `gfpoly` (`x^63 + x^62 + x^57` in its
high word).

`admin/prove lean` checks that `function prog plainRet` is the function's
bytes and relocations as rind's Linux release build emits it, from
BoringSSL's text, which the blocks below follow line for line, and that its
statics begin with `gfpoly`'s and `carry`'s words.
-/

namespace Rind.X86_64.GcmInitAvx2

open VG VG.X86_64

/-- The static of the reduction constant. -/
def gfpolyName : String := "gfpoly"

/-- `gfpoly`: 1, and `x^63 + x^62 + x^57` reflected, in its high word. -/
def gfpoly : List (BitVec 64) := [1, 0xc200000000000000]

/-- The static `shift_key_1` adds by. -/
def carryName : String := "gfpoly_and_internal_carrybit"

/-- `gfpoly_and_internal_carrybit`: `gfpoly`, and the carry from the low word
into the high one. -/
def carry : List (BitVec 64) := [1, 0xc200000000000001]

def vop (o : VOp) : Instr := .vg (.vop o)

/-- `[rdi + d]` -/
def at_ (d : Int) : MemOp := { base := .rdi, disp := d }

/-- Load the key, swapping its words, and multiply it by `x`: shift each
word left, and add the carry out of the low word and, if the top bit fell
out, `gfpoly`, by masks of the sign bits `vpsrad` spreads. Then broadcast
`gfpoly` to both lanes of `ymm6`. -/
def head : List Instr :=
  [.vpshufdLoad .xmm3 { base := .rsi } 0x4e,
   vop (.vpshufd .l128 .xmm0 .xmm3 0xd3),
   vop (.vshift .psrad .l128 .xmm0 .xmm0 31),
   vop (.vbin .vpaddq .l128 .xmm3 .xmm3 .xmm3),
   .rip (.vbin .vpand .l128 .xmm0 .xmm0) carryName carry,
   vop (.vbin .vpxor .l128 .xmm3 .xmm3 .xmm0),
   .rip (.vbroadcasti128 .xmm6) gfpolyName gfpoly]

/-- Square H^1 in `xmm3` into H^2 in `xmm5`: the low and high products, the
low folded into the middle and the middle into the high. -/
def square : List Instr :=
  [vop (.vpclmulqdq .l128 .xmm0 .xmm3 .xmm3 0x00),
   vop (.vpclmulqdq .l128 .xmm5 .xmm3 .xmm3 0x11),
   vop (.vpclmulqdq .l128 .xmm1 .xmm6 .xmm0 0x01),
   vop (.vpshufd .l128 .xmm0 .xmm0 0x4e),
   vop (.vbin .vpxor .l128 .xmm1 .xmm1 .xmm0),
   vop (.vpclmulqdq .l128 .xmm0 .xmm6 .xmm1 0x01),
   vop (.vpshufd .l128 .xmm1 .xmm1 0x4e),
   vop (.vbin .vpxor .l128 .xmm5 .xmm5 .xmm1),
   vop (.vbin .vpxor .l128 .xmm5 .xmm5 .xmm0)]

/-- `_ghash_mul` of the two lanes of `a` by those of `b` into `d`: the low,
middle, and high schoolbook products, the low folded into the middle and the
middle into the high, by `gfpoly` in `ymm6`, with `ymm0` to `ymm2` as
scratch. -/
def mul (a b d : XReg) : List Instr :=
  [vop (.vpclmulqdq .l256 .xmm0 a b 0x00),
   vop (.vpclmulqdq .l256 .xmm1 a b 0x01),
   vop (.vpclmulqdq .l256 .xmm2 a b 0x10),
   vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm2),
   vop (.vpclmulqdq .l256 .xmm2 .xmm6 .xmm0 0x01),
   vop (.vpshufd .l256 .xmm0 .xmm0 0x4e),
   vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm0),
   vop (.vbin .vpxor .l256 .xmm1 .xmm1 .xmm2),
   vop (.vpclmulqdq .l256 d a b 0x11),
   vop (.vpclmulqdq .l256 .xmm0 .xmm6 .xmm1 0x01),
   vop (.vpshufd .l256 .xmm1 .xmm1 0x4e),
   vop (.vbin .vpxor .l256 d d .xmm1),
   vop (.vbin .vpxor .l256 d d .xmm0)]

/-- Store each power's two halves XORed, for the powers in the lanes of
`ymm4` and `ymm3`, to `[rdi + d]`. -/
def karatsuba (d : Int) : List Instr :=
  [vop (.vbin .vpunpcklqdq .l256 .xmm0 .xmm4 .xmm3),
   vop (.vbin .vpunpckhqdq .l256 .xmm1 .xmm4 .xmm3),
   vop (.vbin .vpxor .l256 .xmm0 .xmm0 .xmm1),
   .vg (.vmovdquStore .l256 (at_ d) .xmm0)]

/-- `[H^2, H^1]` in `ymm3` and `[H^2, H^2]` in `ymm5`; `[H^4, H^3]` in
`ymm4`; store them and their halves XORed in the order 4, 2, 3, 1; then
`[H^6, H^5]` in `ymm3` and `[H^8, H^7]` in `ymm4`, stored with theirs in
the order 8, 6, 7, 5. -/
def powers : List Instr :=
  [vop (.vinserti128 .xmm3 .xmm5 .xmm3 1),
   vop (.vinserti128 .xmm5 .xmm5 .xmm5 1)] ++
  mul .xmm3 .xmm5 .xmm4 ++
  [.vg (.vmovdquStore .l256 (at_ 96) .xmm3),
   .vg (.vmovdquStore .l256 (at_ 64) .xmm4)] ++
  karatsuba 160 ++
  mul .xmm4 .xmm5 .xmm3 ++
  mul .xmm3 .xmm5 .xmm4 ++
  [.vg (.vmovdquStore .l256 (at_ 32) .xmm3),
   .vg (.vmovdquStore .l256 (at_ 0) .xmm4)] ++
  karatsuba 128 ++
  [vop .vzeroupper]

/-- The function, but for its `ret`. -/
def prog : Prog isa := .block (head ++ square ++ powers)

end Rind.X86_64.GcmInitAvx2
