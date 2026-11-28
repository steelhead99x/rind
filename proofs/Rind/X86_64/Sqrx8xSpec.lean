import Rind.X86_64.Sqrx8xAsm

/-! # bn_sqrx8x_internal's contract, and its phases'

The internal routine runs on its caller's frame, at `fp`, its stack pointer: the return address at word 0,
slots at words 1 to 6, and from word 7, byte 56, `t`'s `2k + 2` words, 16-byte aligned. Its caller,
`bn_sqrx8x_mont`, stores `n0` at slot 5 and its own stack pointer at slot 6, and zeroes `t`'s last two words;
the routine writes slots 1 to 4 and `t`. It squares `a`'s `k` words into `t`'s `2k`, then reduces them by `n`
eight words at a time, keeping each pass's eight multipliers in `t`'s first eight words, which it no longer
needs: `t`'s upper `k` words and `rax` are then `(a² + Q·n) / 2^(64k)` for some `Q < 2^(64k)`.

Its phases: clearing `t` and the first row's triangle (`entry`, `zero`, `init`), the triangle of products
`a_i·a_j`, `i < j` (`tri` and the passes), the shift and add of the squares (`shift`), and the reduction
(`redPass`'s loop). -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

namespace rind.x86_64.sqrx8x

/-- Word `i` of `t`, from byte 56 of the frame. -/
abbrev tw (M : Mem) (fp : Addr) (i : Nat) : BitVec 64 := M.readW (wa fp (i + 7)) 64

/-- The low 64 bits of an XMM register, which `movq r64, xmm` reads. -/
abbrev xlo (s : S) (x : XReg) : BitVec 64 := (s.vg.xmm x).setWidth 64

/-- What both the routine and each of its phases take: `k` a multiple of eight from eight, below `2^29`; the
arrays and the frame, apart (`Arr`); `t` 16-byte aligned; `a`'s and `n`'s words; `n0 = -n⁻¹ mod 2^64` at slot 5;
`n`'s and `-8k`'s in `xmm2` and `xmm3`. -/
structure Ctx (s : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64) : Prop where
  k8 : 8 ≤ k
  k0 : k % 8 = 0
  ar : Arr s k ap np fp
  al : (fp.toNat + 56) % 16 = 0
  hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i
  hN : ∀ i < k, s.vg.mem.readW (wa np i) 64 = n i
  s5 : s.vg.mem.readW (wa fp 5) 64 = n0
  n0 : ((n 0).toNat * n0.toNat + 1) % 2 ^ 64 = 0
  x2 : xlo s .xmm2 = np
  x3 : xlo s .xmm3 = BitVec.ofNat 64 (2 ^ 64 - 8 * k)

/-- `M'` matches `M` but in slots 1 to 4 and `t`'s `2k + 2` words. -/
def Keeps (M M' : Mem) (fp : Addr) (k : Nat) : Prop :=
  ∀ y, 32 ≤ (y - wa fp 1).toNat → 8 * (2 * k + 2) ≤ (y - wa fp 7).toNat → M' y = M y

/-- The routine's entry: its caller's `call` leaves the stack pointer at `fp`, `ap` in `rsi`, `8k` in `r9`, and
zero in `xmm0`; `t`'s last two words are zero; and the frame is below `2^63`, as every user-space stack is, since
a comparison of two of its pointers, whose overflow flag the next carry chain takes, overflows otherwise. -/
structure InPre (s : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64) : Prop where
  ctx : Ctx s k ap np fp a n n0
  k29 : k < 2 ^ 29
  rsp : s.vg.gpr .rsp = fp
  rsi : s.vg.gpr .rsi = ap
  r9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k)
  x0 : s.vg.xmm .xmm0 = 0
  t2k : tw s.vg.mem fp (2 * k) = 0
  t2k1 : tw s.vg.mem fp (2 * k + 1) = 0
  h63 : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 63

/-- The routine's result: `t`'s upper `k` words and `rax`, a bit, times `2^(64k)` are `a² + Q·n` for some
`Q < 2^(64k)`; `rcx` is `-8k`, `r8` the end of `t`, and `rbp` `np`; memory is as it was but in slots 1 to 4 and
`t`; and the stack pointer, the XMM registers, and the regions are as they were. -/
structure InPost (s s' : S) (k : Nat) (np fp : Addr) (a n : Nat → BitVec 64) : Prop where
  mont : ∃ Q, Q < 2 ^ (64 * k) ∧
    (val (fun i => tw s'.vg.mem fp (k + i)) k + (s'.vg.gpr .rax).toNat * 2 ^ (64 * k)) * 2 ^ (64 * k) =
      val a k * val a k + Q * val n k
  rax : (s'.vg.gpr .rax).toNat ≤ 1
  rcx : s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 * k)
  r8 : s'.vg.gpr .r8 = wa fp (2 * k + 7)
  rbp : s'.vg.gpr .rbp = np
  keeps : Keeps s.vg.mem s'.vg.mem fp k
  frame : Frame s s' [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-! ## The reduction's contract -/

/-- The reduction's entry, which the shift and add leaves: `t`'s `2k` words are `A`, its last two zero; `rdi` at
`t`, `rbp` at `n`, `rbx` `n0`, `rdx` `t`'s first word, `rax` and the flags zero; slot 1 `n`'s last eight words, and
slot 2 the end of `t`'s `2k`. -/
structure RedPre (s : S) (k : Nat) (ap np fp : Addr) (a n : Nat → BitVec 64) (n0 : BitVec 64) (A : Nat) : Prop
    where
  ctx : Ctx s k ap np fp a n n0
  rsp : s.vg.gpr .rsp = fp
  rdi : s.vg.gpr .rdi = wa fp 7
  rbp : s.vg.gpr .rbp = np
  rbx : s.vg.gpr .rbx = n0
  rdx : s.vg.gpr .rdx = tw s.vg.mem fp 0
  rax : s.vg.gpr .rax = 0
  cf : s.vg.cf = some false
  of : s.vg.of = some false
  s1 : s.vg.mem.readW (wa fp 1) 64 = wa np (k - 8)
  s2 : s.vg.mem.readW (wa fp 2) 64 = wa fp (2 * k + 7)
  val : val (tw s.vg.mem fp) (2 * k) = A
  t2k : tw s.vg.mem fp (2 * k) = 0
  t2k1 : tw s.vg.mem fp (2 * k + 1) = 0

/-- The reduction's result, as `InPost`'s, of `A` for `a²`. -/
structure RedPost (s s' : S) (k : Nat) (np fp : Addr) (n : Nat → BitVec 64) (A : Nat) : Prop where
  mont : ∃ Q, Q < 2 ^ (64 * k) ∧
    (val (fun i => tw s'.vg.mem fp (k + i)) k + (s'.vg.gpr .rax).toNat * 2 ^ (64 * k)) * 2 ^ (64 * k) =
      A + Q * val n k
  rax : (s'.vg.gpr .rax).toNat ≤ 1
  rcx : s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8 * k)
  r8 : s'.vg.gpr .r8 = wa fp (2 * k + 7)
  rbp : s'.vg.gpr .rbp = np
  keeps : Keeps s.vg.mem s'.vg.mem fp k
  frame : Frame s s' [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

end rind.x86_64.sqrx8x
