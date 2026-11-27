import Rind.X86_64.Mul4xHead
import Rind.X86_64.Mul4xOuter
import Rind.X86_64.Mul4xFinal
import VerifiedGarbage.TCB.X86_64.Target

open VG VG.X86_64 Rind.X86_64.Mul4x rind.x86_64.asm

set_option linter.unusedSimpArgs false

/-!
# aws-lc's `bn_mul4x_mont`, proven

`bn_mul4x_mont_correct`: the routine `RindIsa/X86_64/Mul4x.lean` gives as
`prog`, which `admin/prove lean` checks is the machine code of rind's naked
function `low::x86_64::mont::bn_mul4x_mont` as rind's Linux release build
emits it, run in rind's extension of VG's x86_64 model
(`RindIsa/X86_64.lean`) from a state `Pre` holds of, terminates in one that
`Post` relates it to: the `k` words at `rp` become the Montgomery product of
the `k` words at `ap` and `bp` modulo those at `np`, below the modulus;
nothing changes but those words and the frame of `8k + 1104` bytes below the
stack pointer; and the registers the System V ABI makes the callee save, the
stack pointer among them, and the return address are as they were, with `rax`
1. Its trace of addresses and branches is a function of the arguments and the
stack pointer alone (`ConstantTime`, with `Pub`), and some state meets `Pre`.

The proof runs each block symbolically (`Mul4xAsm`, `Mul4xTailAsm`,
`Mul4xHeadAsm`), inducts over the loops (`Mul4xLoop`, `Mul4xOuter`,
`Mul4xFinal`, `Mul4xHead`), and shows each pass is a Montgomery step and the
last subtraction and selection reduce the result below the modulus
(`Mul4xModel`, `Mul4xSub`). Every theorem rests only on Lean's three axioms.
-/

namespace rind.x86_64.mul4x

/-- Word `i` of the array at `p`. -/
def words (M : Mem) (p : Addr) (i : Nat) : BitVec 64 := M.readW (wa p i) 64

/-- The width, `num`, which the routine reads as 32 bits. -/
def num (s : S) : Nat := (s.vg.gpr .r9).toNat

/-- The bytes below the stack pointer the routine may use, for `k` words: its pushes and `tp`'s `k + 3` words,
1024-byte aligned. -/
def frameLen (k : Nat) : Nat := 8 * k + 1104

/-- `len` bytes at `p`, without wrapping, apart from the frame and the return address,
`[sp0 - frameLen k, sp0 + 8)`. -/
def OffFrame (p : Addr) (len : Nat) (sp0 : Addr) (k : Nat) : Prop :=
  p.toNat + len ≤ 2 ^ 64 ∧ (p.toNat + len ≤ sp0.toNat - frameLen k ∨ sp0.toNat + 8 ≤ p.toNat)

/-- The pushes of the callee-saved registers `g` below `sp0`. -/
def pushes (M : Mem) (sp0 : Addr) (g : Reg → BitVec 64) : Mem :=
  (((((M.writeW (sp0 - BitVec.ofNat 64 8) (g .rbx)).writeW (sp0 - BitVec.ofNat 64 16) (g .rbp)).writeW
    (sp0 - BitVec.ofNat 64 24) (g .r12)).writeW (sp0 - BitVec.ofNat 64 32) (g .r13)).writeW
    (sp0 - BitVec.ofNat 64 40) (g .r14)).writeW (sp0 - BitVec.ofNat 64 48) (g .r15)

theorem pushes_byte (M : Mem) (sp0 y : Addr) (g : Reg → BitVec 64) (_hsp : 48 ≤ sp0.toNat)
    (hy : 48 ≤ (y - (sp0 - BitVec.ofNat 64 48)).toNat) : pushes M sp0 g y = M y := by
  unfold pushes Mem.writeW
  repeat rw [write_other _ _ _ _ _ (by bv_omega)]

theorem pushes_readW (M : Mem) (sp0 x : Addr) (g : Reg → BitVec 64) (hsp : 48 ≤ sp0.toNat)
    (hx : ∀ b < 8, 48 ≤ (x + BitVec.ofNat 64 b - (sp0 - BitVec.ofNat 64 48)).toNat) :
    (pushes M sp0 g).readW x 64 = M.readW x 64 := by
  simp only [Mem.readW]; congr 1; apply read_congr; intro b hb
  exact pushes_byte M sp0 _ g hsp (hx b (by omega))

theorem pushes_saved (M : Mem) (sp0 : Addr) (g : Reg → BitVec 64) (_hsp : 48 ≤ sp0.toNat) :
    (pushes M sp0 g).readW (sp0 - 48#64) 64 = g .r15 ∧ (pushes M sp0 g).readW (sp0 - 40#64) 64 = g .r14 ∧
      (pushes M sp0 g).readW (sp0 - 32#64) 64 = g .r13 ∧ (pushes M sp0 g).readW (sp0 - 24#64) 64 = g .r12 ∧
      (pushes M sp0 g).readW (sp0 - 16#64) 64 = g .rbp ∧ (pushes M sp0 g).readW (sp0 - 8#64) 64 = g .rbx := by
  unfold pushes
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    repeat (first
      | rw [readW_writeW_self]
      | rw [readW_writeW_sep _ _ _ _ (by unfold Apart; constructor <;> bv_omega)])

theorem lose_readW (m : Mem) (a x : Addr) (n : Nat) (u : Nat → BitVec 64)
    (h : ∀ b < 8, n ≤ (x + BitVec.ofNat 64 b - a).toNat) : (lose m a n u).readW x 64 = m.readW x 64 := by
  simp only [Mem.readW]; congr 1; apply read_congr; intro b hb
  have := h b (by omega)
  simp only [lose]; split <;> first | rfl | omega

theorem lose_byte (m : Mem) (a y : Addr) (n : Nat) (u : Nat → BitVec 64) (h : n ≤ (y - a).toNat) :
    lose m a n u y = m y := by
  simp only [lose]; split <;> first | rfl | omega

theorem others_mxcsr {g g' : VG.X86_64.State} (h : others g' = others g) : g'.mxcsr = g.mxcsr :=
  congrArg (fun x => x.2.2.2.2.1) h

theorem others_rd {g g' : VG.X86_64.State} (h : others g' = others g) : g'.rd = g.rd :=
  congrArg (fun x => x.2.2.2.2.2.1) h

theorem val_congr {f g : Nat → BitVec 64} {m : Nat} (h : ∀ i < m, f i = g i) : val f m = val g m :=
  gsum_congr fun i hi => by rw [h i hi]

theorem stack_off (x tp rp sp0 : Addr) (k c : Nat) (hc : c < 8) (h1 : tp.toNat + 8 * (k + 1) ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ sp0.toNat + 8) (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hp : rp.toNat + 8 * k ≤ 2 ^ 64)
    (htp : sp0.toNat ≤ tp.toNat + 8 * k + 1103)
    (hoff : rp.toNat + 8 * k ≤ sp0.toNat - (8 * k + 1104) ∨ sp0.toNat + 8 ≤ rp.toNat) :
    8 * (k + 1) ≤ (x + BitVec.ofNat 64 c - tp).toNat ∧ 8 * k ≤ (x + BitVec.ofNat 64 c - rp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> rcases hoff with h | h <;> omega

theorem push_off (sp0 tp : Addr) (k c b : Nat) (hb : b < 8) (c1 : 8 ≤ c) (c2 : c ≤ 48)
    (htp : tp.toNat + 8 * k + 80 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64) :
    8 * (k + 3) ≤ (sp0 - BitVec.ofNat 64 c + BitVec.ofNat 64 b - tp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem rp_lose (rp tp sp0 : Addr) (k i c : Nat) (hi : i < k) (hc : c < 8) (hp : rp.toNat + 8 * k ≤ 2 ^ 64)
    (hoff : rp.toNat + 8 * k ≤ sp0.toNat - (8 * k + 1104) ∨ sp0.toNat + 8 ≤ rp.toNat)
    (htp1 : tp.toNat + 8 * k + 80 ≤ sp0.toNat) (htp2 : sp0.toNat ≤ tp.toNat + 8 * k + 1103)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) : sp0.toNat - tp.toNat ≤ (wa rp i + BitVec.ofNat 64 c - tp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, wa_toNat hp hi, BitVec.toNat_ofNat]
  rcases hoff with h | h <;> omega

theorem frame_off (y tp sp0 : Addr) (k : Nat) (hF : 8 * k + 1104 ≤ sp0.toNat)
    (htp1 : tp.toNat + 8 * k + 80 ≤ sp0.toNat) (htp2 : sp0.toNat ≤ tp.toNat + 8 * k + 1103)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hy : 8 * k + 1104 ≤ (y - (sp0 - BitVec.ofNat 64 (8 * k + 1104))).toNat) :
    sp0.toNat - tp.toNat ≤ (y - tp).toNat ∧ 48 ≤ (y - (sp0 - BitVec.ofNat 64 48)).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hy ⊢
  have := y.isLt
  constructor <;> omega

theorem ret_off (rp sp0 : Addr) (k c : Nat) (hc : c < 8) (hF : 8 * k + 1104 ≤ sp0.toNat)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hp : rp.toNat + 8 * k ≤ 2 ^ 64)
    (hoff : rp.toNat + 8 * k ≤ sp0.toNat - (8 * k + 1104) ∨ sp0.toNat + 8 ≤ rp.toNat) :
    8 * k ≤ (sp0 + BitVec.ofNat 64 c - rp).toNat ∧
      8 * k + 1104 ≤ (sp0 + BitVec.ofNat 64 c - (sp0 - BitVec.ofNat 64 (8 * k + 1104))).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> rcases hoff with h | h <;> omega

/-! ## The routine -/

/-- The theorem's hypotheses, `rp = rdi`, `ap = rsi`, `bp = rdx`, `np = rcx`, `n0 = r8`, and `num = r9`: `num` a
multiple of four from eight, below `2^32`; the routine may read `ap`, `bp`, and `np`'s `num` words and the word at
`n0`, and write `rp`'s and the stack's below the return address, which `lo` bounds to `frameLen num` bytes; none of
the arrays overlaps that frame or the return address, nor `rp` `np`; `n0` is `-np⁻¹ mod 2^64`; and `ap`'s value is
below `np`'s. The arrays may overlap each other but `rp` and `np`, since the routine writes `rp` only after its last
read of `ap` and `bp`. -/
structure Pre (s : S) : Prop where
  k8 : 8 ≤ num s
  k4 : num s % 4 = 0
  k32 : num s < 2 ^ 32
  wr : ∃ rest, s.vg.wr = ⟨s.vg.gpr .rsp, 8⟩ :: rest ∧ ⟨s.vg.gpr .rdi, 8 * num s⟩ ∈ rest
  rA : ⟨s.vg.gpr .rsi, 8 * num s⟩ ∈ s.vg.rd
  rB : ⟨s.vg.gpr .rdx, 8 * num s⟩ ∈ s.vg.rd
  rN : ⟨s.vg.gpr .rcx, 8 * num s⟩ ∈ s.vg.rd
  rN0 : ⟨s.vg.gpr .r8, 8⟩ ∈ s.vg.rd
  lo : s.lo.toNat + frameLen (num s) ≤ (s.vg.gpr .rsp).toNat
  sp : (s.vg.gpr .rsp).toNat + 8 ≤ 2 ^ 64
  oA : OffFrame (s.vg.gpr .rsi) (8 * num s) (s.vg.gpr .rsp) (num s)
  oB : OffFrame (s.vg.gpr .rdx) (8 * num s) (s.vg.gpr .rsp) (num s)
  oN : OffFrame (s.vg.gpr .rcx) (8 * num s) (s.vg.gpr .rsp) (num s)
  oN0 : OffFrame (s.vg.gpr .r8) 8 (s.vg.gpr .rsp) (num s)
  oP : OffFrame (s.vg.gpr .rdi) (8 * num s) (s.vg.gpr .rsp) (num s)
  sepPN : (s.vg.gpr .rdi).toNat + 8 * num s ≤ (s.vg.gpr .rcx).toNat ∨
    (s.vg.gpr .rcx).toNat + 8 * num s ≤ (s.vg.gpr .rdi).toNat
  n0 : ((words s.vg.mem (s.vg.gpr .rcx) 0).toNat * (s.vg.mem.readW (s.vg.gpr .r8) 64).toNat + 1) % 2 ^ 64 = 0
  lt : val (words s.vg.mem (s.vg.gpr .rsi)) (num s) < val (words s.vg.mem (s.vg.gpr .rcx)) (num s)

/-- What the routine ensures: `rp`'s words are below `np`'s and, times `2^(64 num)`, are `ap`'s times `bp`'s modulo
`np`'s; memory but `rp` and the frame is unchanged; the registers the System V ABI makes the callee save, the stack
pointer among them, and the return address are as they were; it returns 1; and its regions are as they were. -/
structure Post (s s' : S) : Prop where
  lt : val (words s'.vg.mem (s.vg.gpr .rdi)) (num s) < val (words s.vg.mem (s.vg.gpr .rcx)) (num s)
  mont : val (words s'.vg.mem (s.vg.gpr .rdi)) (num s) * 2 ^ (64 * num s) % val (words s.vg.mem (s.vg.gpr .rcx)) (num s) =
    val (words s.vg.mem (s.vg.gpr .rsi)) (num s) * val (words s.vg.mem (s.vg.gpr .rdx)) (num s) %
      val (words s.vg.mem (s.vg.gpr .rcx)) (num s)
  mem : ∀ y, 8 * num s ≤ (y - s.vg.gpr .rdi).toNat →
    frameLen (num s) ≤ (y - (s.vg.gpr .rsp - BitVec.ofNat 64 (frameLen (num s)))).toNat → s'.vg.mem y = s.vg.mem y
  abi : abiPreserved s.vg s'.vg
  rax : s'.vg.gpr .rax = 1
  wr : s'.vg.wr = s.vg.wr
  rd : s'.vg.rd = s.vg.rd

/-- What is public: the arguments and the stack pointer. The arrays' and `n0`'s values are not. -/
def Pub (s₁ s₂ : S) : Prop :=
  s₁.vg.gpr .rdi = s₂.vg.gpr .rdi ∧ s₁.vg.gpr .rsi = s₂.vg.gpr .rsi ∧ s₁.vg.gpr .rdx = s₂.vg.gpr .rdx ∧
    s₁.vg.gpr .rcx = s₂.vg.gpr .rcx ∧ s₁.vg.gpr .r8 = s₂.vg.gpr .r8 ∧ s₁.vg.gpr .r9 = s₂.vg.gpr .r9 ∧
    s₁.vg.gpr .rsp = s₂.vg.gpr .rsp

/-- The routine's trace, of the arguments, the width, and the stack pointer. -/
def traceOf (rp ap bp np n0p sp0 : Addr) (k : Nat) : List Leak :=
  let tp := tpOf sp0 k
  (prologueATrace sp0 ++ [.addr (tp + pagesOf sp0 tp)]) ++
    (walkTrace tp ((pagesOf sp0 tp).toNat / 4096) ++
    (body0Trace ap bp np n0p tp k ++
    (loopTrace (firstTrace ap np tp) 4 1 ((k - 8) / 4) ++
    (firstTailTrace ap np tp (k - 3) ++
    (outerTrace ap bp np tp k ++
    (finalTrace np tp k ++
    (subLoopTrace np tp rp k ++
    (subTailTrace np tp rp (k - 4) ++
    (copyLoopTrace tp rp k ++ epilogueTrace tp sp0 k)))))))))

/-- The routine's trace from `s`, a function of what is public. -/
def trace (s : S) : List Leak :=
  traceOf (s.vg.gpr .rdi) (s.vg.gpr .rsi) (s.vg.gpr .rdx) (s.vg.gpr .rcx) (s.vg.gpr .r8) (s.vg.gpr .rsp) (num s)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem correct (s : S) (h : Pre s) : ∃ s', Exec I prog s (trace s) s' ∧ Post s s' := by
  obtain ⟨k8, k4, k32, ⟨rest, hwr, hrpw⟩, rA, rB, rN, rN0, hlo, hsp, oA, oB, oN, oN0, oP, sepPN, hn0, hlt⟩ := h
  have hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (num s) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold num; omega
  unfold trace
  generalize hk : num s = k at *
  unfold frameLen at hlo
  unfold OffFrame frameLen at oA oB oN oN0 oP
  generalize hsp0 : s.vg.gpr .rsp = sp0 at *
  generalize hrdi : s.vg.gpr .rdi = rp at *
  generalize hrsi : s.vg.gpr .rsi = ap at *
  generalize hrdx : s.vg.gpr .rdx = bp at *
  generalize hrcx : s.vg.gpr .rcx = np at *
  generalize hr8 : s.vg.gpr .r8 = n0p at *
  set a := words s.vg.mem ap with ha
  set bw := words s.vg.mem bp with hb
  set n := words s.vg.mem np with hn
  set n0' := s.vg.mem.readW n0p 64 with hn0'
  -- The prologue and the walk.
  obtain ⟨s₁, s₂, hx1, hx2, h_sp, h_ax, h_9, h_wr, h_mem, h_g, h_oth, h_mx, h_lo⟩ :=
    head_ok s k sp0 rest k32 (by omega) hsp hsp0 hr9 hwr
  have htp := tpOf_toNat sp0 k k32 (by omega)
  simp only [traceOf]
  generalize tpOf sp0 k = tp at *
  have t1 := Nat.div_add_mod (sp0.toNat - 8 * k - 80) 1024
  have t2 := Nat.mod_lt (sp0.toNat - 8 * k - 80) (show 1024 > 0 by norm_num)
  have T : tp.toNat + 8 * k + 80 ≤ sp0.toNat ∧ sp0.toNat ≤ tp.toNat + 8 * k + 1103 ∧ tp.toNat % 1024 = 0 := by
    rw [htp]; omega
  clear t1 t2
  obtain ⟨T1, T2, T3⟩ := T
  have hmem2 : s₂.vg.mem = pushes s.vg.mem sp0 s.vg.gpr := h_mem
  have hsp48 : 48 ≤ sp0.toNat := by omega
  -- An array word apart from the frame reads as it did.
  have off2 : ∀ (p : Addr) (L i : Nat), p.toNat + 8 * L ≤ 2 ^ 64 →
      (p.toNat + 8 * L ≤ sp0.toNat - (8 * k + 1104) ∨ sp0.toNat + 8 ≤ p.toNat) → i < L →
      s₂.vg.mem.readW (wa p i) 64 = s.vg.mem.readW (wa p i) 64 := by
    intro p L i hp hoff hi
    rw [hmem2]
    apply pushes_readW _ _ _ _ hsp48
    intro c hc
    rw [BitVec.toNat_sub, BitVec.toNat_add, wa_toNat hp hi, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rcases hoff with h | h <;> omega
  have rd2 : s₂.vg.rd = s.vg.rd := others_rd h_oth
  have sepX : ∀ (p : Addr) (L : Nat), (p.toNat + L ≤ sp0.toNat - (8 * k + 1104) ∨ sp0.toNat + 8 ≤ p.toNat) →
      p.toNat + L ≤ tp.toNat ∨ tp.toNat + 8 * (k + 3) ≤ p.toNat := fun p L h => by omega
  have ar2 : Arrays s₂ k ap bp np n0p tp :=
    ⟨k32, oA.1, oB.1, oN.1, oN0.1, by omega, sepX _ _ oA.2, sepX _ _ oB.2, sepX _ _ oN.2, sepX _ _ oN0.2,
      by rw [rd2]; exact List.mem_append_left _ rA, by rw [rd2]; exact List.mem_append_left _ rB,
      by rw [rd2]; exact List.mem_append_left _ rN, by rw [rd2]; exact List.mem_append_left _ rN0,
      sp0.toNat + 8 - tp.toNat, by omega, by rw [h_wr]; exact List.mem_cons_self⟩
  have out2 : Out s₂ k np tp rp := ⟨oP.1, sepX _ _ oP.2, sepPN, by rw [h_wr]; exact List.mem_cons_of_mem _ hrpw⟩
  have hA2 : ∀ i < k, s₂.vg.mem.readW (wa ap i) 64 = a i := fun i hi => off2 ap k i oA.1 oA.2 hi
  have hB2 : ∀ i < k, s₂.vg.mem.readW (wa bp i) 64 = bw i := fun i hi => off2 bp k i oB.1 oB.2 hi
  have hN2 : ∀ i < k, s₂.vg.mem.readW (wa np i) 64 = n i := fun i hi => off2 np k i oN.1 oN.2 hi
  have hn02 : s₂.vg.mem.readW n0p 64 = n0' := by
    have := off2 n0p 1 0 (by omega) (by omega) (by omega); rwa [wa_zero] at this
  have g2 : ∀ r, r ∉ [Reg.rsp, .rax, .r9, .r10, .r11] → s₂.vg.gpr r = s.vg.gpr r := h_g
  have hn0w : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0 := hn0
  -- The first pass.
  obtain ⟨s₃, s₄, s₅, hx3, hx4, hx5, p_ax, p14, p12, p8, pw, pS, pR, pAg, pF⟩ :=
    pass0_ok s₂ k ap bp np n0p tp rp sp0 n0' a bw n k8 k4 ar2 ((g2 .rsi (by decide)).trans hrsi)
      ((g2 .rdx (by decide)).trans hrdx) ((g2 .rcx (by decide)).trans hrcx) ((g2 .r8 (by decide)).trans hr8) h_sp
      ((g2 .rdi (by decide)).trans hrdi) h_ax h_9 hA2 hN2 hB2 hn02
  have ar5 := ar2.frame pF
  have hNpos : 0 < val n k := by omega
  have hI1 : OuterInv s₅ s₅ k tp a bw n 1 := by
    refine ⟨Frame.refl _ _, p_ax, p14, Agree.refl _ _ _, fun i => s₅.vg.mem.readW (wa tp i) 64, fun j _ => rfl, ?_⟩
    rw [val_congr (m := k + 1) fun i hi => pw i (by omega)]
    obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
    have hP := pass0_nat a n (bw 0) (n0' * mulLo (a 0) (bw 0)) K (mac_q (n 0) n0' _ hn0w)
    obtain ⟨h1, h2⟩ := mont_step (val a (K + 1)) (val n (K + 1)) 0 _ 0 0 (bw 0).toNat
      (n0' * mulLo (a 0) (bw 0)).toNat 0 (bw 0).isLt (BitVec.isLt _) (by rw [hP]; ring) (by omega) (by simp)
    refine ⟨h1, 0 + 2 ^ (64 * 0) * (n0' * mulLo (a 0) (bw 0)).toNat, ?_⟩
    rw [h2]; simp [val, gsum]
  have hr9_5 : s₅.vg.gpr .r9 = BitVec.ofNat 64 k := (pF.gpr .r9 (by decide)).trans h_9
  have hA5 : ∀ i < k, s₅.vg.mem.readW (wa ap i) 64 = a i := fun i hi =>
    (pAg.arr (by omega) ar2.htp oA.1 ar2.sepA hi).trans (hA2 i hi)
  have hB5 : ∀ i < k, s₅.vg.mem.readW (wa bp i) 64 = bw i := fun i hi =>
    (pAg.arr (by omega) ar2.htp oB.1 ar2.sepB hi).trans (hB2 i hi)
  have hN5 : ∀ i < k, s₅.vg.mem.readW (wa np i) 64 = n i := fun i hi =>
    (pAg.arr (by omega) ar2.htp oN.1 ar2.sepN hi).trans (hN2 i hi)
  -- The other passes.
  obtain ⟨s₆, hx6, hI6⟩ := outer_ok s₅ k ap bp np n0p tp n0' a bw n k8 k4 ar5
    ((pF.gpr .rsi (by decide)).trans ((g2 .rsi (by decide)).trans hrsi))
    ((pF.gpr .rcx (by decide)).trans ((g2 .rcx (by decide)).trans hrcx))
    ((pF.gpr .rsp (by decide)).trans h_sp) p12 p8 hr9_5 hA5 hN5 hB5 hn0w hI1
  obtain ⟨F6, -, -, ag6, t, hT6, hV, Q, hQ⟩ := hI6
  have ar6 := ar5.frame F6
  have out6 := (out2.frame pF).frame F6
  have hN6 : ∀ i < k, s₆.vg.mem.readW (wa np i) 64 = n i := fun i hi =>
    (ag6.arr (by omega) ar2.htp oN.1 ar2.sepN hi).trans (hN5 i hi)
  have hrp6 : s₆.vg.mem.readW (wa tp (k + 2)) 64 = rp := (ag6.tp (by omega) (by omega) ar2.htp).trans pR
  have F26 := pF.trans (F6.mono (by decide))
  have g6 : ∀ r, r ∉ [Reg.rax, .rdx, .rdi, .rbx, .rbp, .r8, .r10, .r11, .r12, .r13, .r14, .r15] →
      s₆.vg.gpr r = s₂.vg.gpr r := F26.gpr
  -- The subtraction.
  obtain ⟨s₇, s₈, s₉, hx7, hx8, hx9, x0, x4, x5, r15_9, ax9, di9, hD9, ag9, F9⟩ :=
    subPhase_ok s₆ k ap bp np n0p tp rp t n k8 k4 ar6 out6 ((g6 .rcx (by decide)).trans ((g2 .rcx (by decide)).trans hrcx))
      ((g6 .rsp (by decide)).trans h_sp) ((g6 .r9 (by decide)).trans h_9) hN6 hT6 hrp6
  have ar9 := ar6.frameX F9
  have out9 := out6.frameX F9
  have hp := oP.1
  have hsepT := out2.sepT
  have ht2 : val t (k + 1) < 2 * val n k := by omega
  obtain ⟨hmask, hsel_lt, hsel_mod⟩ := select_nat t n k hNpos ht2
  have hT9 : ∀ i < k, s₉.vg.mem.readW (wa tp i) 64 = t i := fun i hi =>
    (ag9.apart (L := k) le_rfl hp (by rw [wa_toNat (k := k + 3) ar2.htp (by omega)]; omega)
      (by rw [wa_toNat (k := k + 3) ar2.htp (by omega)]; rcases hsepT with h | h <;> omega)).trans (hT6 i (by omega))
  -- The copy.
  obtain ⟨s₁₀, hx10, hC⟩ := copyPhase_ok s₉ k ap bp np n0p tp rp t n k8 k4 ar9 out9 (by omega) di9
    ((F9.gpr .rsp (by decide)).trans ((g6 .rsp (by decide)).trans h_sp)) ax9 r15_9 hmask x4
    (by rw [x5, pcmpeqd_self]) hT9 hD9
  have F10 := hC.frame
  -- Bytes past `tp`'s `k + 1` words and apart from `rp`'s keep the values the first pass left.
  have keep5 : ∀ y, 8 * (k + 1) ≤ (y - tp).toNat → 8 * k ≤ (y - rp).toNat → s₁₀.vg.mem y = s₅.vg.mem y :=
    fun y h1 h2 => (hC.agree y (by omega) h2).trans ((ag9 y h2).trans (ag6 y h1))
  have keepW : ∀ x, (∀ c < 8, 8 * (k + 1) ≤ (x + BitVec.ofNat 64 c - tp).toNat ∧
      8 * k ≤ (x + BitVec.ofNat 64 c - rp).toNat) → s₁₀.vg.mem.readW x 64 = s₅.vg.mem.readW x 64 := by
    intro x hx
    simp only [Mem.readW]; congr 1; apply read_congr; intro c hc
    exact keep5 _ (hx c (by omega)).1 (hx c (by omega)).2
  -- The stack's words above `tp`'s `k + 1`.
  have stackW : ∀ x : Addr, tp.toNat + 8 * (k + 1) ≤ x.toNat → x.toNat + 8 ≤ sp0.toNat + 8 →
      s₁₀.vg.mem.readW x 64 = s₅.vg.mem.readW x 64 := by
    intro x h1 h2
    exact keepW x fun c hc => stack_off x tp rp sp0 k c hc h1 h2 hsp oP.1 T2 oP.2
  have hS10 : s₁₀.vg.mem.readW (wa tp (k + 1)) 64 = sp0 :=
    (stackW _ (by rw [wa_toNat (k := k + 3) ar2.htp (by omega)]) (by rw [wa_toNat (k := k + 3) ar2.htp (by omega)]; omega)).trans pS
  have hsave : ∀ c, 8 ≤ c → c ≤ 48 → c % 8 = 0 →
      s₁₀.vg.mem.readW (sp0 - BitVec.ofNat 64 c) 64 = s₂.vg.mem.readW (sp0 - BitVec.ofNat 64 c) 64 := by
    intro c c1 c2 c3
    have e : (sp0 - BitVec.ofNat 64 c).toNat = sp0.toNat - c := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [stackW _ (by omega) (by omega)]
    exact readW_agree pAg fun b hb => push_off sp0 tp k c b hb c1 c2 (by omega) hsp
  obtain ⟨v15, v14, v13, v12, vbp, vbx⟩ := pushes_saved s.vg.mem sp0 s.vg.gpr hsp48
  rw [← hmem2] at v15 v14 v13 v12 vbp vbx
  have F610 := F9.trans (F10.mono (by decide))
  have hwr10 : s₁₀.vg.wr = ⟨tp, sp0.toNat + 8 - tp.toNat⟩ :: rest := by
    rw [F610.wr, F6.wr, pF.wr, h_wr]
  -- The epilogue.
  obtain ⟨s₁₁, hx11, e_sp, e_ax, e15, e14, e13, e12, ebp, ebx, ewr, erd, emx, elo, emem⟩ :=
    epilogue_ok s₁₀ k (sp0.toNat + 8 - tp.toNat) tp sp0 _ _ _ _ _ _ rest k32 (by omega) hsp
      ((F610.gpr .rsp (by decide)).trans ((g6 .rsp (by decide)).trans h_sp))
      ((F610.gpr .r9 (by decide)).trans ((g6 .r9 (by decide)).trans h_9)) hwr10 rfl hS10
      ((hsave 48 (by omega) le_rfl rfl).trans v15) ((hsave 40 (by omega) (by omega) rfl).trans v14)
      ((hsave 32 (by omega) (by omega) rfl).trans v13) ((hsave 24 (by omega) (by omega) rfl).trans v12)
      ((hsave 16 (by omega) (by omega) rfl).trans vbp) ((hsave 8 le_rfl (by omega) rfl).trans vbx)
  -- The result.
  have hR : ∀ i < k, words s₁₁.vg.mem rp i = select t n k i := fun i hi => by
    unfold words
    rw [emem, lose_readW _ _ _ _ _ fun c hc => rp_lose rp tp sp0 k i c hi hc oP.1 oP.2 T1 T2 hsp]
    exact hC.words i hi
  have hRv : val (words s₁₁.vg.mem rp) k = val (select t n k) k := val_congr hR
  have hmemP : ∀ y, 8 * k ≤ (y - rp).toNat → 8 * k + 1104 ≤ (y - (sp0 - BitVec.ofNat 64 (8 * k + 1104))).toNat →
      s₁₁.vg.mem y = s.vg.mem y := by
    intro y h1 h2
    obtain ⟨f1, f2⟩ := frame_off y tp sp0 k (by omega) T1 T2 hsp h2
    rw [emem, lose_byte _ _ _ _ _ f1, keep5 y (by omega) h1, pAg y (by omega), hmem2,
      pushes_byte _ _ _ _ hsp48 f2]
  refine ⟨s₁₁, Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 (Exec.seq hx4 (Exec.seq hx5 (Exec.seq hx6
    (Exec.seq hx7 (Exec.seq hx8 (Exec.seq hx9 (Exec.seq hx10 (Exec.block hx11)))))))))), ?_⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, e_ax, by rw [ewr, hwr], ?_⟩
  · rw [hrdi, hrcx, hk, hRv]; exact hsel_lt
  · rw [hrdi, hrcx, hrsi, hrdx, hk, hRv]
    show val (select t n k) k * 2 ^ (64 * k) % val n k = val a k * val bw k % val n k
    rw [Nat.mul_mod, hsel_mod, ← Nat.mul_mod, Nat.mul_comm, hQ, Nat.add_mul_mod_self_right]
  · rw [hrdi, hsp0, hk]; unfold frameLen; exact hmemP
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ebx
    · exact ebp
    · rw [e_sp, hsp0]
    · exact e12
    · exact e13
    · exact e14
    · exact e15
  · rw [hsp0]
    simp only [Mem.readW]; congr 1; apply read_congr; intro c hc
    obtain ⟨r1, r2⟩ := ret_off rp sp0 k c hc (by omega) hsp oP.1 oP.2
    exact hmemP _ r1 r2
  · rw [emx, others_mxcsr F610.others, others_mxcsr F26.others, h_mx]
  · rw [erd, F610.rd, F26.rd, rd2]

theorem constant_time : ConstantTime I Pre Pub prog := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨e0, e1, e2, e3, e4, e5, e6⟩ x₁ x₂
  obtain ⟨_, y₁, -⟩ := correct s₁ h₁
  obtain ⟨_, y₂, -⟩ := correct s₂ h₂
  rw [(exec_det x₁ y₁).1, (exec_det x₂ y₂).1]
  simp only [trace, num, e0, e1, e2, e3, e4, e5, e6]

/-! ## The precondition holds of some state -/

/-- Memory holding the modulus 1 at `0x203000` and `n0 = -1` at `0x204000`, and zeros elsewhere. -/
def witnessMem : Mem := fun x =>
  if x = 0x203000#64 then 1 else if (x - 0x204000#64).toNat < 8 then 0xFF else 0

/-- A state the precondition holds of: eight words, `rp` at `0x200000`, `ap`, `bp`, and `np` after it, the stack
pointer at `0x100000`. -/
def witness : S where
  vg := { gpr := fun r => if r = .rdi then 0x200000#64 else if r = .rsi then 0x201000#64
            else if r = .rdx then 0x202000#64 else if r = .rcx then 0x203000#64 else if r = .r8 then 0x204000#64
            else if r = .r9 then 8#64 else if r = .rsp then 0x100000#64 else 0,
          cf := none, zf := none, sf := none, of := none,
          mem := witnessMem,
          rd := [⟨0x201000#64, 64⟩, ⟨0x202000#64, 64⟩, ⟨0x203000#64, 64⟩, ⟨0x204000#64, 8⟩],
          wr := [⟨0x100000#64, 8⟩, ⟨0x200000#64, 64⟩] }
  lo := 0

set_option exponentiation.threshold 512 in
set_option maxRecDepth 8192 in
theorem pre_witness : Pre witness := by
  have hk : num witness = 8 := by decide
  refine ⟨?_, ?_, ?_, ⟨[⟨0x200000#64, 64⟩], rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [hk, OffFrame, frameLen]) <;> decide

/-- The routine computes the Montgomery product of its arguments, keeping what the System V ABI and its contract
require; its trace depends only on its arguments and the stack pointer; and some state meets its precondition. -/
theorem bn_mul4x_mont_correct :
    (∀ s, Pre s → ∃ t s', Exec I prog s t s' ∧ Post s s') ∧ ConstantTime I Pre Pub prog ∧ ∃ s, Pre s :=
  ⟨fun s h => let ⟨s', e, p⟩ := correct s h; ⟨_, s', e, p⟩, constant_time, _, pre_witness⟩

end rind.x86_64.mul4x

/-- info: 'rind.x86_64.mul4x.bn_mul4x_mont_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.mul4x.bn_mul4x_mont_correct
