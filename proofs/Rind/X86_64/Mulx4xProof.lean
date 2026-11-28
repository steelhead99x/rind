import Rind.X86_64.Mulx4xHead
import Rind.X86_64.Mulx4xFinal

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x

set_option linter.unusedSimpArgs false

/-!
# aws-lc's `bn_mulx4x_mont`, proven

`bn_mulx4x_mont_correct`: the routine `RindIsa/X86_64/Mulx4x.lean` gives as
`prog`, which `admin/prove lean` checks is the machine code of rind's naked
function `low::x86_64::mont::bn_mulx4x_mont` as rind's Linux release build
emits it, run in rind's extension of VG's x86_64 model
(`RindIsa/X86_64.lean`) from a state `Pre` holds of, terminates in one that
`Post` relates it to: the `k` words at `rp` become the Montgomery product of
the `k` words at `ap` and `bp` modulo those at `np`, below the modulus;
nothing changes but those words and the frame of `8k + 248` bytes below the
stack pointer; and the registers the System V ABI makes the callee save, the
stack pointer among them, and the return address are as they were, with `rax`
1. Its trace of addresses and branches is a function of the arguments and the
stack pointer alone (`ConstantTime`, with `Pub`), and some state meets `Pre`.

The proof runs each block symbolically (`Mulx4xAsm`, `Mulx4xTail`,
`Mulx4xHead`), inducts over the loops (`Mulx4xLoop`, `Mulx4xPass`,
`Mulx4xFinal`, `Mulx4xHead`), and shows each pass is a Montgomery step and the
last subtraction and selection reduce the result below the modulus
(`Mulx4xModel`, `Mul4xSub`). Every theorem rests only on Lean's three axioms.
-/

namespace rind.x86_64.mulx4x

/-- The bytes below the stack pointer the routine may use, for `k` words: its pushes and the frame's `k + 9`
words, 128-byte aligned. -/
def frameLen (k : Nat) : Nat := 8 * k + 248

/-- `len` bytes at `p`, without wrapping, apart from the frame and the return address,
`[sp0 - frameLen k, sp0 + 8)`. -/
def OffFrame (p : Addr) (len : Nat) (sp0 : Addr) (k : Nat) : Prop :=
  p.toNat + len ≤ 2 ^ 64 ∧ (p.toNat + len ≤ sp0.toNat - frameLen k ∨ sp0.toNat + 8 ≤ p.toNat)

theorem out_byte (p fp sp0 : Addr) (k L i c : Nat) (hc : c < 8) (hi : i < L) (hp : p.toNat + 8 * L ≤ 2 ^ 64)
    (hoff : p.toNat + 8 * L ≤ sp0.toNat - (8 * k + 248) ∨ sp0.toNat + 8 ≤ p.toNat)
    (h1 : fp.toNat + 8 * k + 120 ≤ sp0.toNat) (h2 : sp0.toNat ≤ fp.toNat + 8 * k + 247)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) : sp0.toNat - fp.toNat ≤ (wa p i + BitVec.ofNat 64 c - fp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, wa_toNat hp hi, BitVec.toNat_ofNat]
  rcases hoff with h | h <;> omega

theorem out_push (y fp sp0 : Addr) (h1 : fp.toNat + 120 ≤ sp0.toNat)
    (hy : sp0.toNat - fp.toNat ≤ (y - fp).toNat) : 48 ≤ (y - (sp0 - BitVec.ofNat 64 48)).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hy ⊢
  have := y.isLt
  have := sp0.isLt
  omega

theorem save_off (rp fp sp0 : Addr) (k c b : Nat) (hb : b < 8) (c1 : 8 ≤ c) (c2 : c ≤ 48)
    (h1 : fp.toNat + 8 * k + 120 ≤ sp0.toNat) (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hp : rp.toNat + 8 * k ≤ 2 ^ 64)
    (hoff : rp.toNat + 8 * k ≤ sp0.toNat - (8 * k + 248) ∨ sp0.toNat + 8 ≤ rp.toNat) :
    8 * k ≤ (sp0 - BitVec.ofNat 64 c + BitVec.ofNat 64 b - rp).toNat ∧
      8 * (k + 9) ≤ (sp0 - BitVec.ofNat 64 c + BitVec.ofNat 64 b - fp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> rcases hoff with h | h <;> omega

theorem frame_off (y fp sp0 : Addr) (k : Nat)
    (h1 : fp.toNat + 8 * k + 120 ≤ sp0.toNat) (h2 : sp0.toNat ≤ fp.toNat + 8 * k + 247)
    (hy : 8 * k + 248 ≤ (y - (sp0 - BitVec.ofNat 64 (8 * k + 248))).toNat) :
    sp0.toNat - fp.toNat ≤ (y - fp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hy ⊢
  have := y.isLt
  have := sp0.isLt
  omega

theorem ret_off (rp sp0 : Addr) (k c : Nat) (hc : c < 8) (hF : 8 * k + 248 ≤ sp0.toNat)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hp : rp.toNat + 8 * k ≤ 2 ^ 64)
    (hoff : rp.toNat + 8 * k ≤ sp0.toNat - (8 * k + 248) ∨ sp0.toNat + 8 ≤ rp.toNat) :
    8 * k ≤ (sp0 + BitVec.ofNat 64 c - rp).toNat ∧
      8 * k + 248 ≤ (sp0 + BitVec.ofNat 64 c - (sp0 - BitVec.ofNat 64 (8 * k + 248))).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> rcases hoff with h | h <;> omega

theorem quarter_sub (k : Nat) (hk : k < 2 ^ 29) (hk8 : 8 ≤ k) :
    BitVec.ofNat 64 (8 * k / 32) - 1 = BitVec.ofNat 64 (k / 4 - 1) := by
  rw [show 8 * k / 32 = k / 4 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

/-- The memory `setup` leaves. -/
abbrev setupMem (M : Mem) (k : Nat) (bp fp rp sp0 n0' : Addr) : Mem :=
  (((((M.writeW fp (BitVec.ofNat 64 (8 * k))).writeW (wa fp 2) (wa bp k)).writeW (wa fp 3) n0').writeW
    (wa fp 4) rp).writeW (wa fp 5) sp0).writeW (wa fp 6) (BitVec.ofNat 64 (8 * k / 32) - 1)

theorem setup_agree (M : Mem) (k : Nat) (bp fp rp sp0 n0' : Addr) :
    Agree M (setupMem M k bp fp rp sp0 n0') fp 7 := fun y hy => by
  unfold setupMem Mem.writeW
  repeat rw [write_other _ _ _ _ _ (by (try simp only [wa]); bv_omega)]

theorem setup_slots (M : Mem) (k : Nat) (bp fp rp sp0 n0' : Addr) (hk : k < 2 ^ 29) (hk8 : 8 ≤ k) :
    Slots (setupMem M k bp fp rp sp0 n0') k bp fp rp sp0 n0' := by
  have e6 := quarter_sub k hk hk8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold setupMem <;> (try rw [wa_zero]) <;>
    repeat (first
      | rw [readW_writeW_self]
      | rw [readW_writeW_sep _ _ _ _ (by unfold Apart; simp only [wa]; constructor <;> bv_omega)])
  exact e6

theorem epi_byte (M : Mem) (fp sp0 y : Addr) (k : Nat) (u : Nat → BitVec 64)
    (hfp : fp.toNat + 8 * (k + 9) ≤ 2 ^ 64) (h1 : fp.toNat + 8 * k + 120 ≤ sp0.toNat)
    (hy : sp0.toNat - fp.toNat ≤ (y - fp).toNat) :
    lose (M.writeW (wa fp (k + 8)) (0 : BitVec 64)) fp (sp0.toNat - fp.toNat) u y = M y := by
  rw [lose_byte _ _ _ _ _ hy]; unfold Mem.writeW
  rw [write_other _ _ _ _ _ ?_]
  rw [BitVec.toNat_sub, wa_toNat (k := k + 9) hfp (by omega)]
  rw [BitVec.toNat_sub] at hy
  have := y.isLt
  omega

/-! ## The routine -/

/-- The theorem's hypotheses, `rp = rdi`, `ap = rsi`, `bp = rdx`, `np = rcx`, `n0 = r8`, and `num = r9`: `num` a
multiple of four from eight, below `2^29` so that `8 num` fits the 32 bits the routine scales it in; the routine
may read `ap`, `bp`, and `np`'s `num` words and the word at `n0`, and write `rp`'s and the stack's below the return
address, which `lo` bounds to `frameLen num` bytes; none of the arrays overlaps that frame or the return address,
nor `rp` `np`; `n0` is `-np⁻¹ mod 2^64`; and `ap`'s value is below `np`'s. The arrays may overlap each other but
`rp` and `np`, since the routine writes `rp` only after its last read of `ap` and `bp`. -/
structure Pre (s : S) : Prop where
  k8 : 8 ≤ num s
  k4 : num s % 4 = 0
  k29 : num s < 2 ^ 29
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
  let fp := fpOf sp0 k
  (prologueATrace sp0 n0p ++ [.addr (pagesOf sp0 fp + fp)]) ++
    (walkTrace fp ((pagesOf sp0 fp).toNat / 4096) ++
    (setupTrace fp ++
    (body0Trace ap bp np fp ++
    (firstLoopTrace ap np fp k ++
    (firstTailTrace fp k ++
    (outerTrace ap bp np fp k ++
    (finalTrace fp ++
    (subLoopTrace np fp rp k ++
    (subTailTrace fp ++
    (copyLoopTrace fp rp k ++ epilogueTrace fp sp0 k))))))))))

/-- The routine's trace from `s`, a function of what is public. -/
def trace (s : S) : List Leak :=
  traceOf (s.vg.gpr .rdi) (s.vg.gpr .rsi) (s.vg.gpr .rdx) (s.vg.gpr .rcx) (s.vg.gpr .r8) (s.vg.gpr .rsp) (num s)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem correct (s : S) (h : Pre s) : ∃ s', Exec I Rind.X86_64.Mulx4x.prog s (trace s) s' ∧ Post s s' := by
  obtain ⟨k8, k4, k29, ⟨rest, hwr, hrpw⟩, rA, rB, rN, rN0, hlo, hsp, oA, oB, oN, oN0, oP, sepPN, hn0, hlt⟩ := h
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
  obtain ⟨s₁, s₂, hx1, hx2, h_sp, h_ax, h_8, h_9, h_wr, h_mem, h_g, h_oth, h_mx, h_lo⟩ :=
    head_ok s k sp0 n0p n0' rest k29 (by omega) hsp hsp0 hr9 hr8 hwr rN0 oN0.1
      (by rcases oN0.2 with h | h <;> omega) hn0'.symm
  have hfp := fpOf_toNat sp0 k k29 (by omega)
  simp only [traceOf]
  generalize fpOf sp0 k = fp at *
  have t1 := Nat.div_add_mod (sp0.toNat - 8 * k - 120) 128
  have t2 := Nat.mod_lt (sp0.toNat - 8 * k - 120) (show 128 > 0 by norm_num)
  have T : fp.toNat + 8 * k + 120 ≤ sp0.toNat ∧ sp0.toNat ≤ fp.toNat + 8 * k + 247 ∧ fp.toNat % 16 = 0 := by
    rw [hfp]; omega
  clear t1 t2
  obtain ⟨T1, T2, al⟩ := T
  have hmem2 : s₂.vg.mem = pushes s.vg.mem sp0 s.vg.gpr := h_mem
  have hsp48 : 48 ≤ sp0.toNat := by omega
  have rd2 : s₂.vg.rd = s.vg.rd := others_rd h_oth
  have g2 : ∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → s₂.vg.gpr r = s.vg.gpr r := h_g
  have sepX : ∀ (p : Addr) (L : Nat), (p.toNat + L ≤ sp0.toNat - (8 * k + 248) ∨ sp0.toNat + 8 ≤ p.toNat) →
      p.toNat + L ≤ fp.toNat ∨ fp.toNat + 8 * (k + 9) ≤ p.toNat := fun p L h => by omega
  have ar2 : Arr s₂ k ap bp np fp :=
    ⟨k29, oA.1, oB.1, oN.1, by omega, sepX _ _ oA.2, sepX _ _ oB.2, sepX _ _ oN.2,
      by rw [rd2]; exact List.mem_append_left _ rA, by rw [rd2]; exact List.mem_append_left _ rB,
      by rw [rd2]; exact List.mem_append_left _ rN,
      ⟨sp0.toNat + 8 - fp.toNat, by omega, by rw [h_wr]; exact List.mem_cons_self⟩⟩
  -- The frame's slots.
  obtain ⟨s₃, hx3, hmem3, hF3⟩ := setup_ok s₂ k ap bp np fp rp sp0 n0' k8 ar2 h_sp
    ((g2 .rdx (by decide)).trans hrdx) h_9 h_8 ((g2 .rdi (by decide)).trans hrdi) h_ax
  have ar3 := ar2.frame hF3
  have out3 : OutX s₃ k np fp rp :=
    ⟨oP.1, sepX _ _ oP.2, sepPN, by rw [hF3.wr, h_wr]; exact List.mem_cons_of_mem _ hrpw⟩
  have agree3 : Agree s₂.vg.mem s₃.vg.mem fp 7 := by rw [hmem3]; exact setup_agree _ k bp fp rp sp0 n0'
  have sl3 : Slots s₃.vg.mem k bp fp rp sp0 n0' := by rw [hmem3]; exact setup_slots _ k bp fp rp sp0 n0' k29 k8
  -- Bytes apart from `[fp, sp0)` read as they did.
  have keepOut : ∀ y, sp0.toNat - fp.toNat ≤ (y - fp).toNat → s₃.vg.mem y = s.vg.mem y := fun y hy => by
    rw [agree3 y (by omega), hmem2, pushes_byte _ _ _ _ hsp48 (out_push y fp sp0 (by omega) hy)]
  have off3 : ∀ (p : Addr) (L i : Nat), p.toNat + 8 * L ≤ 2 ^ 64 →
      (p.toNat + 8 * L ≤ sp0.toNat - (8 * k + 248) ∨ sp0.toNat + 8 ≤ p.toNat) → i < L →
      s₃.vg.mem.readW (wa p i) 64 = s.vg.mem.readW (wa p i) 64 := by
    intro p L i hp hoff hi
    simp only [Mem.readW]; congr 1; apply read_congr; intro c hc
    exact keepOut _ (out_byte p fp sp0 k L i c (by omega) hi hp hoff T1 T2 hsp)
  have hA3 : ∀ i < k, s₃.vg.mem.readW (wa ap i) 64 = a i := fun i hi => off3 ap k i oA.1 oA.2 hi
  have hB3 : ∀ i < k, s₃.vg.mem.readW (wa bp i) 64 = bw i := fun i hi => off3 bp k i oB.1 oB.2 hi
  have hN3 : ∀ i < k, s₃.vg.mem.readW (wa np i) 64 = n i := fun i hi => off3 np k i oN.1 oN.2 hi
  have hn0w : ((n 0).toNat * n0'.toNat + 1) % 2 ^ 64 = 0 := hn0
  have g3 : ∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → r ∉ [Reg.r9, .r10] →
      s₃.vg.gpr r = s.vg.gpr r := fun r hr hr' => (hF3.gpr r hr').trans (g2 r hr)
  have hrsp3 : s₃.vg.gpr .rsp = fp := (hF3.gpr .rsp (by decide)).trans h_sp
  -- The passes.
  obtain ⟨s₄, s₅, s₆, hx4, hx5, hx6, hI6⟩ :=
    pass0_ok s₃ k ap bp np fp rp sp0 n0' a bw n k8 k4 ar3 sl3 ((g3 .rsi (by decide) (by decide)).trans hrsi)
      ((g3 .rdx (by decide) (by decide)).trans hrdx) ((g3 .rcx (by decide) (by decide)).trans hrcx) hrsp3 hA3 hN3 hB3 hn0w (by omega)
  obtain ⟨s₇, hx7, hI7⟩ := outer_ok s₃ k ap bp np fp rp sp0 n0' a bw n k8 k4 ar3 sl3 hrsp3 hA3 hN3 hB3 hn0w s₆ hI6
  -- The subtraction and selection.
  obtain ⟨s₈, s₉, s₁₀, s₁₁, hx8, hx9, hx10, hx11, f_bx, f_dx, f_si, fF, fmem, flt, fmod⟩ :=
    finalPhase_ok s₃ s₇ k ap bp np fp rp sp0 n0' a bw n k8 k4 ar3 out3 sl3 al hrsp3 hN3 hlt hI7
  -- The callee-saved registers the prologue pushed.
  have hsave : ∀ c, 8 ≤ c → c ≤ 48 →
      s₁₁.vg.mem.readW (sp0 - BitVec.ofNat 64 c) 64 = s₂.vg.mem.readW (sp0 - BitVec.ofNat 64 c) 64 := by
    intro c c1 c2
    simp only [Mem.readW]; congr 1; apply read_congr; intro b hb
    obtain ⟨o1, o2⟩ := save_off rp fp sp0 k c b (by omega) c1 c2 T1 hsp oP.1 oP.2
    rw [fmem _ o1 o2]
    exact agree3 _ (by omega)
  obtain ⟨v15, v14, v13, v12, vbp, vbx⟩ := pushes_saved s.vg.mem sp0 s.vg.gpr hsp48
  rw [← hmem2] at v15 v14 v13 v12 vbp vbx
  have hwr11 : s₁₁.vg.wr = ⟨fp, sp0.toNat + 8 - fp.toNat⟩ :: rest := by rw [fF.wr, hF3.wr, h_wr]
  -- The epilogue.
  obtain ⟨s₁₂, hx12, e_sp, e_ax, e15, e14, e13, e12, ebp, ebx, ewr, erd, emx, elo, emem⟩ :=
    epilogue_ok s₁₁ k (sp0.toNat + 8 - fp.toNat) fp sp0 _ _ _ _ _ _ rest (by omega) hsp
      ((fF.gpr .rsp (by decide)).trans hrsp3) f_bx f_dx f_si hwr11 rfl
      ((hsave 48 (by omega) le_rfl).trans v15) ((hsave 40 (by omega) (by omega)).trans v14)
      ((hsave 32 (by omega) (by omega)).trans v13) ((hsave 24 (by omega) (by omega)).trans v12)
      ((hsave 16 (by omega) (by omega)).trans vbp) ((hsave 8 le_rfl (by omega)).trans vbx)
  have epi : ∀ y, sp0.toNat - fp.toNat ≤ (y - fp).toNat → s₁₂.vg.mem y = s₁₁.vg.mem y := fun y hy => by
    rw [emem]; exact epi_byte _ fp sp0 y k _ (by omega) T1 hy
  -- The result.
  have hRv : val (words s₁₂.vg.mem rp) k = val (fun i => s₁₁.vg.mem.readW (wa rp i) 64) k :=
    val_congr fun i hi => by
      unfold words
      simp only [Mem.readW]; congr 1; apply read_congr; intro c hc
      exact epi _ (out_byte rp fp sp0 k k i c (by omega) hi oP.1 oP.2 T1 T2 hsp)
  have hmemP : ∀ y, 8 * k ≤ (y - rp).toNat → 8 * k + 248 ≤ (y - (sp0 - BitVec.ofNat 64 (8 * k + 248))).toNat →
      s₁₂.vg.mem y = s.vg.mem y := by
    intro y h1 h2
    have f1 := frame_off y fp sp0 k T1 T2 h2
    rw [epi y f1, fmem y h1 (by omega), keepOut y f1]
  refine ⟨s₁₂, Exec.seq hx1 (Exec.seq hx2 (Exec.seq (Exec.block hx3) (Exec.seq hx4 (Exec.seq hx5 (Exec.seq hx6
    (Exec.seq hx7 (Exec.seq hx8 (Exec.seq hx9 (Exec.seq hx10 (Exec.seq hx11 (Exec.block hx12))))))))))), ?_⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, e_ax, by rw [ewr, hwr], ?_⟩
  · rw [hrdi, hrcx, hk, hRv]; exact flt
  · rw [hrdi, hrcx, hrsi, hrdx, hk, hRv]; exact fmod
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
  · rw [emx, others_mxcsr fF.others, others_mxcsr hF3.others, h_mx]
  · rw [erd, fF.rd, hF3.rd, rd2]

theorem constant_time : ConstantTime I Pre Pub Rind.X86_64.Mulx4x.prog := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨e0, e1, e2, e3, e4, e5, e6⟩ x₁ x₂
  obtain ⟨_, y₁, -⟩ := correct s₁ h₁
  obtain ⟨_, y₂, -⟩ := correct s₂ h₂
  rw [(exec_det x₁ y₁).1, (exec_det x₂ y₂).1]
  simp only [trace, num, e0, e1, e2, e3, e4, e5, e6]

/-! ## The precondition holds of some state -/

set_option exponentiation.threshold 512 in
set_option maxRecDepth 8192 in
theorem pre_witness : Pre witness := by
  have hk : num witness = 8 := by decide
  refine ⟨?_, ?_, ?_, ⟨[⟨0x200000#64, 64⟩], rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [hk, OffFrame, frameLen]) <;> decide

/-- The routine computes the Montgomery product of its arguments, keeping what the System V ABI and its contract
require; its trace depends only on its arguments and the stack pointer; and some state meets its precondition. -/
theorem bn_mulx4x_mont_correct :
    (∀ s, Pre s → ∃ t s', Exec I Rind.X86_64.Mulx4x.prog s t s' ∧ Post s s') ∧
      ConstantTime I Pre Pub Rind.X86_64.Mulx4x.prog ∧ ∃ s, Pre s :=
  ⟨fun s h => let ⟨s', e, p⟩ := correct s h; ⟨_, s', e, p⟩, constant_time, _, pre_witness⟩

end rind.x86_64.mulx4x

/-- info: 'rind.x86_64.mulx4x.bn_mulx4x_mont_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.mulx4x.bn_mulx4x_mont_correct
