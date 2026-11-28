import Rind.X86_64.Sqrx8xMontFinal

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

/-!
# aws-lc's `bn_sqrx8x_mont`, proven given `bn_sqrx8x_internal`

`bn_sqrx8x_mont_correct_of`: the routine `RindIsa/X86_64/Sqrx8xMont.lean` gives
as `prog`, which `admin/prove lean` checks is the machine code of rind's naked
function `low::x86_64::mont::bn_sqrx8x_mont` as rind's Linux release build
emits it, run in rind's extension of VG's x86_64 model
(`RindIsa/X86_64.lean`) from a state `Pre` holds of, terminates in one that
`Post` relates it to: the `k` words at `rp` become the Montgomery square of
the `k` words at `ap` modulo those at `np`, below the modulus; nothing changes
but those words and the frame of `48k + 184` bytes below the stack pointer;
and the registers the System V ABI makes the callee save, the stack pointer
among them, and the return address are as they were, with `rax` 1. Its trace
of addresses and branches is a function of the arguments and the stack
pointer alone (`ConstantTime`, with `Pub`), and some state meets `Pre`.

All of it takes the routine it calls, `bn_sqrx8x_internal`, to meet its
contract (`Internal`): from a state `InPre` holds of, it terminates in one
`InPost` relates it to, with a trace `inT` of its arguments and frame alone.

The proof runs each block around the call symbolically (`Sqrx8xMontHead`,
`Sqrx8xMontTail`), inducts over the loops (`Sqrx8xMontFinal`), and shows the
last subtraction and selection reduce the internal routine's result below the
modulus (`Mul4xSub`). Every theorem rests only on Lean's three axioms.
-/

namespace rind.x86_64.sqrx8xmont

/-- The bytes below the stack pointer the routine may use, for `k` words: its pushes, the call's return address,
and the internal routine's frame of `2k + 9` words, which the routine places up to `32k + 63` bytes lower, 64-byte
aligned, so that it does not share `ap`'s offset in a page. -/
def frameLen (k : Nat) : Nat := 48 * k + 184

/-- `len` bytes at `p`, without wrapping, apart from the frame and the return address,
`[sp0 - frameLen k, sp0 + 8)`. -/
def OffFrame (p : Addr) (len : Nat) (sp0 : Addr) (k : Nat) : Prop :=
  p.toNat + len ≤ 2 ^ 64 ∧ (p.toNat + len ≤ sp0.toNat - frameLen k ∨ sp0.toNat + 8 ≤ p.toNat)

theorem OffFrame.bound {p : Addr} {len : Nat} {sp0 : Addr} {k : Nat} (h : OffFrame p len sp0 k) :
    p.toNat + len ≤ 2 ^ 64 := h.1

theorem OffFrame.apart {p : Addr} {len : Nat} {sp0 : Addr} {k : Nat} (h : OffFrame p len sp0 k) :
    p.toNat + len ≤ sp0.toNat - (48 * k + 184) ∨ sp0.toNat + 8 ≤ p.toNat := h.2

/-- `bn_sqrx8x_internal`'s contract, for a trace `inT` of its width, arguments, and frame. -/
def Internal (inT : Nat → Addr → Addr → Addr → List Leak) : Prop :=
  ∀ s k ap np fp a n n0, sqrx8x.InPre s k ap np fp a n n0 →
    ∃ s', Exec I Rind.X86_64.Sqrx8x.prog s (inT k ap np fp) s' ∧ sqrx8x.InPost s s' k np fp a n

theorem out_byte (p fp sp0 : Addr) (k L i c : Nat) (hc : c < 8) (hi : i < L) (hp : p.toNat + 8 * L ≤ 2 ^ 64)
    (hoff : p.toNat + 8 * L ≤ sp0.toNat - (48 * k + 184) ∨ sp0.toNat + 8 ≤ p.toNat)
    (h2 : sp0.toNat ≤ fp.toNat + 48 * k + 183)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) : sp0.toNat - fp.toNat ≤ (wa p i + BitVec.ofNat 64 c - fp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, wa_toNat hp hi, BitVec.toNat_ofNat]
  rcases hoff with h | h <;> omega

theorem out_push (y fp sp0 : Addr) (h1 : fp.toNat + 120 ≤ sp0.toNat)
    (hy : sp0.toNat - fp.toNat ≤ (y - fp).toNat) : 48 ≤ (y - (sp0 - BitVec.ofNat 64 48)).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hy ⊢
  have := y.isLt
  have := sp0.isLt
  omega

theorem frame_byte (y fp sp0 : Addr) (k : Nat)
    (h2 : sp0.toNat ≤ fp.toNat + 48 * k + 183)
    (hy : 48 * k + 184 ≤ (y - (sp0 - BitVec.ofNat 64 (48 * k + 184))).toNat) :
    sp0.toNat - fp.toNat ≤ (y - fp).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at hy ⊢
  have := y.isLt
  have := sp0.isLt
  omega

theorem ret_byte (rp sp0 : Addr) (k c : Nat) (hc : c < 8) (hF : 48 * k + 184 ≤ sp0.toNat)
    (hsp : sp0.toNat + 8 ≤ 2 ^ 64) (hp : rp.toNat + 8 * k ≤ 2 ^ 64)
    (hoff : rp.toNat + 8 * k ≤ sp0.toNat - (48 * k + 184) ∨ sp0.toNat + 8 ≤ rp.toNat) :
    8 * k ≤ (sp0 + BitVec.ofNat 64 c - rp).toNat ∧
      48 * k + 184 ≤ (sp0 + BitVec.ofNat 64 c - (sp0 - BitVec.ofNat 64 (48 * k + 184))).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> rcases hoff with h | h <;> omega

/-- Two memories read the same word where its eight bytes agree. -/
theorem readW_bytes {M M' : Mem} {x : Addr} (h : ∀ b < 8, M' (x + BitVec.ofNat 64 b) = M (x + BitVec.ofNat 64 b)) :
    M'.readW x 64 = M.readW x 64 := by
  simp only [Mem.readW]; congr 1; exact read_congr _ _ _ _ h

theorem wa_pred (w : Addr) (i : Nat) : wa (w - 8) (i + 1) = wa w i := by
  simp only [wa]; bv_omega

theorem neg8k (k : Nat) (hk : k < 2 ^ 29) :
    0 - BitVec.ofNat 64 (8 * k) = BitVec.ofNat 64 (2 ^ 64 - 8 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
  omega

/-! ## The routine -/

/-- The theorem's hypotheses, `rp = rdi`, `ap = rsi`, `np = rcx`, `n0 = r8`, and `num = r9`; `rdx` is unused:
`num` a multiple of eight from eight, below `2^29` so that `8 num` fits the 32 bits the routine scales it in; the
routine may read `ap` and `np`'s `num` words and the word at `n0`, and write `rp`'s and the stack's below the
return address, which `lo` bounds to `frameLen num` bytes; the stack pointer is below `2^63`, as every user-space
stack is, since the internal routine's carry chain needs its frame not to straddle `2^63`; none of the arrays
overlaps that frame or the return address, nor `rp` `np`; `n0` is `-np⁻¹ mod 2^64`; and `ap`'s value is below
`np`'s. `rp` may overlap `ap`, since the routine writes `rp` only after its last read of `ap`. -/
structure Pre (s : S) : Prop where
  k8 : 8 ≤ num s
  k0 : num s % 8 = 0
  k29 : num s < 2 ^ 29
  wr : ∃ rest, s.vg.wr = ⟨s.vg.gpr .rsp, 8⟩ :: rest ∧ ⟨s.vg.gpr .rdi, 8 * num s⟩ ∈ rest
  rA : ⟨s.vg.gpr .rsi, 8 * num s⟩ ∈ s.vg.rd
  rN : ⟨s.vg.gpr .rcx, 8 * num s⟩ ∈ s.vg.rd
  rN0 : ⟨s.vg.gpr .r8, 8⟩ ∈ s.vg.rd
  lo : s.lo.toNat + frameLen (num s) ≤ (s.vg.gpr .rsp).toNat
  sp : (s.vg.gpr .rsp).toNat + 8 ≤ 2 ^ 63
  oA : OffFrame (s.vg.gpr .rsi) (8 * num s) (s.vg.gpr .rsp) (num s)
  oN : OffFrame (s.vg.gpr .rcx) (8 * num s) (s.vg.gpr .rsp) (num s)
  oN0 : OffFrame (s.vg.gpr .r8) 8 (s.vg.gpr .rsp) (num s)
  oP : OffFrame (s.vg.gpr .rdi) (8 * num s) (s.vg.gpr .rsp) (num s)
  sepPN : (s.vg.gpr .rdi).toNat + 8 * num s ≤ (s.vg.gpr .rcx).toNat ∨
    (s.vg.gpr .rcx).toNat + 8 * num s ≤ (s.vg.gpr .rdi).toNat
  n0 : ((words s.vg.mem (s.vg.gpr .rcx) 0).toNat * (s.vg.mem.readW (s.vg.gpr .r8) 64).toNat + 1) % 2 ^ 64 = 0
  lt : val (words s.vg.mem (s.vg.gpr .rsi)) (num s) < val (words s.vg.mem (s.vg.gpr .rcx)) (num s)

/-- What the routine ensures: `rp`'s words are below `np`'s and, times `2^(64 num)`, are `ap`'s squared modulo
`np`'s; memory but `rp` and the frame is unchanged; the registers the System V ABI makes the callee save, the stack
pointer among them, and the return address are as they were; it returns 1; and its regions are as they were. -/
structure Post (s s' : S) : Prop where
  lt : val (words s'.vg.mem (s.vg.gpr .rdi)) (num s) < val (words s.vg.mem (s.vg.gpr .rcx)) (num s)
  mont : val (words s'.vg.mem (s.vg.gpr .rdi)) (num s) * 2 ^ (64 * num s) % val (words s.vg.mem (s.vg.gpr .rcx)) (num s) =
    val (words s.vg.mem (s.vg.gpr .rsi)) (num s) * val (words s.vg.mem (s.vg.gpr .rsi)) (num s) %
      val (words s.vg.mem (s.vg.gpr .rcx)) (num s)
  mem : ∀ y, 8 * num s ≤ (y - s.vg.gpr .rdi).toNat →
    frameLen (num s) ≤ (y - (s.vg.gpr .rsp - BitVec.ofNat 64 (frameLen (num s)))).toNat → s'.vg.mem y = s.vg.mem y
  abi : abiPreserved s.vg s'.vg
  rax : s'.vg.gpr .rax = 1
  wr : s'.vg.wr = s.vg.wr
  rd : s'.vg.rd = s.vg.rd

/-- What is public: the arguments and the stack pointer. The arrays' and `n0`'s values are not. -/
def Pub (s₁ s₂ : S) : Prop :=
  s₁.vg.gpr .rdi = s₂.vg.gpr .rdi ∧ s₁.vg.gpr .rsi = s₂.vg.gpr .rsi ∧ s₁.vg.gpr .rcx = s₂.vg.gpr .rcx ∧
    s₁.vg.gpr .r8 = s₂.vg.gpr .r8 ∧ s₁.vg.gpr .r9 = s₂.vg.gpr .r9 ∧ s₁.vg.gpr .rsp = s₂.vg.gpr .rsp

/-- The routine's trace, of the internal routine's, the arguments, the width, and the stack pointer. -/
def traceOf (inT : Nat → Addr → Addr → Addr → List Leak) (rp ap np n0p sp0 : Addr) (k : Nat) : List Leak :=
  let wsp := fpOf sp0 ap k
  mulx4x.prologueATrace sp0 n0p ++
    ([.branch (decide (32 * k < (offOf sp0 ap k).toNat))] ++
    ([.addr (pagesOf sp0 wsp + wsp)] ++
    (mulx4x.walkTrace wsp ((pagesOf sp0 wsp).toNat / 4096) ++
    (setupTrace wsp k ++
    (([.addr (wsp - 8)] ++ inT k ap np (wsp - 8) ++ [.addr (wsp - 8)]) ++
    (subLoopTrace np rp wsp k ++
    (subTailTrace wsp ++
    (copyLoopTrace rp wsp k ++ epilogueTrace sp0))))))))

/-- The routine's trace from `s`, a function of what is public. -/
def trace (inT : Nat → Addr → Addr → Addr → List Leak) (s : S) : List Leak :=
  traceOf inT (s.vg.gpr .rdi) (s.vg.gpr .rsi) (s.vg.gpr .rcx) (s.vg.gpr .r8) (s.vg.gpr .rsp) (num s)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem correct (inT : Nat → Addr → Addr → Addr → List Leak) (hin : Internal inT) (s : S) (h : Pre s) :
    ∃ s', Exec I Rind.X86_64.Sqrx8xMont.prog s (trace inT s) s' ∧ Post s s' := by
  obtain ⟨k8, k0, k29, ⟨rest, hwr, hrpw⟩, rA, rN, rN0, hlo, hsp, oA, oN, oN0, oP, -, hn0, hlt⟩ := id h
  have hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (num s) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; unfold num; omega
  unfold trace
  generalize hk : num s = k at *
  unfold frameLen at hlo
  generalize hsp0 : s.vg.gpr .rsp = sp0 at *
  generalize hrdi : s.vg.gpr .rdi = rp at *
  generalize hrsi : s.vg.gpr .rsi = ap at *
  generalize hrcx : s.vg.gpr .rcx = np at *
  generalize hr8 : s.vg.gpr .r8 = n0p at *
  set a := words s.vg.mem ap with ha
  set n := words s.vg.mem np with hn
  set n0' := s.vg.mem.readW n0p 64 with hn0'
  have sp0L := sp0.isLt
  -- The prologue and the walk.
  obtain ⟨s₁, s₂, s₃, s₄, hx1, hx2, hx3, hx4, h_sp, h_ax, h_8, h_9, h_wr, h_mem, h_g, h_oth, h_mx, h_xmm, h_lo⟩ :=
    head_ok s k sp0 ap n0p n0' rest k8 k29 (by omega) (by omega) hsp0 hr9 hr8 hrsi hwr rN0 oN0.bound
      (by rcases oN0.apart with h | h <;> omega) hn0'.symm
  obtain ⟨W1, W2, W3⟩ := fpOf_toNat sp0 ap k k8 k29 (by omega)
  simp only [traceOf]
  generalize fpOf sp0 ap k = wsp at *
  have hrd4 : s₄.vg.rd = s.vg.rd := others_rd h_oth
  have g4 : ∀ r, r ∉ [Reg.rsp, .rax, .rbp, .r8, .r9, .r10, .r11] → s₄.vg.gpr r = s.vg.gpr r := h_g
  have hwL : wsp.toNat + 8 * (2 * k + 8) ≤ 2 ^ 64 := by omega
  -- The frame's slots.
  obtain ⟨s₅, hx5, m5, r9_5, r10_5, x0_5, x1_5, x2_5, x3_5, wr5, lo5, oth5, g5⟩ :=
    setup_ok s₄ k wsp np rp sp0 n0' (sp0.toNat + 8 - wsp.toNat) rest k29 (by omega) h_wr h_sp h_9 h_8 h_ax
      ((g4 .rcx (by decide)).trans hrcx) ((g4 .rdi (by decide)).trans hrdi)
  have hrsp5 : s₅.vg.gpr .rsp = wsp := (g5 .rsp (by decide)).trans h_sp
  have hlo5 : s₅.lo.toNat + 8 ≤ wsp.toNat := by rw [lo5, h_lo]; omega
  -- The call.
  obtain ⟨c₁, hc1, c_sp, c_wr, c_mem, c_g, c_xmm, c_rd, c_mx, c_lo⟩ :=
    call_ok s₅ wsp _ rest hrsp5 (by rw [wr5, h_wr]) hlo5
  obtain ⟨fp, hfp⟩ : ∃ fp, wsp - 8 = fp := ⟨_, rfl⟩
  rw [hfp] at c_sp c_wr c_mem
  rw [hfp]
  have F1 : fp.toNat + 8 = wsp.toNat := by
    rw [← hfp, BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]; omega
  have fp8 : fp + 8 = wsp := by rw [← hfp]; exact BitVec.sub_add_cancel _ _
  have waP : ∀ i, wa fp (i + 1) = wa wsp i := fun i => by rw [← hfp]; exact wa_pred wsp i
  have hfpL : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 64 := by omega
  have T1 : fp.toNat + 16 * k + 120 ≤ sp0.toNat := by omega
  have T2 : sp0.toNat ≤ fp.toNat + 48 * k + 183 := by omega
  have fpL := fp.isLt
  have A4 : (wa wsp 4).toNat = wsp.toNat + 32 := wa_toNat hwL (by omega)
  have A5 : (wa wsp 5).toNat = wsp.toNat + 40 := wa_toNat hwL (by omega)
  have A2k : (wa wsp (2 * k + 6)).toNat = wsp.toNat + 8 * (2 * k + 6) := wa_toNat hwL (by omega)
  have Wf1 : (wa fp 1).toNat = fp.toNat + 8 := wa_toNat hfpL (by omega)
  have Wf7 : (wa fp 7).toNat = fp.toNat + 56 := wa_toNat hfpL (by omega)
  -- Bytes above `t`'s end read as the pushes left them, and bytes apart from `[fp, sp0)` as they were.
  have m1 : ∀ y, 16 * k + 72 ≤ (y - fp).toNat → c₁.vg.mem y = pushes s.vg.mem sp0 s.vg.gpr y := by
    intro y hy
    have := y.isLt
    rw [dist] at hy
    rw [c_mem, m5, ← h_mem]
    simp only [Mem.writeW]
    rw [write_other _ _ _ _ _ (by rw [dist]; omega), write_other _ _ _ _ _ (by rw [dist, A2k]; omega),
      write_other _ _ _ _ _ (by rw [dist, A5]; omega), write_other _ _ _ _ _ (by rw [dist, A4]; omega)]
  have keepOut : ∀ y, sp0.toNat - fp.toNat ≤ (y - fp).toNat → c₁.vg.mem y = s.vg.mem y := fun y hy => by
    rw [m1 y (by omega), pushes_byte _ _ _ _ (by omega) (out_push y fp sp0 (by omega) hy)]
  have off1 : ∀ (p : Addr) (L i : Nat), p.toNat + 8 * L ≤ 2 ^ 64 →
      (p.toNat + 8 * L ≤ sp0.toNat - (48 * k + 184) ∨ sp0.toNat + 8 ≤ p.toNat) → i < L →
      c₁.vg.mem.readW (wa p i) 64 = s.vg.mem.readW (wa p i) 64 := by
    intro p L i hp hoff hi
    refine readW_bytes fun c hc => ?_
    exact keepOut _ (out_byte p fp sp0 k L i c (by omega) hi hp hoff T2 (by omega))
  -- The slots the wrapper writes.
  have rdCall : ∀ x : Addr, 8 ≤ (x - fp).toNat → 8 ≤ (fp - x).toNat →
      c₁.vg.mem.readW x 64 = s₅.vg.mem.readW x 64 := fun x h1 h2 => by
    rw [c_mem]; exact readW_writeW_sep _ _ _ _ ⟨h1, h2⟩
  have e5 : wa fp 5 = wa wsp 4 := waP 4
  have e6 : wa fp 6 = wa wsp 5 := waP 5
  have s5 : c₁.vg.mem.readW (wa fp 5) 64 = n0' := by
    rw [rdCall _ (by rw [dist, e5, A4]; omega) (by rw [dist, e5, A4]; omega), e5, m5,
      readW_writeW_disj _ _ _ _ _ (disj_wa hwL hwL (by omega) (by omega) (by omega)),
      readW_wa_ne _ hwL (by omega) (by omega) (by omega), readW_writeW_self]
  have s6 : c₁.vg.mem.readW (wa fp 6) 64 = sp0 := by
    rw [rdCall _ (by rw [dist, e6, A5]; omega) (by rw [dist, e6, A5]; omega), e6, m5,
      readW_writeW_disj _ _ _ _ _ (disj_wa hwL hwL (by omega) (by omega) (by omega)), readW_writeW_self]
  have e2k : wa fp (2 * k + 7) = wa wsp (2 * k + 6) := waP (2 * k + 6)
  have e2k1 : wa fp (2 * k + 8) = wa wsp (2 * k + 6) + 8#64 := by
    rw [show 2 * k + 8 = (2 * k + 7) + 1 from rfl, waP, wa_succ]
  have t2k : sqrx8x.tw c₁.vg.mem fp (2 * k) = 0 := by
    show c₁.vg.mem.readW (wa fp (2 * k + 7)) 64 = 0
    rw [rdCall _ (by rw [dist, e2k, A2k]; omega) (by rw [dist, e2k, A2k]; omega), e2k, m5, readW_writeW128_lo]
    rfl
  have t2k1 : sqrx8x.tw c₁.vg.mem fp (2 * k + 1) = 0 := by
    show c₁.vg.mem.readW (wa fp (2 * k + 1 + 7)) 64 = 0
    have e : (wa fp (2 * k + 1 + 7)).toNat = wsp.toNat + 8 * (2 * k + 7) := by
      rw [show 2 * k + 1 + 7 = (2 * k + 7) + 1 by omega, waP]; exact wa_toNat hwL (by omega)
    rw [rdCall _ (by rw [dist, e]; omega) (by rw [dist, e]; omega), show 2 * k + 1 + 7 = 2 * k + 8 by omega, e2k1, m5,
      readW_writeW128_hi]
    rfl
  -- The internal routine's precondition.
  have rd1 : c₁.vg.rd = s.vg.rd := by rw [c_rd, others_rd oth5, hrd4]
  have pre : sqrx8x.InPre c₁ k ap np fp a n n0' := by
    refine ⟨⟨k8, by omega, ⟨k29, oA.bound, oN.bound, hfpL, by rcases oA.apart with h | h <;> omega,
      by rcases oN.apart with h | h <;> omega, by rw [rd1]; exact List.mem_append_left _ rA,
      by rw [rd1]; exact List.mem_append_left _ rN, ⟨sp0.toNat + 8 - wsp.toNat + 8, by omega, by rw [c_wr]; exact List.mem_cons_self⟩⟩,
      by omega, fun i hi => off1 ap k i oA.bound oA.apart hi, fun i hi => off1 np k i oN.bound oN.apart hi, s5, hn0,
      by show (c₁.vg.xmm .xmm2).setWidth 64 = np; rw [c_xmm]; exact x2_5,
      by show (c₁.vg.xmm .xmm3).setWidth 64 = _; rw [c_xmm]; exact x3_5.trans (neg8k k k29)⟩,
      k29, c_sp, ?_, (c_g .r9 (by decide)).trans r9_5, by rw [c_xmm]; exact x0_5, t2k, t2k1, by omega⟩
    rw [c_g .rsi (by decide), g5 .rsi (by decide), g4 .rsi (by decide), hrsi]
  -- The internal routine, and its return.
  obtain ⟨c₂, hxin, post⟩ := hin c₁ k ap np fp a n n0' pre
  have hF2 := post.frame
  have c2_sp : c₂.vg.gpr .rsp = fp := (hF2.gpr .rsp (by decide)).trans c_sp
  have hm2 : c₂.vg.mem.readW fp 64 = c₁.vg.mem.readW fp 64 := by
    refine readW_bytes fun b hb => ?_
    exact post.keeps _ (by simp only [dist, Wf1, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [dist, Wf7, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  obtain ⟨c₃, hret, r_sp, r_wr, r_mem, r_g, r_xmm, r_rd, r_mx, r_lo⟩ :=
    ret_ok c₁ c₂ fp _ rest c_sp c2_sp hm2 (by rw [hF2.wr, c_wr]) (by omega) (by omega)
  have hxc : Exec I (.call Rind.X86_64.Sqrx8xMont.internal Rind.X86_64.Sqrx8x.prog) s₅
      ([.addr fp] ++ inT k ap np fp ++ [.addr fp]) c₃ := by
    have e := Exec.call (M := I) (name := Rind.X86_64.Sqrx8xMont.internal) hc1 hxin hret
    have h1 : (I.callAddrs s₅).map Leak.addr = [.addr fp] := by
      show [Leak.addr (s₅.vg.gpr .rsp - 8)] = _; rw [hrsp5, hfp]
    have h2 : (I.retAddrs c₂).map Leak.addr = [.addr fp] := by
      show [Leak.addr (c₂.vg.gpr .rsp)] = _; rw [c2_sp]
    rwa [h1, h2] at e
  have c3_sp : c₃.vg.gpr .rsp = wsp := by rw [r_sp, fp8]
  have c3_wr : c₃.vg.wr = ⟨wsp, sp0.toNat + 8 - wsp.toNat⟩ :: rest := by rw [r_wr, fp8, Nat.add_sub_cancel]
  have rd3 : c₃.vg.rd = s.vg.rd := by rw [r_rd, others_rd hF2.others, rd1]
  -- Bytes above `t`'s end read after the return as before the call.
  have m3 : ∀ y, 16 * k + 72 ≤ (y - fp).toNat → c₃.vg.mem y = c₁.vg.mem y := by
    intro y hy
    rw [r_mem, lose_byte _ _ _ _ _ (by omega)]
    have := y.isLt
    rw [dist] at hy
    exact post.keeps y (by rw [dist, Wf1]; omega) (by rw [dist, Wf7]; omega)
  have keep3 : ∀ y, sp0.toNat - fp.toNat ≤ (y - fp).toNat → c₃.vg.mem y = s.vg.mem y := fun y hy => by
    rw [m3 y (by omega), keepOut y hy]
  have hN3 : ∀ i < k, c₃.vg.mem.readW (wa np i) 64 = n i := fun i hi => by
    show _ = s.vg.mem.readW (wa np i) 64
    refine readW_bytes fun c hc => ?_
    exact keep3 _ (out_byte np fp sp0 k k i c (by omega) hi oN.bound oN.apart T2 (by omega))
  have h53 : c₃.vg.mem.readW (wa wsp 5) 64 = sp0 := by
    rw [← s6, e6]
    refine readW_bytes fun b hb => ?_
    rw [r_mem, lose_byte _ _ _ _ _ (by simp only [dist, A5, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
    exact post.keeps _ (by simp only [dist, A5, Wf1, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      (by simp only [dist, A5, Wf7, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  -- The internal routine's result, `t`'s upper half and top bit.
  obtain ⟨Q, hQ, hmont⟩ := post.mont
  have hrax3 : c₃.vg.gpr .rax = c₂.vg.gpr .rax := r_g .rax (by decide)
  have hV : val (ut c₃.vg.mem wsp k (decide ((c₃.vg.gpr .rax).toNat = 1))) (k + 1) * 2 ^ (64 * k) =
      val a k * val a k + Q * val n k := by
    rw [val_ut, hrax3, bit_toNat _ post.rax, ← hmont]
    have ev1 : ∀ i < k, c₃.vg.mem.readW (wa wsp (k + 6 + i)) 64 = c₂.vg.mem.readW (wa fp (k + i + 7)) 64 := by
      intro i hi
      have e : wa fp (k + i + 7) = wa wsp (k + 6 + i) := by rw [show k + i + 7 = k + 6 + i + 1 by omega, waP]
      have ea : (wa wsp (k + 6 + i)).toNat = wsp.toNat + 8 * (k + 6 + i) := wa_toNat hwL (by omega)
      rw [e]
      refine readW_bytes fun b hb => ?_
      rw [r_mem, lose_byte _ _ _ _ _ (by simp only [dist, ea, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
    have ev : val (fun i => c₃.vg.mem.readW (wa wsp (k + 6 + i)) 64) k =
        val (fun i => sqrx8x.tw c₂.vg.mem fp (k + i)) k := val_congr ev1
    rw [ev]; ring
  have hnR := val_lt n k
  have hlt3 : val (ut c₃.vg.mem wsp k (decide ((c₃.vg.gpr .rax).toNat = 1))) (k + 1) < 2 * val n k := by
    have h1 : val a k * val a k < val n k * val n k := Nat.mul_self_lt_mul_self hlt
    have h2 : val n k * val n k ≤ 2 ^ (64 * k) * val n k := Nat.mul_le_mul_right _ (le_of_lt hnR)
    have h3 : Q * val n k ≤ 2 ^ (64 * k) * val n k := Nat.mul_le_mul_right _ (le_of_lt hQ)
    have : val (ut c₃.vg.mem wsp k (decide ((c₃.vg.gpr .rax).toNat = 1))) (k + 1) * 2 ^ (64 * k) <
        2 * val n k * 2 ^ (64 * k) := by
      rw [hV, show 2 * val n k * 2 ^ (64 * k) = 2 ^ (64 * k) * val n k + 2 ^ (64 * k) * val n k by ring]
      linarith
    exact Nat.lt_of_mul_lt_mul_right this
  -- The subtraction and selection.
  have tar : TArr c₃ k np rp wsp :=
    ⟨k29, oN.bound, oP.bound, hwL, by rcases oN.apart with h | h <;> omega, by rcases oP.apart with h | h <;> omega,
      by have := h.sepPN; rw [hk, hrdi, hrcx] at this; exact this,
      by rw [rd3]; exact List.mem_append_left _ rN, by rw [c3_wr]; exact List.mem_cons_of_mem _ hrpw,
      ⟨sp0.toNat + 8 - wsp.toNat, by omega, by rw [c3_wr]; exact List.mem_cons_self⟩⟩
  obtain ⟨c₄, c₅, c₆, c₇, tx1, tx2, tx3, tx4, t_sp, t_si, t_wr, t_oth, t_lo, t_mem, t_lt, t_mod⟩ :=
    tail_ok c₃ k np rp wsp fp sp0 n k8 k0 tar (by omega) hfp c3_sp ((r_g .r8 (by decide)).trans post.r8)
      ((r_g .rcx (by decide)).trans post.rcx)
      (by show (c₃.vg.xmm .xmm1).setWidth 64 = rp; rw [r_xmm, hF2.xmm, c_xmm]; exact x1_5)
      ((r_g .rbp (by decide)).trans post.rbp) (by rw [hrax3]; exact post.rax) hN3 h53 hlt3
  -- Bytes apart from `rp` and from `[fp, sp0)` read before the epilogue as they did.
  have keep7 : ∀ y, sp0.toNat - fp.toNat ≤ (y - fp).toNat → 8 * k ≤ (y - rp).toNat → c₇.vg.mem y = s.vg.mem y :=
    fun y hy hr => by
      have := y.isLt
      rw [t_mem y (by rw [dist]; rw [dist] at hy; omega) hr, keep3 y hy]
  -- The callee-saved registers the prologue pushed.
  have hsave : ∀ c, 8 ≤ c → c ≤ 48 →
      c₇.vg.mem.readW (sp0 - BitVec.ofNat 64 c) 64 = s₄.vg.mem.readW (sp0 - BitVec.ofNat 64 c) 64 := by
    intro c c1 c2
    refine readW_bytes fun b hb => ?_
    have o1 : 8 * k ≤ (sp0 - BitVec.ofNat 64 c + BitVec.ofNat 64 b - rp).toNat := by
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; rcases oP.apart with h | h <;> omega
    have o2 : 8 * (2 * k + 8) ≤ (sp0 - BitVec.ofNat 64 c + BitVec.ofNat 64 b - wsp).toNat := by
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    have o3 : 16 * k + 72 ≤ (sp0 - BitVec.ofNat 64 c + BitVec.ofNat 64 b - fp).toNat := by
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [t_mem _ o2 o1, m3 _ o3, m1 _ o3, h_mem]
  have hsp48 : 48 ≤ sp0.toNat := by omega
  obtain ⟨v15, v14, v13, v12, vbp, vbx⟩ := pushes_saved s.vg.mem sp0 s.vg.gpr hsp48
  rw [← h_mem] at v15 v14 v13 v12 vbp vbx
  -- The epilogue.
  obtain ⟨c₈, hx8, e_sp, e_ax, e15, e14, e13, e12, ebp, ebx, ewr, erd, emx, elo, emem⟩ :=
    epilogue_ok c₇ (sp0.toNat + 8 - wsp.toNat) wsp sp0 _ _ _ _ _ _ rest (by omega) t_sp t_si
      (by rw [t_wr, c3_wr]) rfl
      ((hsave 48 (by omega) le_rfl).trans v15) ((hsave 40 (by omega) (by omega)).trans v14)
      ((hsave 32 (by omega) (by omega)).trans v13) ((hsave 24 (by omega) (by omega)).trans v12)
      ((hsave 16 (by omega) (by omega)).trans vbp) ((hsave 8 le_rfl (by omega)).trans vbx)
  have epi : ∀ y, sp0.toNat - fp.toNat ≤ (y - fp).toNat → c₈.vg.mem y = c₇.vg.mem y := fun y hy => by
    have := y.isLt
    rw [emem, lose_byte _ _ _ _ _ (by rw [dist]; rw [dist] at hy; omega)]
  -- The result.
  have hRv : val (words c₈.vg.mem rp) k = val (fun i => c₇.vg.mem.readW (wa rp i) 64) k :=
    val_congr fun i hi => by
      unfold words
      refine readW_bytes fun c hc => ?_
      exact epi _ (out_byte rp fp sp0 k k i c (by omega) hi oP.bound oP.apart T2 (by omega))
  have hmemP : ∀ y, 8 * k ≤ (y - rp).toNat → 48 * k + 184 ≤ (y - (sp0 - BitVec.ofNat 64 (48 * k + 184))).toNat →
      c₈.vg.mem y = s.vg.mem y := by
    intro y h1 h2
    have f1 := frame_byte y fp sp0 k T2 h2
    rw [epi y f1, keep7 y f1 h1]
  have xt := Exec.seq tx1 (Exec.seq tx2 (Exec.seq tx3 (Exec.seq tx4 (Exec.block hx8))))
  rw [List.nil_append] at xt
  refine ⟨c₈, Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 (Exec.seq hx4 (Exec.seq (Exec.block hx5) (Exec.seq hxc
    xt))))), ?_⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_⟩, e_ax, by rw [ewr, hwr], ?_⟩
  · rw [hrdi, hrcx, hk, hRv]; exact t_lt
  · rw [hrdi, hrcx, hrsi, hk, hRv, Nat.mul_mod, t_mod, ← Nat.mul_mod, hV, Nat.add_mul_mod_self_right]
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
    refine readW_bytes fun c hc => ?_
    obtain ⟨r1, r2⟩ := ret_byte rp sp0 k c hc (by omega) (by omega) oP.bound oP.apart
    exact hmemP _ r1 r2
  · rw [emx, others_mxcsr t_oth, r_mx, others_mxcsr hF2.others, c_mx, others_mxcsr oth5, h_mx]
  · rw [erd, others_rd t_oth, rd3]

theorem constant_time (inT : Nat → Addr → Addr → Addr → List Leak) (hin : Internal inT) :
    ConstantTime I Pre Pub Rind.X86_64.Sqrx8xMont.prog := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨e0, e1, e3, e4, e5, e6⟩ x₁ x₂
  obtain ⟨_, y₁, -⟩ := correct inT hin s₁ h₁
  obtain ⟨_, y₂, -⟩ := correct inT hin s₂ h₂
  rw [(exec_det x₁ y₁).1, (exec_det x₂ y₂).1]
  simp only [trace, num, e0, e1, e3, e4, e5, e6]

/-! ## The precondition holds of some state -/

set_option exponentiation.threshold 512 in
set_option maxRecDepth 8192 in
theorem pre_witness : Pre witness := by
  have hk : num witness = 8 := by decide
  refine ⟨?_, ?_, ?_, ⟨[⟨0x200000#64, 64⟩], rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [hk, OffFrame, frameLen]) <;> decide

/-- Given `bn_sqrx8x_internal`'s contract, the routine computes the Montgomery square of its argument, keeping what
the System V ABI and its contract require; its trace depends only on its arguments and the stack pointer; and some
state meets its precondition. -/
theorem bn_sqrx8x_mont_correct_of (inT : Nat → Addr → Addr → Addr → List Leak) (hin : Internal inT) :
    (∀ s, Pre s → ∃ t s', Exec I Rind.X86_64.Sqrx8xMont.prog s t s' ∧ Post s s') ∧
      ConstantTime I Pre Pub Rind.X86_64.Sqrx8xMont.prog ∧ ∃ s, Pre s :=
  ⟨fun s h => let ⟨s', e, p⟩ := correct inT hin s h; ⟨_, s', e, p⟩, constant_time inT hin, _, pre_witness⟩

end rind.x86_64.sqrx8xmont

/-- info: 'rind.x86_64.sqrx8xmont.bn_sqrx8x_mont_correct_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.sqrx8xmont.bn_sqrx8x_mont_correct_of
