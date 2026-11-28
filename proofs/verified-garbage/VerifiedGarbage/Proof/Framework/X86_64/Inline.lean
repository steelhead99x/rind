module

public import VerifiedGarbage.Proof.Framework.Inline
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-!
# Inlining verified code (x86-64)

The inlining theory (`Proof/Framework/Inline.lean`) for x86-64 states
(`regionModel`): running code from a state that permits more memory gives
the same result (`Exec.widen`), code never writes outside the regions its
state permits (`Exec.regions`), and `WP.inline` combines the two with the
correctness part of the inlined function's `Verified` proof.
-/

@[expose] public section

namespace VG.X86_64

/-- `s`, permitted to read `rd` and write `wr` instead. -/
def State.withRegions (s : State) (rd wr : List Region) : State := { s with rd := rd, wr := wr }

@[simp] theorem State.withRegions_gpr (s : State) (rd wr) : (s.withRegions rd wr).gpr = s.gpr := rfl
@[simp] theorem State.withRegions_mem (s : State) (rd wr) : (s.withRegions rd wr).mem = s.mem := rfl
@[simp] theorem State.withRegions_mxcsr (s : State) (rd wr) : (s.withRegions rd wr).mxcsr = s.mxcsr := rfl
@[simp] theorem State.withRegions_rd (s : State) (rd wr) : (s.withRegions rd wr).rd = rd := rfl
@[simp] theorem State.withRegions_wr (s : State) (rd wr) : (s.withRegions rd wr).wr = wr := rfl
@[simp] theorem State.withRegions_self (s : State) : s.withRegions s.rd s.wr = s := rfl
@[simp] theorem State.withRegions_withRegions (s : State) (rd wr rd' wr') :
    (s.withRegions rd wr).withRegions rd' wr' = s.withRegions rd' wr' := rfl

section
variable {s s' : State} {rd wr : List Region}

theorem load64_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 64}
    (h : s.load64 a = some v) : (s.withRegions rd wr).load64 a = some v := by
  simp only [State.load64] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load64, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem load32_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 32}
    (h : s.load32 a = some v) : (s.withRegions rd wr).load32 a = some v := by
  simp only [State.load32] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load32, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem load8_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : Byte}
    (h : s.load8 a = some v) : (s.withRegions rd wr).load8 a = some v := by
  simp only [State.load8] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load8, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem readSrc_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {src : Src} {v : BitVec 64}
    (h : readSrc s src = some v) : readSrc (s.withRegions rd wr) src = some v := by
  cases src with
  | mem m => exact load64_widen hc h
  | _ => exact h

theorem readSrc32_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {src : Src} {v : BitVec 32}
    (h : readSrc32 s src = some v) : readSrc32 (s.withRegions rd wr) src = some v := by
  cases src with
  | mem m => exact load32_widen hc h
  | _ => exact h

theorem store64_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 64} (h : s.store64 a v = some s') :
    (s.withRegions rd wr).store64 a v = some (s'.withRegions rd wr) := by
  simp only [State.store64] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store64, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem store32_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 32} (h : s.store32 a v = some s') :
    (s.withRegions rd wr).store32 a v = some (s'.withRegions rd wr) := by
  simp only [State.store32] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store32, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem store8_widen (hc : Covers s.wr wr) {a : Addr} {v : Byte} (h : s.store8 a v = some s') :
    (s.withRegions rd wr).store8 a v = some (s'.withRegions rd wr) := by
  simp only [State.store8] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store8, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem store16_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 16} (h : s.store16 a v = some s') :
    (s.withRegions rd wr).store16 a v = some (s'.withRegions rd wr) := by
  simp only [State.store16] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store16, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem load16_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 16}
    (h : s.load16 a = some v) : (s.withRegions rd wr).load16 a = some v := by
  simp only [State.load16] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load16, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem load128_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 128}
    (h : s.load128 a = some v) : (s.withRegions rd wr).load128 a = some v := by
  simp only [State.load128] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load128, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store128_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 128} (h : s.store128 a v = some s') :
    (s.withRegions rd wr).store128 a v = some (s'.withRegions rd wr) := by
  simp only [State.store128] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store128, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem load256_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 256}
    (h : s.load256 a = some v) : (s.withRegions rd wr).load256 a = some v := by
  simp only [State.load256] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load256, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h


theorem setVy_withRegions (s : State) (rd wr : List Region) (r : VReg) (v : BitVec 256) :
    (s.withRegions rd wr).setVy r v = (s.setVy r v).withRegions rd wr := by
  cases r <;> rfl

theorem setVz_withRegions (s : State) (rd wr : List Region) (r : VReg) (l0 l1 l2 l3 : BitVec 128) :
    (s.withRegions rd wr).setVz r l0 l1 l2 l3 = (s.setVz r l0 l1 l2 l3).withRegions rd wr := by
  cases r <;> rfl

theorem store256_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 256} (h : s.store256 a v = some s') :
    (s.withRegions rd wr).store256 a v = some (s'.withRegions rd wr) := by
  simp only [State.store256] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store256, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem load512_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) {a : Addr} {v : BitVec 512}
    (h : s.load512 a = some v) : (s.withRegions rd wr).load512 a = some v := by
  simp only [State.load512] at h
  split at h <;> [rename_i hi; cases h]
  simp only [State.load512, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, hc _ _ hi,
    ite_true]
  exact h

theorem store512_widen (hc : Covers s.wr wr) {a : Addr} {v : BitVec 512} (h : s.store512 a v = some s') :
    (s.withRegions rd wr).store512 a v = some (s'.withRegions rd wr) := by
  simp only [State.store512] at h
  split at h <;> [rename_i hi; cases h]
  cases h
  simp only [State.store512, State.withRegions_wr, hc _ _ hi, ite_true]; rfl

theorem exec_widen (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) {i : Instr}
    (h : exec i s = some s') : exec i (s.withRegions rd wr) = some (s'.withRegions rd wr) := by
  cases i with
  | mov d src =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec, readSrc_widen hc hv, Option.map_some]; rfl
  | mov32 d src =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec, readSrc32_widen hc hv, Option.map_some]; rfl
  | movzx8 d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load8_widen hc hv]; rfl
  | movzx16 d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load16_widen hc hv]; rfl
  | store m r => exact store64_widen hw h
  | store32 m r => exact store32_widen hw h
  | store8 m r => exact store8_widen hw h
  | store16 m r => exact store16_widen hw h
  | alu op d src =>
    simp only [reduceExec, Taint.execAlu_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, out, ho, rfl⟩ := h
    refine ⟨b, readSrc_widen hc hb, out, ho, ?_⟩
    split <;> rfl
  | alu32 op d src =>
    simp only [reduceExec, Taint.execAlu32_eq, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨b, hb, out, ho, rfl⟩ := h
    refine ⟨b, readSrc32_widen hc hb, out, ho, ?_⟩
    split <;> rfl
  | shift32 op d n =>
    simp only [reduceExec, execShift32] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | bswap32 d => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | rorx32 d r n =>
    simp only [reduceExec, execRorx32] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    simp only [Option.some.injEq] at h; subst h; rfl
  | andn32 d a b => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | rorx d r n =>
    simp only [reduceExec, execRorx] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    simp only [Option.some.injEq] at h; subst h; rfl
  | andn d a b => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | shiftCl op d => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | shiftx op d r c => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | bswap d => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | shift op d n =>
    simp only [reduceExec, execShift] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    cases op <;> (simp only [Option.some.injEq] at h; subst h; rfl)
  | movImm64 d v => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | leaSym d name => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | aluTbl op d m n ws =>
    have e : ∀ b, execAluW op d b (s.withRegions rd wr) = (execAluW op d b s).map (·.withRegions rd wr) := by
      intro b; cases op <;> first | rfl | (simp only [execAluW, Option.map_map]; rfl)
    simp only [reduceExec] at h ⊢
    split at h <;> [rename_i hc'; cases h]
    have e₁ : (s.withRegions rd wr).ea m = s.ea m := rfl
    have e₂ : (s.withRegions rd wr).syms = s.syms := rfl
    have e₃ : (s.withRegions rd wr).gpr = s.gpr := rfl
    simp only [e₁, e₂, e₃]
    split
    · rw [e, h]; rfl
    · contradiction
  | vmovdquTbl d m n ws | movdquTbl d m n ws =>
    simp only [reduceExec] at h ⊢
    split at h <;> [rename_i hc'; cases h]
    cases h
    have e₁ : (s.withRegions rd wr).ea m = s.ea m := rfl
    have e₂ : (s.withRegions rd wr).syms = s.syms := rfl
    have e₃ : (s.withRegions rd wr).gpr = s.gpr := rfl
    simp only [e₁, e₂, e₃]
    exact ite_eq_left_of_eq_true _ _ (eq_true hc') |>.trans rfl
  | vpmovmskb len d r => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | vpcmpltuw d a b => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | movqR d r => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | movdquLoad d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | movdquStore m r => exact store128_widen hw h
  | xop op => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; cases op <;> rfl
  | vop op =>
    simp only [reduceExec, Option.some.injEq] at h ⊢; subst h
    cases op <;> simp only [VOp.exec] <;> (try split) <;> rfl
  | vmovdquLoad len d m =>
    cases len
    · simp only [reduceExec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [reduceExec]
      rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [reduceExec]
      rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv]; rfl
  | vbroadcasti128 d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | vbinLoad op len d a m =>
    cases len
    · simp only [reduceExec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [reduceExec]
      rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, rfl⟩ := h
      simp only [reduceExec]
      rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv]; rfl
  | vmovdquStore len m r =>
    cases len
    · exact store128_widen hw h
    · exact store256_widen hw h
  | zop op =>
    simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; cases op <;> rfl
  | eop op =>
    simp only [reduceExec, Option.some.injEq] at h ⊢; subst h
    cases op <;> exact setVy_withRegions _ _ _ _ _
  | evLoad d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv, Option.map_some,
      setVy_withRegions]
  | evMadd52Load hi d a m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv, Option.map_some,
      setVy_withRegions]
    rfl
  | evStore m r | e5ExtractStore m r _ => exact store256_widen hw h
  | e5op op =>
    simp only [reduceExec, Option.some.injEq] at h ⊢; subst h
    cases op <;> exact setVz_withRegions _ _ _ _ _ _ _ _
  | evBroadcastLoad d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load64_widen hc hv, Option.map_some,
      setVy_withRegions]
  | e5InsertLoad d a m n =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv, Option.map_some,
      setVz_withRegions]
    rfl
  | kLoad k d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, State.withRegions_gpr,
      State.loadMasked512_mono (t := s.withRegions rd wr) hc rfl hv]; rfl
  | kStore m k r =>
    simp only [reduceExec] at h ⊢
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, State.withRegions_gpr,
      show (s.withRegions rd wr).zmm r = s.zmm r from rfl,
      State.storeMasked512_mono (t := s.withRegions rd wr) hw rfl h]
    obtain ⟨_, rfl⟩ := State.storeMasked512_eq h; rfl
  | kLoad8 k d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, State.withRegions_gpr,
      State.loadMasked512B_mono (t := s.withRegions rd wr) hc rfl hv]; rfl
  | kStore8 m k r =>
    simp only [reduceExec] at h ⊢
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, State.withRegions_gpr,
      show (s.withRegions rd wr).zmm r = s.zmm r from rfl,
      State.storeMasked512B_mono (t := s.withRegions rd wr) hw rfl h]
    obtain ⟨_, rfl⟩ := State.storeMasked512B_eq h; rfl
  | vmovdqu32Load d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load512_widen hc hv]; rfl
  | vbroadcasti32x4 d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | vbroadcasti32x4H d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load128_widen hc hv]; rfl
  | zbcst op d a m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load64_widen hc hv]; rfl
  | vpbroadcastdZ d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load32_widen hc hv]; rfl
  | zbcstd op d a m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load32_widen hc hv]; rfl
  | vpmadd52Load hi d a m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h
    obtain ⟨v, hv, rfl⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load256_widen hc hv]; rfl
  | vmovdqu32Store m r => exact store512_widen hw h
  | stmxcsr m => exact store32_widen hw h
  | ldmxcsr m =>
    simp only [reduceExec, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    simp only [reduceExec]
    rw [show (s.withRegions rd wr).ea m = s.ea m from rfl, load32_widen hc hv, Option.bind_some]
    split at h <;> [cases h; cases h]
    rename_i hr; simp only [hr, ite_true]; rfl
  | lfence => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | mul r => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | imul d r => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | imul3 d r v => simp only [reduceExec, Option.some.injEq] at h ⊢; subst h; rfl
  | shld d r n =>
    simp only [reduceExec, execShld] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, and_self, ite_true]
    simp only [Option.some.injEq] at h; subst h; rfl
  | btr d n =>
    simp only [reduceExec, execBtr] at h ⊢
    split at h <;> [skip; cases h]
    rename_i hn
    simp only [hn, ite_true]
    simp only [Option.some.injEq] at h; subst h; rfl
  | mulx hi lo src =>
    simp only [reduceExec, execMulx] at h ⊢
    split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, rfl⟩
  | adcx d src =>
    simp only [reduceExec, execAdcx] at h ⊢
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, c, hc', rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, c, hc', rfl⟩
  | adox d src =>
    simp only [reduceExec, execAdox] at h ⊢
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, c, hc', rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, c, hc', rfl⟩
  | cmov cc d src =>
    simp only [reduceExec, execCmov] at h ⊢
    split at h
    · cases h
    · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
      obtain ⟨b, hb, c, hc', rfl⟩ := h
      exact ⟨b, readSrc_widen hc hb, c, by cases cc <;> exact hc', by cases c <;> rfl⟩
  | push | pop | alloc | free | callr => simp only [reduceExec, reduceCtorEq] at h

theorem addrs_withRegions (i : Instr) (s : State) (rd wr : List Region) :
    addrs i (s.withRegions rd wr) = addrs i s := by
  cases i <;> rfl

theorem exec_regions {i : Instr} (h : exec i s = some s') : s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i with
  | store m r =>
    simp only [reduceExec, State.store64] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | store32 m r =>
    simp only [reduceExec, State.store32] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | store8 m r =>
    simp only [reduceExec, State.store8] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | store16 m r =>
    simp only [reduceExec, State.store16] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | movdquStore m r =>
    simp only [reduceExec, State.store128] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | movdquLoad d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | xop op => simp only [reduceExec, Option.some.injEq] at h; subst h; cases op <;> exact ⟨rfl, rfl⟩
  | vop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]; exact ⟨rfl, rfl⟩
  | vmovdquLoad len d m | vbinLoad _ len d _ m =>
    cases len <;> simp only [reduceExec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
      exact ⟨rfl, rfl⟩
  | vmovdquTbl d m n ws | movdquTbl d m n ws => simp only [reduceExec] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | vbroadcasti128 d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | vmovdquStore len m r =>
    cases len
    · simp only [reduceExec, State.store128] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
    · simp only [reduceExec, State.store256] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | zop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]; exact ⟨rfl, rfl⟩
  | eop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.EOp.exec_eq op s]; exact ⟨rfl, rfl⟩
  | e5op op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.E5Op.exec_eq op s]; exact ⟨rfl, rfl⟩
  | evLoad d m | evMadd52Load _ d _ m | evBroadcastLoad d m | e5InsertLoad d _ m _ =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; cases d <;> exact ⟨rfl, rfl⟩
  | evStore m r | e5ExtractStore m r _ =>
    simp only [reduceExec, State.store256] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | kLoad k d m | kLoad8 k d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | kStore m k r => obtain ⟨_, rfl⟩ := State.storeMasked512_eq h; exact ⟨rfl, rfl⟩
  | kStore8 m k r => obtain ⟨_, rfl⟩ := State.storeMasked512B_eq h; exact ⟨rfl, rfl⟩
  | vmovdqu32Load d m | vbroadcasti32x4 d m | zbcst _ d _ m | vpbroadcastdZ d m | zbcstd _ d _ m | vpmadd52Load _ d _ m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | vbroadcasti32x4H d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | vmovdqu32Store m r =>
    simp only [reduceExec, State.store512] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | stmxcsr m =>
    simp only [reduceExec, State.store32] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | ldmxcsr m =>
    simp only [reduceExec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
    split at h <;> cases h; exact ⟨rfl, rfl⟩
  | lfence => simp only [reduceExec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | mul r => simp only [reduceExec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | imul d r => simp only [reduceExec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | imul3 d r v => simp only [reduceExec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  | shld d r n => simp only [reduceExec, execShld] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | btr d n => simp only [reduceExec, execBtr] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩
  | mulx hi lo src =>
    simp only [reduceExec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | push | pop | alloc | free | callr => simp only [reduceExec, reduceCtorEq] at h
  | _ => exact ⟨(Taint.exec_nonstore rfl h).1, (Taint.exec_nonstore rfl h).2.1⟩

theorem exec_frame {i : Instr} (h : exec i s = some s') : Frame s.wr s.mem s'.mem := by
  cases i with
  | store m r =>
    simp only [reduceExec, State.store64] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | store32 m r =>
    simp only [reduceExec, State.store32] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | store8 m r =>
    simp only [reduceExec, State.store8] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | store16 m r =>
    simp only [reduceExec, State.store16] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | movdquStore m r =>
    simp only [reduceExec, State.store128] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | movdquLoad d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | xop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; cases op <;> exact Frame.refl _ _
  | vop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.VOp.exec_eq op s]; exact Frame.refl _ _
  | vmovdquLoad len d m | vbinLoad _ len d _ m =>
    cases len <;> simp only [reduceExec, Option.map_eq_some_iff] at h <;> obtain ⟨_, _, rfl⟩ := h <;>
      exact Frame.refl _ _
  | vmovdquTbl d m n ws | movdquTbl d m n ws => simp only [reduceExec] at h; split at h <;> cases h; exact Frame.refl _ _
  | vbroadcasti128 d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | vmovdquStore len m r =>
    cases len
    · simp only [reduceExec, State.store128] at h; split at h <;> cases h
      rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
    · simp only [reduceExec, State.store256] at h; split at h <;> cases h
      rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | zop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.ZOp.exec_eq op s]; exact Frame.refl _ _
  | eop op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.EOp.exec_eq op s]; exact Frame.refl _ _
  | e5op op =>
    simp only [reduceExec, Option.some.injEq] at h; subst h; rw [Taint.E5Op.exec_eq op s]; exact Frame.refl _ _
  | evLoad d m | evMadd52Load _ d _ m | evBroadcastLoad d m | e5InsertLoad d _ m _ =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; cases d <;> exact Frame.refl _ _
  | evStore m r | e5ExtractStore m r _ =>
    simp only [reduceExec, State.store256] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | kLoad k d m | kLoad8 k d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | kStore m k r => exact State.storeMasked512_frame h
  | kStore8 m k r => exact State.storeMasked512B_frame h
  | vmovdqu32Load d m | vbroadcasti32x4 d m | zbcst _ d _ m | vpbroadcastdZ d m | zbcstd _ d _ m | vpmadd52Load _ d _ m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | vbroadcasti32x4H d m =>
    simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | vmovdqu32Store m r =>
    simp only [reduceExec, State.store512] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | stmxcsr m =>
    simp only [reduceExec, State.store32] at h; split at h <;> cases h
    rename_i hi; obtain ⟨r, hr, hc⟩ := hi; exact (Frame.refl _ _).writeW hr _ hc
  | ldmxcsr m =>
    simp only [reduceExec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
    split at h <;> cases h; exact Frame.refl _ _
  | lfence => simp only [reduceExec, Option.some.injEq] at h; subst h; exact Frame.refl _ _
  | mul r => simp only [reduceExec, Option.some.injEq] at h; subst h; exact Frame.refl _ _
  | imul d r => simp only [reduceExec, Option.some.injEq] at h; subst h; exact Frame.refl _ _
  | imul3 d r v => simp only [reduceExec, Option.some.injEq] at h; subst h; exact Frame.refl _ _
  | shld d r n => simp only [reduceExec, execShld] at h; split at h <;> cases h; exact Frame.refl _ _
  | btr d n => simp only [reduceExec, execBtr] at h; split at h <;> cases h; exact Frame.refl _ _
  | mulx hi lo src =>
    simp only [reduceExec, execMulx] at h; split at h
    · cases h
    · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; exact Frame.refl _ _
  | push | pop | alloc | free | callr => simp only [reduceExec, reduceCtorEq] at h
  | _ => rw [(Taint.exec_nonstore rfl h).2.2.1]; exact Frame.refl _ _

theorem eval_withRegions (c : Cond) (s : State) (rd wr : List Region) :
    eval c (s.withRegions rd wr) = eval c s := by
  cases c <;> rfl

end

/-- Calls and returns change only `rsp` (by 8 each way), and the memory. -/
theorem call_gpr {s s' : State} (h : isa.call s = some s') (r : Reg) :
    s'.gpr r = if r = .rsp then s.gpr .rsp - 8 else s.gpr r := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_gpr {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') (r : Reg) :
    s₂.gpr .rsp = s₁.gpr .rsp ∧ s'.gpr r = if r = .rsp then s₂.gpr .rsp + 8 else s₂.gpr r := by
  simp only [isa, ret] at h; split at h <;> cases h; rename_i hc; exact ⟨hc.1, rfl⟩

theorem ofNat_eight_mul_succ (n : Nat) :
    BitVec.ofNat 64 (8 * (n + 1)) = BitVec.ofNat 64 (8 * n) + 8 := by
  rw [show 8 * (n + 1) = 8 * n + 8 by omega_using [], BitVec.ofNat_add]; rfl

theorem pushRegs_eq (s : State) (rs : List Reg) :
    (pushRegs s rs).rd = s.rd ∧ (pushRegs s rs).wr = s.wr ∧
      (pushRegs s rs).gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * rs.length) ∧
      ∀ r, r ≠ .rsp → (pushRegs s rs).gpr r = s.gpr r := by
  induction rs generalizing s with
  | nil => exact ⟨rfl, rfl, by simp [pushRegs], fun _ _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih { s.setReg .rsp (s.gpr .rsp - 8) with
      mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) }
    refine ⟨h₁, h₂, ?_, fun r hr => ?_⟩
    · simp only [pushRegs, h₃, List.length_cons, ofNat_eight_mul_succ]
      simp only [State.setReg, ite_true]
      rw [BitVec.sub_sub, BitVec.add_comm]
    · simp only [pushRegs, h₄ r hr]
      simp [State.setReg, hr]

theorem popReg_eq (s : State) (d : Reg) (k : Nat) :
    (popReg s d k).rd = s.rd ∧ (popReg s d k).wr = s.wr ∧
      (popReg s d k).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (8 * k) ∧
      ∀ r, r ≠ .rsp → r ≠ d → (popReg s d k).gpr r = s.gpr r := by
  induction k generalizing s with
  | zero => exact ⟨rfl, rfl, by simp [popReg], fun _ _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih ((s.setReg d (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp
      (s.gpr .rsp + 8))
    refine ⟨h₁, h₂, ?_, fun r hr hr' => ?_⟩
    · simp only [popReg, h₃, ofNat_eight_mul_succ]
      simp only [State.setReg, ite_true]
      rw [BitVec.add_assoc, BitVec.add_comm (8 : BitVec 64)]
    · simp only [popReg, h₄ r hr hr']
      simp [State.setReg, hr, hr']

theorem pushRegs_withRegions (s : State) (rs : List Reg) (rd wr : List Region) :
    pushRegs (s.withRegions rd wr) rs = (pushRegs s rs).withRegions rd wr := by
  induction rs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    exact ih { s.setReg .rsp (s.gpr .rsp - 8) with mem := s.mem.writeW (s.gpr .rsp - 8) (s.gpr x) }

theorem popReg_withRegions (s : State) (d : Reg) (k : Nat) (rd wr : List Region) :
    popReg (s.withRegions rd wr) d k = (popReg s d k).withRegions rd wr := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    exact ih ((s.setReg d (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8))

/-- A frame's push adds its region at the head of `wr`, and changes no
register but `rsp`. -/
theorem push_eq {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ k, s₁.rd = s.rd ∧ s₁.wr = ⟨s₁.gpr .rsp, 8 * k⟩ :: s.wr ∧
      (∀ r, r ≠ .rsp → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 (8 * k) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case push rs =>
    split at h <;> cases h
    obtain ⟨h₁, -, h₃, h₄⟩ := pushRegs_eq s rs
    exact ⟨rs.length, h₁, by rw [h₃], h₄, h₃⟩
  case alloc bytes =>
    split at h <;> cases h
    rename_i hc
    have e : 8 * (bytes / 8) = bytes := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.2.2.1)
    refine ⟨bytes / 8, rfl, ?_, fun r hr => ?_, ?_⟩
    · simp only [State.setReg, ite_true, e]
    · simp only [State.setReg, hr, ite_false]
    · simp only [State.setReg, ite_true, e]

/-- A frame's pop removes the region at the head of `wr`, and changes only
its register and `rsp`. -/
theorem pop_eq {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s₂.wr = s₁.wr ∧ s'.rd = s₂.rd ∧ s'.wr = s₂.wr.tail ∧
      (∀ r, r ≠ .rsp → Taint.clobbers j r = false → s'.gpr r = s₂.gpr r) ∧
      s₂.gpr .rsp = s₁.gpr .rsp ∧
      ∃ k, s₁.wr.head? = some ⟨s₁.gpr .rsp, 8 * k⟩ ∧
        s'.gpr .rsp = s₂.gpr .rsp + BitVec.ofNat 64 (8 * k) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case pop d k =>
    split at h <;> cases h
    rename_i hc
    obtain ⟨h₁, -, h₃, h₄⟩ := popReg_eq s₂ d k
    refine ⟨hc.2.2.2.1, h₁, rfl, fun r hr hd => h₄ r hr ?_, hc.2.2.1, k, hc.2.2.2.2, h₃⟩
    intro e; subst e; simp [Taint.clobbers] at hd
  case free bytes =>
    split at h <;> cases h
    rename_i hc
    have e : 8 * (bytes / 8) = bytes := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.2.2.1)
    refine ⟨hc.2.2.2.2.1, rfl, rfl, fun r hr _ => ?_, hc.2.2.2.1, bytes / 8, by rw [e]; exact hc.2.2.2.2.2,
      ?_⟩
    · simp only [State.setReg, hr, ite_false]
    · simp only [State.setReg, ite_true, e]

theorem push_widen {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    ∃ f, s₁.rd = s.rd ∧ s₁.wr = f :: s.wr ∧ ∀ rd wr,
      isa.push i (s.withRegions rd wr) = some (s₁.withRegions rd (f :: wr)) := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h
  case push rs =>
    split at h <;> cases h
    rename_i hc
    refine ⟨_, (pushRegs_eq s rs).1, rfl, fun rd wr => ?_⟩
    simp only [isa, push, State.withRegions_gpr, ne_eq, hc.1, hc.2.1, hc.2.2, not_false_eq_true,
      and_self, ite_true, pushRegs_withRegions]
    rfl
  case alloc bytes =>
    split at h <;> cases h
    rename_i hc
    refine ⟨_, rfl, rfl, fun rd wr => ?_⟩
    simp only [isa, push, State.withRegions_gpr, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, and_self, ite_true]
    rfl

theorem pop_widen {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') (rd : List Region)
    {wr : List Region} (hw : wr.head? = s₁.wr.head?) :
    isa.pop j (s₁.withRegions rd wr) (s₂.withRegions rd wr) = some (s'.withRegions rd wr.tail) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h
  case pop =>
    split at h <;> cases h
    rename_i hc
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, ne_eq, hw, hc.1, hc.2.1,
      hc.2.2.1, hc.2.2.2.2, and_self, ite_true, not_false_eq_true, popReg_withRegions]
    rfl
  case free =>
    split at h <;> cases h
    rename_i hc
    simp only [isa, pop, State.withRegions_gpr, State.withRegions_wr, hw, hc.1, hc.2.1, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2.2, and_self, ite_true]
    rfl

theorem exec_gpr {i : Instr} {r : Reg} (hi : Taint.clobbers i r = false) {s s' : State}
    (h : exec i s = some s') : s'.gpr r = s.gpr r := by
  cases hd : Taint.dstOf i with
  | some d =>
    have hc : Taint.clobbers i d = true := by cases i <;> cases hd <;> exact beq_self_eq_true _
    refine (Taint.exec_nonstore hd h).2.2.2 r fun h' => ?_
    rw [h', hc] at hi; cases hi
  | none =>
    cases i <;> cases hd
    · simp only [reduceExec, State.store64] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, State.store32] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, State.store8] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, State.store16] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, State.store128] at h; split at h <;> cases h; rfl
    · simp only [reduceExec] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.some.injEq] at h; subst h; rename_i op; cases op <;> rfl
    · simp only [reduceExec, Option.some.injEq] at h; subst h; rename_i op
      rw [Taint.VOp.exec_eq op s]
    · rename_i len _ _; cases len <;> simp only [reduceExec, Option.map_eq_some_iff] at h <;>
        obtain ⟨_, _, rfl⟩ := h <;> rfl
    · rename_i len _ _; cases len
      · simp only [reduceExec, State.store128] at h; split at h <;> cases h; rfl
      · simp only [reduceExec, State.store256] at h; split at h <;> cases h; rfl
    · simp only [reduceExec] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · rename_i len _ _ _; cases len <;> simp only [reduceExec, Option.map_eq_some_iff] at h <;>
        obtain ⟨_, _, rfl⟩ := h <;> rfl
    · simp only [reduceExec, Option.some.injEq] at h; subst h; rename_i op
      rw [Taint.ZOp.exec_eq op s]
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, State.store512] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · simp only [reduceExec, Option.some.injEq] at h; subst h; rename_i op
      rw [Taint.EOp.exec_eq op s]
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
      rw [Taint.setVy_eq]
    · simp only [reduceExec, State.store256] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
      rw [Taint.setVy_eq]
    · simp only [reduceExec, Option.some.injEq] at h; subst h; rename_i op
      rw [Taint.E5Op.exec_eq op s]
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
      rw [Taint.setVy_eq]
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
      rw [Taint.setVz_eq]
    · simp only [reduceExec, State.store256] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · obtain ⟨_, rfl⟩ := State.storeMasked512_eq h; rfl
    · simp only [reduceExec, Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h; rfl
    · obtain ⟨_, rfl⟩ := State.storeMasked512B_eq h; rfl
    · simp only [reduceExec, State.store32] at h; split at h <;> cases h; rfl
    · simp only [reduceExec, Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h
      split at h <;> cases h; rfl
    · simp only [reduceExec, Option.some.injEq] at h; subst h; rfl
    · rename_i q
      simp only [Taint.clobbers, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
      simp only [reduceExec, Option.some.injEq] at h; subst h
      exact Taint.execMul_gpr q s hi.1 hi.2
    · rename_i hi' lo src
      simp only [Taint.clobbers, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
      simp only [reduceExec, execMulx] at h; split at h
      · cases h
      · simp only [Option.map_eq_some_iff] at h; obtain ⟨_, _, rfl⟩ := h
        exact Taint.mulx_gpr s _ _ hi.1 hi.2
    · simp only [reduceExec, reduceCtorEq] at h
    · simp only [reduceExec, reduceCtorEq] at h
    · simp only [reduceExec, reduceCtorEq] at h
    · simp only [reduceExec, reduceCtorEq] at h
    · simp only [reduceExec, reduceCtorEq] at h

/-- A call and its return restore every register, `rsp` included. -/
theorem call_ret_gpr {s s₁ s₂ s' : State} (hc : isa.call s = some s₁) (hr : isa.ret s₁ s₂ = some s')
    {r : Reg} (hb : s₂.gpr r = s₁.gpr r) : s'.gpr r = s.gpr r := by
  obtain ⟨hsp, h'⟩ := ret_gpr hr r
  rw [h']
  by_cases hrs : r = .rsp
  · subst hrs
    rw [ite_eq_left rfl, hsp, call_gpr hc, ite_eq_left rfl]
    exact BitVec.sub_add_cancel _ _
  · simp only [hrs, ite_false, hb, call_gpr hc]

/-- A frame restores every register but its pop's. -/
theorem frame_gpr {i j : Instr} {s s₁ s₂ s' : State} {r : Reg} (hj : Taint.clobbers j r = false)
    (hp : isa.push i s = some s₁) (hq : isa.pop j s₁ s₂ = some s') (hb : s₂.gpr r = s₁.gpr r) :
    s'.gpr r = s.gpr r := by
  obtain ⟨k, -, w₁, g₁, e₁⟩ := push_eq hp
  obtain ⟨-, -, -, g₂, e₂, k', h₃, e₃⟩ := pop_eq hq
  by_cases hrs : r = .rsp
  · subst hrs
    rw [w₁] at h₃
    simp only [List.head?_cons, Option.some.injEq, Region.mk.injEq] at h₃
    have : k = k' := by omega_using [h₃]
    subst this
    rw [e₃, hb, e₁, BitVec.sub_add_cancel]
  · rw [g₂ r hrs hj, hb, g₁ r hrs]

/-- The permissions of x86-64 states, for the inlining theory
(`Proof/Framework/Inline.lean`). -/
def regionModel : RegionModel isa where
  rd := State.rd
  wr := State.wr
  mem := State.mem
  withRegions := State.withRegions
  rd_with _ _ _ := rfl
  wr_with _ _ _ := rfl
  mem_with _ _ _ := rfl
  with_self _ := rfl
  with_with _ _ _ _ _ := rfl
  exec_regions h := ⟨(exec_regions h).1, (exec_regions h).2, exec_frame h⟩
  exec_widen hc hw h := exec_widen hc hw h
  addrs_with := addrs_withRegions
  eval_with := eval_withRegions
  callAddrs_with _ _ _ := rfl
  retAddrs_with _ _ _ := rfl
  call_widen h := by
    simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  ret_widen h := by
    simp only [isa, ret] at h; split at h <;> cases h; rename_i hc
    exact ⟨rfl, rfl, fun _ _ => (ite_eq_left hc).trans rfl⟩
  push_widen := push_widen
  pop_widen h := ⟨(pop_eq h).1, (pop_eq h).2.1, (pop_eq h).2.2.1, fun _ _ hw => pop_widen h _ hw⟩
  icall_with i _ _ _ := by cases i <;> rfl

theorem execBlock_regions {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem :=
  regionModel.execBlock_regions h

/-- The permissions never change. -/
theorem Exec.rdwr {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    s'.rd = s.rd ∧ s'.wr = s.wr :=
  regionModel.rdwr h

/-- Code that calls no function changes memory only within the regions it
may write (a call also stores its return address below the stack pointer). -/
theorem Exec.regions {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s')
    (hn : c.noCalls = true) : s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame s.wr s.mem s'.mem :=
  regionModel.regions h (Code.noFrames_of_noCalls hn) (.inl hn)

/-- Running from a state that permits more memory. -/
theorem Exec.widen {c : Prog isa} {s s' : State} {t : List Leak} {rd wr : List Region}
    (h : Exec isa c s t s') (hc : Covers (s.rd ++ s.wr) (rd ++ wr)) (hw : Covers s.wr wr) :
    Exec isa c (s.withRegions rd wr) t (s'.withRegions rd wr) :=
  regionModel.widen h hc hw

theorem execBlock_gpr {is : List Instr} {r : Reg} (hc : ∀ i ∈ is, Taint.clobbers i r = false)
    {s s' : State} {t : List Leak} (h : execBlock isa is s = some (s', t)) : s'.gpr r = s.gpr r :=
  execBlock_keep (fun s : State => s.gpr r) (fun hi he => exec_gpr hi he) hc h

/-- A register that no instruction writes keeps its value. -/
theorem Exec.gpr {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : s'.gpr r = s.gpr r :=
  Exec.keep (fun s : State => s.gpr r) (fun hi he => exec_gpr hi he) frame_gpr hc (.inr fun _ _ _ _ hc hr hb => call_ret_gpr hc hr hb) h

/-- A register that no instruction writes keeps its value, as a
postcondition. -/
theorem WP.gpr {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {r : Reg}
    (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false) : WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

/-- Inlining verified code: from a state `s` in which the code's precondition
holds once its permissions are narrowed to `rd` and `wr`, the code
terminates in a state satisfying its postcondition and calling-convention
obligations (both on the narrowed states), which has the permissions of `s`,
differs from it in memory only within `wr`, and keeps every register that no
instruction writes. -/
theorem WP.inline {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    {s : State} {rd wr : List Region} (hpre : k.pre (s.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → abiPreserved s s' → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, Taint.clobbers i r = false) → s'.gpr r = s.gpr r) →
      k.post (s.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noCalls = true := by decide +kernel) : WP isa c s Q :=
  regionModel.wp_narrow (hv _ hpre) hc hw (Code.noFrames_of_noCalls hn) (.inl hn)
    fun _ _ he hr hw hf hp => hQ _ hr hw hp.1 hf (fun _ h => Exec.gpr h he) hp.2

/-- Widening writable regions: code verified against `k` is verified against
a contract `k'` whose states permit writing regions that extend (same bases,
at least as long) the ones `k` permits (`wr s`), reading the same ones, if
`k'` asks nothing more. The code runs as it does from the narrowed state,
with the same trace and result. -/
theorem Verified.widen {c : Prog isa} {k k' : Contract isa} (h : Verified target c k)
    (wr : State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (s.withRegions s.rd (wr s)))
    (hwr : ∀ s, k'.pre s → List.Forall₂ Region.Prefix (wr s) s.wr)
    (hpost : ∀ s s', k'.pre s →
      k.post (s.withRegions s.rd (wr s)) (s'.withRegions s.rd (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (s₁.withRegions s₁.rd (wr s₁)) (s₂.withRegions s₂.rd (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified target c k' :=
  regionModel.verified_widen (T := target) (fun _ _ _ _ h => h) h wr hpre hwr hpost hpub hsat

end VG.X86_64
