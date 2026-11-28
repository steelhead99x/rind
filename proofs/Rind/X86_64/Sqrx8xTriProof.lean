import Rind.X86_64.Sqrx8xTriChunks

/-! # bn_sqrx8x_internal's `tri`

`tri` adds the products `b i · b j`, `i < j`, of a row block's eight words `b` of `a` into `t`: its six chunks
in turn, each carry a chunk leaves but the last zero, since the chunk's inputs and products sum to less than its
weight. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- A word written leaves another, apart from it, as it was. -/
theorem readW_writeW_wa (M : Mem) (p q : Addr) (x y : Nat) (v : BitVec 64) (hp : p.toNat + 8 * x + 8 ≤ 2 ^ 64)
    (hq : q.toNat + 8 * y + 8 ≤ 2 ^ 64)
    (h : p.toNat + 8 * x + 8 ≤ q.toNat + 8 * y ∨ q.toNat + 8 * y + 8 ≤ p.toNat + 8 * x) :
    (M.writeW (wa p x) v).readW (wa q y) 64 = M.readW (wa q y) 64 :=
  readW_writeW_sep _ _ _ _ (apart_wa p q x y hp hq h)

theorem prod_le (x y : BitVec 64) : x.toNat * y.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
  Nat.mul_le_mul (by have := x.isLt; omega) (by have := y.isLt; omega)

open Lean Meta Elab Tactic in
/-- The words `x.toNat` and products `x.toNat * y.toNat` of words in `e`. -/
partial def wordTerms (e : Expr) (acc : Array Expr) : Array Expr :=
  let isWord (e : Expr) := e.isAppOfArity ``BitVec.toNat 2
  let acc := if isWord e || (e.isAppOfArity ``HMul.hMul 6 && isWord e.appFn!.appArg! && isWord e.appArg!) then
    if acc.contains e then acc else acc.push e else acc
  match e with
  | .app f a => wordTerms a (wordTerms f acc)
  | .mdata _ b => wordTerms b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Adds the bound of every word and product of words in hypothesis `h`: below `2^64`, and at most
`(2^64 - 1)^2`. -/
elab "word_bounds " h:ident : tactic => withMainContext do
  let ty ← instantiateMVars (← getLocalDeclFromUserName h.getId).type
  for t in wordTerms ty #[] do
    let pf ← if t.isAppOfArity ``BitVec.toNat 2 then mkAppM ``BitVec.isLt #[t.appArg!]
      else mkAppM ``prod_le #[t.appFn!.appArg!.appArg!, t.appArg!.appArg!]
    let g ← getMainGoal
    let (_, g) ← (← g.assert (← mkFreshUserName `hb) (← inferType pf) pf).intro1P
    replaceMainGoal [g]

set_option exponentiation.threshold 4096 in
/-- In the last row, where `t`'s word `16R + 8` is still zero, chunk A leaves no mask. -/
theorem mask_last (w0 w1 o10 o11 o12 o13 o14 o15 r9 r10 r11 r12 r13 r14 r15 b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 64)
    (h : w1.toNat * 2 ^ 128 + w0.toNat * 2 ^ 64 + o10.toNat * 2 ^ 192 + o11.toNat * 2 ^ 256 + o12.toNat * 2 ^ 320 +
      o13.toNat * 2 ^ 384 + o14.toNat * 2 ^ 448 + o15.toNat * 2 ^ 512 + 1 * 2 ^ 576 =
      r10.toNat * 2 ^ 128 + r11.toNat * 2 ^ 192 + r12.toNat * 2 ^ 256 + r13.toNat * 2 ^ 320 + r14.toNat * 2 ^ 384 +
      r15.toNat * 2 ^ 448 + r9.toNat * 2 ^ 64 + b0.toNat * b1.toNat * 2 ^ 64 + b0.toNat * b2.toNat * 2 ^ 128 +
      b0.toNat * b3.toNat * 2 ^ 192 + b0.toNat * b4.toNat * 2 ^ 256 + b0.toNat * b5.toNat * 2 ^ 320 +
      b0.toNat * b6.toNat * 2 ^ 384 + b0.toNat * b7.toNat * 2 ^ 448) : False := by
  have e : r10.toNat * 2 ^ 128 + r11.toNat * 2 ^ 192 + r12.toNat * 2 ^ 256 + r13.toNat * 2 ^ 320 + r14.toNat * 2 ^ 384 +
      r15.toNat * 2 ^ 448 + r9.toNat * 2 ^ 64 + b0.toNat * b1.toNat * 2 ^ 64 + b0.toNat * b2.toNat * 2 ^ 128 +
      b0.toNat * b3.toNat * 2 ^ 192 + b0.toNat * b4.toNat * 2 ^ 256 + b0.toNat * b5.toNat * 2 ^ 320 +
      b0.toNat * b6.toNat * 2 ^ 384 + b0.toNat * b7.toNat * 2 ^ 448 =
      2 ^ 64 * (hsum [r9, r10, r11, r12, r13, r14, r15] + b0.toNat * hsum [b1, b2, b3, b4, b5, b6, b7]) := by
    simp only [hsum]; ring
  have h1 := hsum_lt [r9, r10, r11, r12, r13, r14, r15]
  have h2 := hsum_lt [b1, b2, b3, b4, b5, b6, b7]
  simp only [List.length_cons, List.length_nil] at h1 h2
  have h3 : b0.toNat * hsum [b1, b2, b3, b4, b5, b6, b7] ≤ (2 ^ 64 - 1) * (2 ^ 448 - 1) :=
    Nat.mul_le_mul (by have := b0.isLt; omega) (by omega)
  rw [e] at h
  have h4 : 2 ^ 576 ≤ 2 ^ 64 * (hsum [r9, r10, r11, r12, r13, r14, r15] + b0.toNat * hsum [b1, b2, b3, b4, b5, b6, b7]) := by
    rw [← h]; omega
  generalize hsum [r9, r10, r11, r12, r13, r14, r15] = X at h1 h4
  generalize b0.toNat * hsum [b1, b2, b3, b4, b5, b6, b7] = Y at h3 h4
  omega

/-- `tri`, as its chunks. -/
theorem tri_split : Rind.X86_64.Sqrx8x.tri = triA ++ (triB ++ (triC ++ (triD ++ (triE ++ triF)))) := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `tri` from row block `R`: `t`'s words `16R + 1` to `16R + 8` (the frame's `16R + 8` to `16R + 15`) and
`r9` to `r14`, at weights `2^64` to `2^(64·14)` from `t`'s word `16R`, and the mask in `rcx`, are its
inputs, `r9` to `r15` and `t`'s word `16R + 8`, with the products `b i · b j`. It leaves `rsi` at the next
block, and `zf` whether that is the end of `a`, slot 2. -/
theorem tri_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64) (u8 : BitVec 64)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hrbp : s.vg.gpr .rbp = 0) (hrdx : s.vg.gpr .rdx = b 0)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false)
    (hu : s.vg.mem.readW (wa fp (16 * R + 15)) 64 = u8) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.tri s = some (s', triTrace ap fp R) ∧
      ∃ (w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) (mc : Bool),
      s'.vg.mem = (((((((s.vg.mem.writeW (wa fp (16 * R + 8)) w0).writeW (wa fp (16 * R + 9)) w1).writeW
        (wa fp (16 * R + 10)) w2).writeW (wa fp (16 * R + 11)) w3).writeW (wa fp (16 * R + 12)) w4).writeW
        (wa fp (16 * R + 13)) w5).writeW (wa fp (16 * R + 14)) w6).writeW (wa fp (16 * R + 15)) w7 ∧
      s'.vg.gpr .rsi = wa ap (8 * R + 8) ∧
      s'.vg.zf = some (wa ap (8 * R + 8) - s.vg.mem.readW (wa fp 2) 64 == 0) ∧
      s'.vg.gpr .rcx = 0 - (BitVec.ofBool mc).setWidth 64 ∧
      (u8 = 0 → mc = false) ∧
      s'.vg.gpr .rbp = 0 ∧
      w0.toNat * 2 ^ 64 + w1.toNat * 2 ^ 128 + w2.toNat * 2 ^ 192 + w3.toNat * 2 ^ 256 + w4.toNat * 2 ^ 320 +
        w5.toNat * 2 ^ 384 + w6.toNat * 2 ^ 448 + w7.toNat * 2 ^ 512 + mc.toNat * 2 ^ 576 +
        (s'.vg.gpr .r9).toNat * 2 ^ 576 + (s'.vg.gpr .r10).toNat * 2 ^ 640 + (s'.vg.gpr .r11).toNat * 2 ^ 704 +
        (s'.vg.gpr .r12).toNat * 2 ^ 768 + (s'.vg.gpr .r13).toNat * 2 ^ 832 + (s'.vg.gpr .r14).toNat * 2 ^ 896 =
        (s.vg.gpr .r9).toNat * 2 ^ 64 + (s.vg.gpr .r10).toNat * 2 ^ 128 + (s.vg.gpr .r11).toNat * 2 ^ 192 +
        (s.vg.gpr .r12).toNat * 2 ^ 256 + (s.vg.gpr .r13).toNat * 2 ^ 320 + (s.vg.gpr .r14).toNat * 2 ^ 384 +
        (s.vg.gpr .r15).toNat * 2 ^ 448 + u8.toNat * 2 ^ 512 + diag8 b ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := id ar
  have hAw : ∀ (M : Mem) (x : Nat) (v : BitVec 64), 16 * R + 8 ≤ x → x < 16 * R + 16 →
      (∀ i < 8, M.readW (wa ap (8 * R + i)) 64 = b i) →
      ∀ i < 8, (M.writeW (wa fp x) v).readW (wa ap (8 * R + i)) 64 = b i := by
    intro M x v h1 h2 h i hi
    rw [readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)]
    exact h i hi
  have hSw : ∀ (M : Mem) (x : Nat) (v : BitVec 64), 16 * R + 8 ≤ x → x < 16 * R + 16 →
      (M.writeW (wa fp x) v).readW (wa fp 2) 64 = M.readW (wa fp 2) 64 := by
    intro M x v h1 h2
    exact readW_writeW_wa _ _ _ _ _ _ (by omega) (by omega) (by omega)
  -- A
  obtain ⟨s1, x1, w0, w1, mc, m1, d1, c1, p1, cf1, of1, e1, F1⟩ :=
    triA_ok s k R ap np fp b u8 hR ar hrsi hrdi hrsp hA hrbp hrdx hcf hof hu
  have hmc : u8 = 0 → mc = false := by
    intro h0
    cases mc
    · rfl
    · exfalso
      have h00 : (0 : BitVec 64).toNat = 0 := rfl
      rw [h0, h00, Nat.zero_mul, Nat.add_zero, Bool.toNat_true] at e1
      exact mask_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1
  have rsi1 := (F1.gpr .rsi (by decide)).trans hrsi
  have rdi1 := (F1.gpr .rdi (by decide)).trans hrdi
  have rsp1 := (F1.gpr .rsp (by decide)).trans hrsp
  have hA1 : ∀ i < 8, s1.vg.mem.readW (wa ap (8 * R + i)) 64 = b i := by
    rw [m1]; exact hAw _ _ _ (by omega) (by omega) (hAw _ _ _ (by omega) (by omega) hA)
  -- B
  obtain ⟨s2, x2, w2, w3, cfB, ofB, m2, cf2, of2, d2, e2, F2⟩ :=
    triB_ok s1 k R ap np fp b hR (ar.frame F1) rsi1 rdi1 rsp1 hA1 p1 d1 cf1 of1
  obtain ⟨rfl, rfl⟩ : cfB = false ∧ ofB = false := by
    word_bounds e2
    cases cfB <;> cases ofB <;> simp only [Bool.toNat_true, Bool.toNat_false] at e2 <;>
      first | exact ⟨rfl, rfl⟩ | omega
  have rsi2 := (F2.gpr .rsi (by decide)).trans rsi1
  have rdi2 := (F2.gpr .rdi (by decide)).trans rdi1
  have rsp2 := (F2.gpr .rsp (by decide)).trans rsp1
  have rbp2 := (F2.gpr .rbp (by decide)).trans p1
  have hA2 : ∀ i < 8, s2.vg.mem.readW (wa ap (8 * R + i)) 64 = b i := by
    rw [m2]; exact hAw _ _ _ (by omega) (by omega) (hAw _ _ _ (by omega) (by omega) hA1)
  -- C
  obtain ⟨s3, x3, w4, w5, cfC, ofC, m3, cf3, of3, r8_3, rax3, d3, e3, F3⟩ :=
    triC_ok s2 k R ap np fp b hR ((ar.frame F1).frame F2) rsi2 rdi2 rsp2 hA2 rbp2 d2 cf2 of2
  obtain ⟨rfl, rfl⟩ : cfC = false ∧ ofC = false := by
    word_bounds e3
    cases cfC <;> cases ofC <;> simp only [Bool.toNat_true, Bool.toNat_false] at e3 <;>
      first | exact ⟨rfl, rfl⟩ | omega
  have rsi3 := (F3.gpr .rsi (by decide)).trans rsi2
  have rdi3 := (F3.gpr .rdi (by decide)).trans rdi2
  have rsp3 := (F3.gpr .rsp (by decide)).trans rsp2
  have rbp3 := (F3.gpr .rbp (by decide)).trans rbp2
  have hA3 : ∀ i < 8, s3.vg.mem.readW (wa ap (8 * R + i)) 64 = b i := by
    rw [m3]; exact hAw _ _ _ (by omega) (by omega) (hAw _ _ _ (by omega) (by omega) hA2)
  -- D
  obtain ⟨s4, x4, w6, w7, cfD, ofD, m4, cf4, of4, r14_4, r15_4, r8_4, r9_4, rax4, d4, e4, F4⟩ :=
    triD_ok s3 k R ap np fp b hR (((ar.frame F1).frame F2).frame F3) rsi3 rdi3 rsp3 hA3 r8_3 rax3 rbp3 d3 cf3
      of3
  obtain ⟨rfl, rfl⟩ : cfD = false ∧ ofD = false := by
    word_bounds e4
    cases cfD <;> cases ofD <;> simp only [Bool.toNat_true, Bool.toNat_false] at e4 <;>
      first | exact ⟨rfl, rfl⟩ | omega
  have rsi4 := (F4.gpr .rsi (by decide)).trans rsi3
  have rdi4 := (F4.gpr .rdi (by decide)).trans rdi3
  have rsp4 := (F4.gpr .rsp (by decide)).trans rsp3
  have rbp4 := (F4.gpr .rbp (by decide)).trans rbp3
  have hA4 : ∀ i < 8, s4.vg.mem.readW (wa ap (8 * R + i)) 64 = b i := by
    rw [m4]; exact hAw _ _ _ (by omega) (by omega) (hAw _ _ _ (by omega) (by omega) hA3)
  -- E
  obtain ⟨s5, x5, cfE, ofE, m5, cf5, of5, r12_5, r13_5, r14_5, r8_5, rbx5, d5, e5, F5⟩ :=
    triE_ok s4 k R ap np fp b hR ((((ar.frame F1).frame F2).frame F3).frame F4) rsi4 rdi4 rsp4 hA4 r14_4 r15_4
      r8_4 r9_4 rax4 rbp4 d4 cf4 of4
  obtain rfl : cfE = false := by
    word_bounds e5
    cases cfE <;> simp only [Bool.toNat_true, Bool.toNat_false] at e5 <;> first | rfl | omega
  have rsi5 := (F5.gpr .rsi (by decide)).trans rsi4
  have rdi5 := (F5.gpr .rdi (by decide)).trans rdi4
  have rsp5 := (F5.gpr .rsp (by decide)).trans rsp4
  have rbp5 := (F5.gpr .rbp (by decide)).trans rbp4
  have hA5 : ∀ i < 8, s5.vg.mem.readW (wa ap (8 * R + i)) 64 = b i := by rw [m5]; exact hA4
  -- F
  obtain ⟨s6, x6, m6, rsi6, zf6, e6, F6⟩ :=
    triF_ok s5 k R ap np fp b ofE hR (((((ar.frame F1).frame F2).frame F3).frame F4).frame F5) rsi5 rdi5 rsp5
      hA5 r12_5 r13_5 r14_5 r8_5 rbp5 rbx5 d5 cf5 of5
  have U : ∀ gs : List Reg, (∀ r ∈ gs, r ∈ [Reg.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12,
      .r13, .r14, .r15]) → ∀ {s s' : S}, Frame s s' gs →
      Frame s s' [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] :=
    fun _ hg _ _ h => h.mono hg
  refine ⟨s6, ?_, w0, w1, w2, w3, w4, w5, w6, w7, mc, ?_, rsi6, ?_, ?_, hmc, ?_, ?_, ?_⟩
  · rw [tri_split, execBlock_append, x1, Option.bind_some, execBlock_append, x2, Option.bind_some,
      execBlock_append, x3, Option.bind_some, execBlock_append, x4, Option.bind_some, execBlock_append, x5,
      Option.bind_some, x6]
    rfl
  · rw [m6, m5, m4, m3, m2, m1]
  · rw [zf6, m5, m4, m3, m2, m1]
    simp only [hSw _ _ _ (by omega : 16 * R + 8 ≤ 16 * R + 8) (by omega),
      hSw _ (16 * R + 9) _ (by omega) (by omega), hSw _ (16 * R + 10) _ (by omega) (by omega),
      hSw _ (16 * R + 11) _ (by omega) (by omega), hSw _ (16 * R + 12) _ (by omega) (by omega),
      hSw _ (16 * R + 13) _ (by omega) (by omega), hSw _ (16 * R + 14) _ (by omega) (by omega),
      hSw _ (16 * R + 15) _ (by omega) (by omega)]
  · rw [(F6.gpr .rcx (by decide)).trans ((F5.gpr .rcx (by decide)).trans ((F4.gpr .rcx (by decide)).trans
      ((F3.gpr .rcx (by decide)).trans (F2.gpr .rcx (by decide)))))]
    exact c1
  · exact (F6.gpr .rbp (by decide)).trans rbp5
  · simp only [Bool.toNat_false, zero_mul, add_zero] at e2 e3 e4 e5
    unfold diag8
    zify at e1 e2 e3 e4 e5 e6 ⊢
    set_option exponentiation.threshold 4096 in linear_combination e1 + e2 + e3 + e4 + e5 + e6
  · exact (U _ (by decide) F1).trans ((U _ (by decide) F2).trans ((U _ (by decide) F3).trans
      ((U _ (by decide) F4).trans ((U _ (by decide) F5).trans (U _ (by decide) F6)))))

end rind.x86_64.sqrx8x
