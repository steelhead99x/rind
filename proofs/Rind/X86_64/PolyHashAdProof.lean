import Rind.X86_64.PolyHashAdAsm

open VG VG.X86_64 Rind.X86_64.PolyHashAd rind.x86_64.asm rind.spec.poly1305
open VG.Spec.Poly1305 (bytesAt)

set_option linter.unusedSimpArgs false

/-!
# aws-lc's `poly_hash_ad_internal` on x86_64

rind's structured copy of aws-lc's AAD hash (`RindIsa/X86_64/PolyHashAd.lean`),
proved on rind's x86_64 model: from `r8` bytes of AAD at `rcx` and `r`'s two
words at `rbp`, each below `2^60`, it leaves in `(r10, r11, r12)` an
accumulator below `5 · 2^128` that is, modulo `p`, RFC 8439's with that `r`
over the AAD zero-padded to whole blocks (`padBlocks`, `Rind.Poly1305Limbs`),
and its trace depends only on `rcx`, `r8`, and `rbp`, not on the AAD's bytes
or `r`'s value.
-/

namespace rind.x86_64.polyhashad

/-! ## Addresses, conditions, and bytes -/

/-- `m` bytes from `k` into a readable range are readable. -/
theorem InRegions.sub {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) (k m : Nat)
    (hk : k + m ≤ n) : InRegions rs (a + BitVec.ofNat 64 k) m := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  unfold Region.Contains at *
  have : ((a + BitVec.ofNat 64 k) - r.base).toNat ≤ (a - r.base).toNat + k := by bv_omega
  omega

theorem beq_toNat (x y : BitVec 64) : (x == y) = decide (x.toNat = y.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_inj]

/-- ZF after a subtraction, as numbers. -/
theorem sub_beq_zero (x y : BitVec 64) : (x - y == 0) = decide (x.toNat = y.toNat) := by
  rw [beq_toNat, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
  have := x.isLt; have := y.isLt
  by_cases h : x.toNat = y.toNat <;> simp [h] <;> omega

theorem add_ofNat (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem ofNat_sub (n k : Nat) (h : k ≤ n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 k = BitVec.ofNat 64 (n - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The branch conditions this routine tests, as flags. -/
theorem eval_b (s : S) : I.eval (.vg .b) s = s.vg.cf := rfl
theorem eval_ae (s : S) : I.eval (.vg .ae) s = s.vg.cf.map (!·) := rfl
theorem eval_e (s : S) : I.eval (.vg .e) s = s.vg.zf := rfl
theorem eval_ne (s : S) : I.eval (.vg .ne) s = s.vg.zf.map (!·) := rfl

/-- Two blocks run one after the other. -/
theorem execBlock_append_of {a b : List Ins} {s s₁ s₂ : S} {t₁ t₂ : List Leak}
    (h₁ : execBlock I a s = some (s₁, t₁)) (h₂ : execBlock I b s₁ = some (s₂, t₂)) :
    execBlock I (a ++ b) s = some (s₂, t₁ ++ t₂) := by
  rw [execBlock_append, h₁]
  simp [h₂]

/-- A 16-byte block of the AAD as the two words `addBlock` reads. -/
theorem block_val (M : Mem) (ad : Addr) (len j : Nat) (h : 16 * (j + 1) ≤ len) :
    (M.readW (ad + BitVec.ofNat 64 (16 * j)) 64).toNat +
        2 ^ 64 * (M.readW (ad + BitVec.ofNat 64 (16 * j) + 8#64) 64).toNat =
      leNum (((bytesAt M ad len).drop (16 * j)).take 16) := by
  rw [bytesAt_drop _ _ (by omega), bytesAt_take _ _ (by omega),
    show (16 : Nat) = 8 + 8 from rfl, bytesAt_add, leNum_append, bytesAt_length, readW64_toNat, readW64_toNat]
  norm_num

/-- The 13-byte AAD as the two words `load13` makes. -/
theorem fast_val (M : Mem) (ad : Addr) :
    (M.readW ad 64).toNat + 2 ^ 64 * (M.readW (ad + 5#64) 64 >>> 24).toNat = leNum (bytesAt M ad 13) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, readW64_toNat, readW64_toNat,
    show (13 : Nat) = 8 + 5 from rfl, bytesAt_add, leNum_append, bytesAt_length,
    show (8 : Nat) = 3 + 5 from rfl, bytesAt_add (a := ad + 5#64), leNum_append, bytesAt_length,
    add_ofNat]
  have := leNum_lt (bytesAt M (ad + 5#64) 3)
  rw [bytesAt_length] at this
  norm_num at this ⊢
  omega

/-! ## The accumulator -/

/-- A block added to an accumulator below `5 · 2^128`, then times `r`: below
`5 · 2^128` again, and the next accumulator modulo `p`. -/
theorem acc_step (h0 h1 h2 w0 w1 r0 r1 : BitVec 64) (a m : Nat) (hr0 : r0.toNat < 2 ^ 60)
    (hr1 : r1.toNat < 2 ^ 60) (hlt : limbs h0 h1 h2 < 5 * 2 ^ 128) (ha : limbs h0 h1 h2 % p = a % p)
    (hm : w0.toNat + 2 ^ 64 * w1.toNat = m) :
    let o := addT h0 h1 h2 w0 w1
    let o' := mulOut o.1 o.2.1 o.2.2 r0 r1
    limbs o'.1 o'.2.1 o'.2.2 < 5 * 2 ^ 128 ∧
      limbs o'.1 o'.2.1 o'.2.2 % p = (a + m + 2 ^ 128) * (r0.toNat + 2 ^ 64 * r1.toNat) % p := by
  intro o o'
  obtain ⟨e1, b1⟩ := limbs_addT h0 h1 h2 w0 w1 hlt
  have e2 := limbs_mulOut o.1 o.2.1 o.2.2 r0 r1 b1 hr0 hr1
  simp only at e2
  simp only [o', e2]
  have := w0.isLt; have := w1.isLt
  have e3 : limbs o.1 o.2.1 o.2.2 = limbs h0 h1 h2 + m + 2 ^ 128 := by rw [e1]; omega
  rw [e3]
  exact ⟨reduce_lt (by omega) (by omega), reduce_step _ _ _ _ ha⟩

/-! ## What the routine is given -/

/-- The routine's inputs: the AAD, `len` bytes at `ad` in memory `M`, and
`r`'s two words, `r0` and `r1`, at `kp`. -/
structure Ctx where
  M : Mem
  ad : Addr
  kp : Addr
  len : Nat
  r0 : BitVec 64
  r1 : BitVec 64

/-- The AAD. -/
abbrev Ctx.x (c : Ctx) : List (BitVec 8) := bytesAt c.M c.ad c.len

/-- `r`. -/
abbrev Ctx.r (c : Ctx) : Nat := c.r0.toNat + 2 ^ 64 * c.r1.toNat

/-- The registers the routine changes. -/
abbrev clobbers : List Reg := [.rax, .rdx, .rcx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- `s0` holds `c`: its memory, `r` at `kp` with each word below `2^60`, and
the AAD readable if there is any. -/
structure Ctx.Ok (c : Ctx) (s0 : S) : Prop where
  mem : s0.vg.mem = c.M
  key : Key s0 c.kp c.r0 c.r1
  hr0 : c.r0.toNat < 2 ^ 60
  hr1 : c.r1.toNat < 2 ^ 60
  len : c.len < 2 ^ 64
  ad : c.len ≠ 0 → InRegions (s0.vg.rd ++ s0.vg.wr) c.ad c.len

/-- A block that keeps `rbp` and memory keeps `r`. -/
theorem Key.frame {s s' : S} {kp r0 r1 : BitVec 64} {gs : List Reg} (k : Key s kp r0 r1) (f : Frame s s' gs)
    (hg : Reg.rbp ∉ gs) (hm : s'.vg.mem = s.vg.mem) : Key s' kp r0 r1 := by
  obtain ⟨hrbp, h0, h1, m0, m1⟩ := k
  rw [← f.rd, ← f.wr] at h0 h1
  rw [← hm] at m0 m1
  exact ⟨(f.gpr _ hg).trans hrbp, h0, h1, m0, m1⟩

/-- An AAD region of `s0` is one of `s`'s, as `s` keeps `s0`'s. -/
theorem Ctx.Ok.region {c : Ctx} {s0 s : S} (ok : c.Ok s0) {gs : List Reg} (f : Frame s0 s gs)
    (k m : Nat) (hk : k + m ≤ c.len) (hm : 0 < m) : InRegions (s.vg.rd ++ s.vg.wr) (c.ad + BitVec.ofNat 64 k) m := by
  rw [f.rd, f.wr]
  exact InRegions.sub (ok.ad (by omega)) k m hk

/-! ## The block loop -/

/-- After `j` blocks: `rcx` and `r8` at the next, and the accumulator over
the first `j`. -/
structure BInv (c : Ctx) (s0 : S) (j : Nat) (s : S) : Prop where
  rcx : s.vg.gpr .rcx = c.ad + BitVec.ofNat 64 (16 * j)
  r8 : s.vg.gpr .r8 = BitVec.ofNat 64 (c.len - 16 * j)
  le : 16 * j ≤ c.len
  mem : s.vg.mem = c.M
  frame : Frame s0 s clobbers
  lt : limbs (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) < 5 * 2 ^ 128
  acc : limbs (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) % p = padBlocks c.r 0 (c.x.take (16 * j))

/-- Block `j`'s trace: its two words, then `r`'s. -/
def blockTrace (ad kp : Addr) (j : Nat) : List Leak :=
  ([.addr (ad + BitVec.ofNat 64 (16 * j)), .addr (ad + BitVec.ofNat 64 (16 * j) + 8#64)] ++ mulTrace kp) ++ []

set_option maxHeartbeats 1000000 in
/-- One iteration of the block loop: block `j`, then whether another whole block is left. -/
theorem block_step (c : Ctx) (s0 : S) (ok : c.Ok s0) (j : Nat) (s : S) (inv : BInv c s0 j s)
    (hj : 16 * (j + 1) ≤ c.len) :
    ∃ s', Exec I (.block block) s (blockTrace c.ad c.kp j) s' ∧
      I.eval (.vg .ae) s' = some (decide (16 * (j + 1 + 1) ≤ c.len)) ∧ BInv c s0 (j + 1) s' := by
  obtain ⟨hrcx, hr8, hle, hmem, fr, hlt, hacc⟩ := inv
  have key : Key s c.kp c.r0 c.r1 := ok.key.frame fr (by decide) (hmem.trans ok.mem.symm)
  obtain ⟨s₁, x₁, a10, a11, a12, m₁, f₁⟩ := addBlock_ok s _ hrcx
    (by simpa using ok.region fr (16 * j) 8 (by omega) (by omega))
    (by rw [add_ofNat]; exact ok.region fr (16 * j + 8) 8 (by omega) (by omega))
  obtain ⟨s₂, x₂, b10, b11, b12, m₂, f₂⟩ := mul_ok s₁ c.kp c.r0 c.r1 (key.frame f₁ (by decide) m₁)
  obtain ⟨s₃, x₃, c_rcx, c_r8, c_cf, m₃, f₃⟩ := next_ok s₂
  have f₃' : Frame s0 s₃ clobbers :=
    ((fr.trans (f₁.mono (by decide))).trans (f₂.mono (by decide))).trans (f₃.mono (by decide))
  have r8₂ : s₂.vg.gpr .r8 = BitVec.ofNat 64 (c.len - 16 * j) := by
    rw [f₂.gpr _ (by decide), f₁.gpr _ (by decide), hr8]
  have rcx₂ : s₂.vg.gpr .rcx = c.ad + BitVec.ofNat 64 (16 * j) := by
    rw [f₂.gpr _ (by decide), f₁.gpr _ (by decide), hrcx]
  have hsub : BitVec.ofNat 64 (c.len - 16 * j) - 16#64 = BitVec.ofNat 64 (c.len - 16 * (j + 1)) := by
    rw [ofNat_sub _ _ (by omega) (by have := ok.len; omega)]; congr 1
  refine ⟨s₃, Exec.block (execBlock_append_of (execBlock_append_of x₁ x₂) x₃), ?_, ?_⟩
  · rw [eval_ae, c_cf, r8₂, hsub]
    simp only [Option.map_some, BitVec.toNat_ofNat]
    congr 1
    have := ok.len
    rw [Nat.mod_eq_of_lt (by omega)]
    by_cases h : 16 * (j + 1 + 1) ≤ c.len <;> simp [h] <;> omega
  · -- the accumulator
    have hm := block_val c.M c.ad c.len j hj
    rw [hmem] at a10 a11 a12
    obtain ⟨lt', acc'⟩ := acc_step _ _ _ _ _ c.r0 c.r1 (padBlocks c.r 0 (c.x.take (16 * j))) _ ok.hr0 ok.hr1 hlt
      (by rw [hacc, Nat.mod_eq_of_lt (padBlocks_lt _ _ _ _ le_rfl (by unfold p; norm_num))]) hm
    rw [← a10, ← a11, ← a12, ← b10, ← b11, ← b12] at lt' acc'
    have g10 : s₃.vg.gpr .r10 = s₂.vg.gpr .r10 := f₃.gpr _ (by decide)
    have g11 : s₃.vg.gpr .r11 = s₂.vg.gpr .r11 := f₃.gpr _ (by decide)
    have g12 : s₃.vg.gpr .r12 = s₂.vg.gpr .r12 := f₃.gpr _ (by decide)
    refine ⟨?_, ?_, by omega, by rw [m₃, m₂, m₁, hmem], f₃', ?_, ?_⟩
    · rw [c_rcx, rcx₂, add_ofNat, show 16 * (j + 1) = 16 * j + 16 by ring]
    · rw [c_r8, r8₂, hsub]
    · rw [g10, g11, g12]; exact lt'
    · rw [g10, g11, g12, acc', padBlocks_take_succ _ _ _ _ (by rw [bytesAt_length]; omega)]

/-- A comparison keeps the block loop's invariant. -/
theorem BInv.cmp {c : Ctx} {s0 s s' : S} {j : Nat} (inv : BInv c s0 j s) (f : Frame s s' [])
    (hm : s'.vg.mem = s.vg.mem) : BInv c s0 j s' := by
  obtain ⟨hrcx, hr8, hle, hmem, fr, hlt, hacc⟩ := inv
  have g : ∀ r, s'.vg.gpr r = s.vg.gpr r := fun r => f.gpr r (by simp)
  exact ⟨by rw [g, hrcx], by rw [g, hr8], hle, hm.trans hmem, fr.trans (f.mono (by simp)),
    by rw [g, g, g]; exact hlt, by rw [g, g, g]; exact hacc⟩

/-- The block loop's trace: none for fewer than 16 bytes, else each block's. -/
def blocksTrace (ad kp : Addr) (len : Nat) : List Leak :=
  if len < 16 then [.branch true] else .branch false :: loopTrace (blockTrace ad kp) 1 0 (len / 16 - 1)

/-- The block loop, skipped for fewer than 16 bytes, hashes every whole block. -/
theorem blocks_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) (inv : BInv c s0 0 s)
    (hcf : s.vg.cf = some (decide (c.len < 16))) :
    ∃ s', Exec I (.ite (.vg .b) (.block []) (.loop (.block block) (.vg .ae))) s (blocksTrace c.ad c.kp c.len) s' ∧
      BInv c s0 (c.len / 16) s' := by
  by_cases h : c.len < 16
  · refine ⟨s, ?_, by rw [Nat.div_eq_of_lt h]; exact inv⟩
    simp only [blocksTrace, h, ↓reduceIte]
    exact Exec.iteT (by rw [eval_b, hcf]; simp [h]) (Exec.block rfl)
  · obtain ⟨s', x, inv'⟩ := loop_ok (BInv c s0) (fun j => 16 * (j + 1) ≤ c.len)
      (fun j => decide (16 * (j + 1 + 1) ≤ c.len)) (blockTrace c.ad c.kp) 1 (block_step c s0 ok)
      (c.len / 16 - 1) 0 s inv (fun i hi => by omega) (fun i hi => by simp only [decide_eq_true_eq]; omega)
      (by simp only [decide_eq_false_iff_not]; omega)
    refine ⟨s', ?_, by rwa [show 0 + 1 * (c.len / 16 - 1 + 1) = c.len / 16 by omega] at inv'⟩
    simp only [blocksTrace, h, ↓reduceIte]
    exact Exec.iteF (by rw [eval_b, hcf]; simp [h]) x

/-! ## The last, partial block -/

/-- After `k` of the last `rem` bytes, from the last down, since `sb`:
`rcx` past the next, `r8` the bytes left, and `(r13, r14)` the `k` bytes as a
number. -/
structure TInv (c : Ctx) (sb : S) (rem k : Nat) (s : S) : Prop where
  rcx : s.vg.gpr .rcx = c.ad + BitVec.ofNat 64 (c.len - k)
  r8 : s.vg.gpr .r8 = BitVec.ofNat 64 (rem - k)
  le : k ≤ rem
  mem : s.vg.mem = c.M
  frame : Frame sb s [.r13, .r14, .r15, .rcx, .r8]
  val : (s.vg.gpr .r14).toNat * 2 ^ 64 + (s.vg.gpr .r13).toNat =
    leNum (bytesAt c.M (c.ad + BitVec.ofNat 64 (c.len - k)) k)

/-- Byte `k` from the end's trace. -/
def byteTrace (ad : Addr) (len k : Nat) : List Leak := [.addr (ad + BitVec.ofNat 64 (len - (k + 1)))]

theorem one_eq : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl

/-- One iteration of the byte loop: byte `k` from the end, then whether another is left. -/
theorem byte_step (c : Ctx) (s0 sb : S) (ok : c.Ok s0) (fb : Frame s0 sb clobbers) (rem : Nat)
    (hrem : rem ≤ 15) (hrl : rem ≤ c.len) (k : Nat) (s : S) (inv : TInv c sb rem k s) (hk : k < rem) :
    ∃ s', Exec I (.block tailByte) s (byteTrace c.ad c.len k) s' ∧
      I.eval (.vg .ne) s' = some (decide (k + 1 < rem)) ∧ TInv c sb rem (k + 1) s' := by
  obtain ⟨hrcx, hr8, hle, hmem, fr, hval⟩ := inv
  have hl := ok.len
  have ea : c.ad + BitVec.ofNat 64 (c.len - k) - 1#64 = c.ad + BitVec.ofNat 64 (c.len - (k + 1)) := by
    rw [show c.len - k = c.len - (k + 1) + 1 by omega, ← add_ofNat, BitVec.add_sub_cancel]
  obtain ⟨s₁, x₁, a13, a14, arcx, ar8, azf, m₁, f₁⟩ := tailByte_ok s _ hrcx
    (by rw [ea]; exact ok.region (fb.trans (fr.mono (by decide))) _ 1 (by omega) (by omega))
  rw [ea] at x₁ a13 a14 arcx
  refine ⟨s₁, Exec.block x₁, ?_, ?_⟩
  · rw [eval_ne, azf, hr8, sub_beq_zero]
    simp only [Option.map_some, BitVec.toNat_ofNat]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
    by_cases h : k + 1 < rem <;> simp [h] <;> omega
  · refine ⟨arcx, ?_, by omega, by rw [m₁, hmem], fr.trans f₁, ?_⟩
    · rw [ar8, hr8, ofNat_sub _ _ (by omega) (by omega)]; congr 1
    · have hb : (s.vg.gpr .r14).toNat * 2 ^ 64 + (s.vg.gpr .r13).toNat < 2 ^ 120 := by
        rw [hval]
        have := leNum_lt (bytesAt c.M (c.ad + BitVec.ofNat 64 (c.len - k)) k)
        rw [bytesAt_length] at this
        calc _ < 256 ^ k := this
          _ ≤ 256 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ < 2 ^ 120 := by norm_num
      have e := tailStep_toNat (s.vg.gpr .r13) (s.vg.gpr .r14) (s.vg.mem (c.ad + BitVec.ofNat 64 (c.len - (k + 1)))) hb
      simp only at e
      rw [a13, a14, e, hval, bytesAt_succ, leNum_cons, one_eq, add_ofNat,
        show c.len - (k + 1) + 1 = c.len - k by omega, hmem]
      ring

/-- The partial block's trace: none for a whole number of blocks, else each
byte's, then `r`'s. -/
def tailTrace (ad kp : Addr) (len : Nat) : List Leak :=
  if len % 16 = 0 then [.branch true] else
    .branch false :: ([] ++ (loopTrace (byteTrace ad len) 1 0 (len % 16 - 1) ++ ([] ++ mulTrace kp)))

/-- What the routine leaves: the accumulator over the AAD. -/
structure Done (c : Ctx) (s0 s : S) : Prop where
  lt : limbs (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) < 5 * 2 ^ 128
  acc : limbs (s.vg.gpr .r10) (s.vg.gpr .r11) (s.vg.gpr .r12) % p = padBlocks c.r 0 c.x
  mem : s.vg.mem = c.M
  frame : Frame s0 s clobbers

set_option maxHeartbeats 1000000 in
/-- The partial block, if any, completes the hash. -/
theorem tail_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) (inv : BInv c s0 (c.len / 16) s)
    (hzf : s.vg.zf = some (decide (c.len % 16 = 0))) :
    ∃ s', Exec I (.ite (.vg .e) (.block []) (.seq (.block tailInit) (.seq (.loop (.block tailByte) (.vg .ne))
      (.block tailHash)))) s (tailTrace c.ad c.kp c.len) s' ∧ Done c s0 s' := by
  obtain ⟨hrcx, hr8, hle, hmem, fr, hlt, hacc⟩ := inv
  have hl := ok.len
  have hx : c.x.length = c.len := bytesAt_length _ _ _
  by_cases h : c.len % 16 = 0
  · refine ⟨s, ?_, hlt, ?_, hmem, fr⟩
    · simp only [tailTrace, h, ↓reduceIte]
      exact Exec.iteT (by rw [eval_e, hzf]; simp [h]) (Exec.block rfl)
    · rw [hacc, padBlocks_whole c.r 0 c.x (by rw [hx]; exact h), hx]
  · -- `tailInit`, the bytes, then `tailHash`
    obtain ⟨s₁, x₁, a13, a14, arcx, m₁, f₁⟩ := tailInit_ok s
    have fb : Frame s0 s₁ clobbers := fr.trans (f₁.mono (by decide))
    have hq : 16 * (c.len / 16) + c.len % 16 = c.len := Nat.div_add_mod _ _
    have inv₀ : TInv c s₁ (c.len % 16) 0 s₁ := by
      refine ⟨?_, ?_, by omega, by rw [m₁, hmem], Frame.refl _ _, ?_⟩
      · rw [arcx, hrcx, hr8, add_ofNat]; congr 2; omega
      · rw [f₁.gpr _ (by decide), hr8]; congr 1; omega
      · rw [a13, a14]; simp [bytesAt, leNum]
    obtain ⟨s₂, x₂, inv₂⟩ := loop_ok (TInv c s₁ (c.len % 16)) (fun k => k < c.len % 16)
      (fun k => decide (k + 1 < c.len % 16)) (byteTrace c.ad c.len) 1
      (byte_step c s0 s₁ ok fb (c.len % 16) (by omega) (by omega))
      (c.len % 16 - 1) 0 s₁ inv₀ (fun i hi => by omega)
      (fun i hi => by simp only [decide_eq_true_eq]; omega) (by simp only [decide_eq_false_iff_not]; omega)
    rw [show 0 + 1 * (c.len % 16 - 1 + 1) = c.len % 16 by omega] at inv₂
    obtain ⟨-, -, -, hmem₂, fr₂, hval⟩ := inv₂
    obtain ⟨s₃, x₃, b10, b11, b12, m₃, f₃⟩ := addTail_ok s₂
    have key : Key s₃ c.kp c.r0 c.r1 :=
      ok.key.frame ((fb.trans (fr₂.mono (by decide))).trans (f₃.mono (by decide))) (by decide)
        (by rw [m₃, hmem₂, ok.mem])
    obtain ⟨s₄, x₄, c10, c11, c12, m₄, f₄⟩ := mul_ok s₃ c.kp c.r0 c.r1 key
    have g : ∀ r ∈ [Reg.r10, Reg.r11, Reg.r12], s₂.vg.gpr r = s.vg.gpr r := by
      intro r hr
      rw [fr₂.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide),
        f₁.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)]
    rw [g _ (by simp), g _ (by simp), g _ (by simp)] at b10 b11 b12
    have hm : (s₂.vg.gpr .r13).toNat + 2 ^ 64 * (s₂.vg.gpr .r14).toNat =
        leNum (bytesAt c.M (c.ad + BitVec.ofNat 64 (16 * (c.len / 16))) (c.len % 16)) := by
      rw [show 16 * (c.len / 16) = c.len - c.len % 16 by omega, ← hval]; ring
    obtain ⟨lt', acc'⟩ := acc_step _ _ _ _ _ c.r0 c.r1 (padBlocks c.r 0 (c.x.take (16 * (c.len / 16)))) _
      ok.hr0 ok.hr1 hlt (by rw [hacc, Nat.mod_eq_of_lt (padBlocks_lt _ _ _ _ le_rfl (by unfold p; norm_num))]) hm
    rw [← b10, ← b11, ← b12, ← c10, ← c11, ← c12] at lt' acc'
    refine ⟨s₄, ?_, lt', ?_, by rw [m₄, m₃, hmem₂], ?_⟩
    · simp only [tailTrace, h, ↓reduceIte]
      exact Exec.iteF (by rw [eval_e, hzf]; simp [h])
        (Exec.seq (Exec.block x₁) (Exec.seq x₂ (Exec.block (execBlock_append_of x₃ x₄))))
    · rw [acc', padBlocks_partial c.r 0 c.x (by rw [hx]; exact h), hx, bytesAt_drop _ _ (by omega),
        show c.len - 16 * (c.len / 16) = c.len % 16 by omega]
    · exact ((fb.trans (fr₂.mono (by decide))).trans (f₃.mono (by decide))).trans (f₄.mono (by decide))

/-! ## Any AAD but 13 bytes -/

/-- The trace of any AAD but 13 bytes. -/
def generalTrace (ad kp : Addr) (len : Nat) : List Leak :=
  [] ++ (blocksTrace ad kp len ++ ([] ++ tailTrace ad kp len))

/-- Any AAD but 13 bytes: the whole blocks, then the partial one. -/
theorem general_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) (inv : BInv c s0 0 s) :
    ∃ s', Exec I general s (generalTrace c.ad c.kp c.len) s' ∧ Done c s0 s' := by
  have hl := ok.len
  obtain ⟨s₁, x₁, -, a_cf, m₁, f₁⟩ := cmp_ok s 16
  have inv₁ := inv.cmp f₁ m₁
  have r8 : s.vg.gpr .r8 = BitVec.ofNat 64 c.len := by rw [inv.r8]; rfl
  obtain ⟨s₂, x₂, inv₂⟩ := blocks_ok c s0 s₁ ok inv₁ (by
    rw [a_cf, r8, sx16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]; rfl)
  obtain ⟨s₃, x₃, a_zf, -, m₃, f₃⟩ := cmp_ok s₂ 0
  have inv₃ := inv₂.cmp f₃ m₃
  obtain ⟨s₄, x₄, done⟩ := tail_ok c s0 s₃ ok inv₃ (by
    rw [a_zf, inv₂.r8, sub_beq_zero]
    simp only [signExtend_zero', BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
    by_cases h : c.len % 16 = 0 <;> simp [h] <;> omega)
  exact ⟨s₄, Exec.seq (Exec.block x₁) (Exec.seq x₂ (Exec.seq (Exec.block x₃) x₄)), done⟩

/-! ## The routine -/

/-- The routine's trace, of the AAD's address and length and `r`'s address. -/
def traceOf (ad kp : Addr) (len : Nat) : List Leak :=
  [] ++ (if len = 13 then .branch false :: ([.addr ad, .addr (ad + 5#64)] ++ mulTrace kp)
    else .branch true :: generalTrace ad kp len)

set_option maxHeartbeats 1000000 in
/-- The routine hashes the AAD `c` gives, its trace a function of `c`'s addresses and length. -/
theorem run (c : Ctx) (s0 : S) (ok : c.Ok s0) (hrcx : s0.vg.gpr .rcx = c.ad)
    (hr8 : s0.vg.gpr .r8 = BitVec.ofNat 64 c.len) :
    ∃ s', Exec I prog s0 (traceOf c.ad c.kp c.len) s' ∧ Done c s0 s' := by
  have hl := ok.len
  obtain ⟨s₁, x₁, a10, a11, a12, a_zf, m₁, f₁⟩ := init_ok s0
  have f₁' : Frame s0 s₁ clobbers := f₁.mono (by decide)
  have hzf : s₁.vg.zf = some (decide (c.len = 13)) := by
    rw [a_zf, hr8, sub_beq_zero]
    simp only [BitVec.toNat_ofNat]
    congr 1
    rw [Nat.mod_eq_of_lt hl]
  have zero : ∀ r ∈ [Reg.r10, Reg.r11, Reg.r12], s₁.vg.gpr r = 0 := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> assumption
  by_cases h : c.len = 13
  · -- 13 bytes: `load13`, then `mul`
    have rcx₁ : s₁.vg.gpr .rcx = c.ad := (f₁.gpr _ (by decide)).trans hrcx
    obtain ⟨s₂, x₂, b10, b11, b12, m₂, f₂⟩ := load13_ok s₁ c.ad rcx₁
      (by simpa using ok.region f₁' 0 8 (by omega) (by omega))
      (ok.region f₁' 5 8 (by omega) (by omega))
    have key : Key s₂ c.kp c.r0 c.r1 :=
      ok.key.frame (f₁'.trans (f₂.mono (by decide))) (by decide) (by rw [m₂, m₁])
    obtain ⟨s₃, x₃, c10, c11, c12, m₃, f₃⟩ := mul_ok s₂ c.kp c.r0 c.r1 key
    refine ⟨s₃, ?_, ?_⟩
    · simp only [traceOf, h, ↓reduceIte]
      exact Exec.seq (Exec.block x₁) (Exec.iteF (by rw [eval_ne, hzf]; simp [h])
        (Exec.block (execBlock_append_of x₂ x₃)))
    · rw [m₁, ok.mem] at b10 b11
      have hv := fast_val c.M c.ad
      rw [← b10, ← b11] at hv
      have hx : c.x = bytesAt c.M c.ad 13 := by rw [Ctx.x, h]
      have hb := leNum_lt (bytesAt c.M c.ad 13)
      rw [bytesAt_length] at hb
      have h2 : (s₂.vg.gpr .r12).toNat < 7 := by rw [b12]; decide
      have e := limbs_mulOut (s₂.vg.gpr .r10) (s₂.vg.gpr .r11) _ c.r0 c.r1 h2 ok.hr0 ok.hr1
      simp only [← c10, ← c11, ← c12] at e
      have el : limbs (s₂.vg.gpr .r10) (s₂.vg.gpr .r11) (s₂.vg.gpr .r12) = 0 + leNum c.x + 2 ^ 128 := by
        unfold limbs; rw [b12, hx, ← hv]; simp only [show (1#64 : BitVec 64).toNat = 1 from rfl]; ring
      refine ⟨?_, ?_, by rw [m₃, m₂, m₁, ok.mem], f₁'.trans ((f₂.mono (by decide)).trans (f₃.mono (by decide)))⟩
      · rw [e, el]; exact reduce_lt (by rw [hx]; norm_num at hb ⊢; omega) (by have := ok.hr0; have := ok.hr1; omega)
      · rw [e, el, reduce_step 0 0 _ _ rfl, padBlocks_block _ _ (by rw [hx]; simp [bytesAt])
          (by rw [bytesAt_length]; omega)]
  · -- any other length
    have inv : BInv c s0 0 s₁ := by
      refine ⟨?_, ?_, by omega, by rw [m₁, ok.mem], f₁', ?_, ?_⟩
      · rw [f₁.gpr _ (by decide), hrcx]; simp
      · rw [f₁.gpr _ (by decide), hr8]; rfl
      · rw [a10, a11, a12]; unfold limbs; simp
      · rw [a10, a11, a12]; unfold limbs; simp
    obtain ⟨s₂, x₂, done⟩ := general_ok c s0 s₁ ok inv
    refine ⟨s₂, ?_, done⟩
    simp only [traceOf, h, ↓reduceIte]
    exact Exec.seq (Exec.block x₁) (Exec.iteT (by rw [eval_ne, hzf]; simp [h]) x₂)

/-! ## The contract -/

/-- The AAD's length. -/
abbrev len (s : S) : Nat := (s.vg.gpr .r8).toNat

/-- What the routine is given in `s`. -/
def ctxOf (s : S) : Ctx :=
  ⟨s.vg.mem, s.vg.gpr .rcx, s.vg.gpr .rbp, len s, s.vg.mem.readW (s.vg.gpr .rbp) 64,
    s.vg.mem.readW (s.vg.gpr .rbp + 8#64) 64⟩

/-- `rcx` points to `r8` bytes of AAD, readable if there are any, and `rbp`
to `r`'s two words, each below `2^60` as RFC 8439's clamp leaves them, as
aws-lc's seal and open call it. -/
structure Pre (s : S) : Prop where
  ad : len s ≠ 0 → InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .rcx) (len s)
  key : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .rbp) 16
  r0 : (s.vg.mem.readW (s.vg.gpr .rbp) 64).toNat < 2 ^ 60
  r1 : (s.vg.mem.readW (s.vg.gpr .rbp + 8#64) 64).toNat < 2 ^ 60

/-- The accumulator in `(r10, r11, r12)`, below `5 · 2^128`, is, modulo `p`,
RFC 8439's with the `r` at `rbp` over the AAD zero-padded to whole blocks,
which is the RFC's own when that `r` is clamped, as seal's and open's is.
Memory and every register but the accumulator's and the scratch ones stay
as they were. -/
structure Post (s s' : S) : Prop where
  acc : limbs (s'.vg.gpr .r10) (s'.vg.gpr .r11) (s'.vg.gpr .r12) % p =
    padBlocks (ctxOf s).r 0 (ctxOf s).x
  lt : limbs (s'.vg.gpr .r10) (s'.vg.gpr .r11) (s'.vg.gpr .r12) < 5 * 2 ^ 128
  mem : s'.vg.mem = s.vg.mem
  frame : Frame s s' clobbers

/-- What is public: the AAD's address and length, and `r`'s address. The
AAD's and `r`'s values are not. -/
def Pub (s₁ s₂ : S) : Prop :=
  s₁.vg.gpr .rcx = s₂.vg.gpr .rcx ∧ s₁.vg.gpr .r8 = s₂.vg.gpr .r8 ∧ s₁.vg.gpr .rbp = s₂.vg.gpr .rbp

/-- The routine's trace from `s`, a function of what is public. -/
def trace (s : S) : List Leak := traceOf (s.vg.gpr .rcx) (s.vg.gpr .rbp) (len s)

/-- From `Pre`, the routine runs with `trace` to a state `Post` holds of. -/
theorem correct (s : S) (h : Pre s) : ∃ s', Exec I prog s (trace s) s' ∧ Post s s' := by
  obtain ⟨had, hkey, hr0, hr1⟩ := h
  have ok : (ctxOf s).Ok s :=
    ⟨rfl, ⟨rfl, by simpa [ctxOf] using InRegions.sub hkey 0 8 (by omega), InRegions.sub hkey 8 8 (by omega), rfl, rfl⟩,
      hr0, hr1, (s.vg.gpr .r8).isLt, had⟩
  obtain ⟨s', x, done⟩ := run (ctxOf s) s ok rfl (by simp [ctxOf])
  exact ⟨s', x, done.acc, done.lt, done.mem, done.frame⟩

/-- Runs from states that agree on what is public leave the same trace. -/
theorem constant_time : ConstantTime I Pre Pub prog := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨e0, e1, e2⟩ x₁ x₂
  obtain ⟨_, y₁, -⟩ := correct s₁ h₁
  obtain ⟨_, y₂, -⟩ := correct s₂ h₂
  rw [(exec_det x₁ y₁).1, (exec_det x₂ y₂).1]
  simp only [trace, len, e0, e1, e2]

/-! ## The precondition holds of some state -/

/-- A state the precondition holds of: no AAD, and `r` zero at `0x1000`. -/
def witness : S where
  vg := { gpr := fun r => if r = .rbp then 0x1000#64 else 0,
          cf := none, zf := none, sf := none, of := none,
          mem := fun _ => 0,
          rd := [⟨0x1000#64, 16⟩],
          wr := [] }
  lo := 0

theorem pre_witness : Pre witness := by
  refine ⟨fun h => absurd rfl h, ⟨⟨0x1000#64, 16⟩, by simp [witness], by decide⟩, ?_, ?_⟩ <;>
    rw [readW64_toNat] <;> simp [witness, bytesAt, leNum, Nat.ofDigits]

/-- The routine hashes the AAD into the accumulator, keeping memory and every
register but its scratch ones; its trace depends only on the AAD's address
and length and `r`'s address; and some state meets its precondition. -/
theorem poly_hash_ad_internal_correct :
    (∀ s, Pre s → ∃ t s', Exec I prog s t s' ∧ Post s s') ∧ ConstantTime I Pre Pub prog ∧ ∃ s, Pre s :=
  ⟨fun s h => let ⟨s', e, p⟩ := correct s h; ⟨_, s', e, p⟩, constant_time, _, pre_witness⟩

end rind.x86_64.polyhashad

/-- info: 'rind.x86_64.polyhashad.poly_hash_ad_internal_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.polyhashad.poly_hash_ad_internal_correct
