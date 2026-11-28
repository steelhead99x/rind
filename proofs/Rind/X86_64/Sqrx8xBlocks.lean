import Rind.X86_64.Sqrx8xRow

/-! # bn_sqrx8x_internal's outer pass, block by block

The blocks around the inner loop: `pre` loads a row's accumulator, `innerEnd` steps to the next column block,
`reload` adds `t`'s next eight words into the accumulator, `brk` folds in the last carry, and `spill` stores the
accumulator and loads the next row's. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 4096

namespace rind.x86_64.sqrx8x

/-- `neg` of a mask sets the carry of its bit. -/
theorem neg_mask_ne (c : Bool) : decide (0 - (BitVec.ofBool c).setWidth 64 ≠ 0) = c := by cases c <;> decide

/-- Zero less a mask borrows its bit. -/
theorem sub_mask_borrow (c : Bool) :
    decide ((0 : BitVec 64).toNat < (0 - (BitVec.ofBool c).setWidth 64).toNat) = c := by cases c <;> decide

theorem sub_mask_borrow' (c : Bool) :
    decide ((0#64).toNat < (0 - (BitVec.ofBool c).setWidth 64).toNat) = c := by cases c <;> decide

theorem neg_neg' (x : BitVec 64) : 0 - (0 - x) = x := by bv_omega

theorem signExtend_m8 : BitVec.signExtend 64 (-8 : BitVec 32) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide

def preTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa fp (16 * R + 15)), .addr (wa fp (16 * R + 16)), .addr (wa fp (16 * R + 17)),
   .addr (wa fp (16 * R + 18)), .addr (wa fp (16 * R + 19)), .addr (wa fp (16 * R + 20)),
   .addr (wa fp (16 * R + 21)), .addr (wa fp (16 * R + 22)), .addr (wa ap (8 * R)), .addr (wa fp 3),
   .addr (wa fp 4)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `pre` from row block `R`: the accumulator `r8..r15` is `t`'s words `16R + 8` on, plus `r9..r14` and the
mask's carry; its carry out is the mask in slot 3. -/
theorem pre_ok (s : S) (k R : Nat) (ap np fp : Addr) (a u : Nat → BitVec 64) (mc : Bool)
    (hR : 8 * R + 16 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R + 8)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7))
    (hrsp : s.vg.gpr .rsp = fp) (hrbp : s.vg.gpr .rbp = 0)
    (hrcx : s.vg.gpr .rcx = 0 - (BitVec.ofBool mc).setWidth 64)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i)
    (hu : ∀ p, 16 * R + 15 ≤ p → p < 16 * R + 23 → s.vg.mem.readW (wa fp p) 64 = u p) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.pre s = some (s', preTrace ap fp R) ∧
      ∃ c : Bool,
      s'.vg.mem = (s.vg.mem.writeW (wa fp 3) (0 - (BitVec.ofBool c).setWidth 64)).writeW (wa fp 4)
        (wa fp (16 * R + 23)) ∧
      s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8) ∧
      s'.vg.gpr .rbp = wa ap (8 * R + 8) ∧
      s'.vg.gpr .rdi = wa fp (16 * R + 23) ∧
      s'.vg.gpr .rdx = a (8 * R) ∧
      s'.vg.gpr .rax = 0 ∧
      s'.vg.gpr .r8 = u (16 * R + 15) ∧
      s'.vg.cf = some false ∧
      s'.vg.of = some false ∧
      (s'.vg.gpr .r9).toNat + (s'.vg.gpr .r10).toNat * 2 ^ 64 + (s'.vg.gpr .r11).toNat * 2 ^ 128 +
        (s'.vg.gpr .r12).toNat * 2 ^ 192 + (s'.vg.gpr .r13).toNat * 2 ^ 256 + (s'.vg.gpr .r14).toNat * 2 ^ 320 +
        (s'.vg.gpr .r15).toNat * 2 ^ 384 + c.toNat * 2 ^ 448 =
        (s.vg.gpr .r9).toNat + (s.vg.gpr .r10).toNat * 2 ^ 64 + (s.vg.gpr .r11).toNat * 2 ^ 128 +
        (s.vg.gpr .r12).toNat * 2 ^ 192 + (s.vg.gpr .r13).toNat * 2 ^ 256 + (s.vg.gpr .r14).toNat * 2 ^ 320 +
        mc.toNat + (u (16 * R + 16)).toNat + (u (16 * R + 17)).toNat * 2 ^ 64 +
        (u (16 * R + 18)).toNat * 2 ^ 128 + (u (16 * R + 19)).toNat * 2 ^ 192 +
        (u (16 * R + 20)).toNat * 2 ^ 256 + (u (16 * R + 21)).toNat * 2 ^ 320 +
        (u (16 * R + 22)).toNat * 2 ^ 384 ∧
      Frame s s' [.rax, .rcx, .rdx, .rbp, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.pre, hrsi, hrdi, hrsp, hrbp, hrcx, hA, hu, ↓BitVec.ofNat_add_ofNat, ofNat_idx,
    BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub, neg_mask_ne,
    sub_mask_borrow, sub_mask_borrow', neg_neg', signExtend_m8]
  all_goals first | decide | acct | (simp only [wa, Nat.add_assoc])

def innerEndTrace (fp : Addr) : List Leak := [.addr (wa fp 2)]

set_option maxHeartbeats 4000000 in
/-- `innerEnd` after column block `J`: `rbp` at the next, `rcx` back to `-8`, and `zf` whether that is the end
of `a`, slot 2. -/
theorem innerEnd_ok (s : S) (k J : Nat) (ap np fp : Addr) (hJ : 8 * J + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrbp : s.vg.gpr .rbp = wa ap (8 * J)) (hrsp : s.vg.gpr .rsp = fp) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.innerEnd s = some (s', innerEndTrace fp) ∧
      s'.vg.mem = s.vg.mem ∧
      s'.vg.gpr .rbp = wa ap (8 * J + 8) ∧
      s'.vg.gpr .rcx = BitVec.ofNat 64 (2 ^ 64 - 8) ∧
      s'.vg.zf = some (wa ap (8 * J + 8) - s.vg.mem.readW (wa fp 2) 64 == 0) ∧
      Frame s s' [.rcx, .rbp] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.innerEnd, hrbp, hrsp, ↓BitVec.ofNat_add_ofNat, ofNat_idx, signExtend_m8]
  all_goals first | decide | acct | (simp only [wa, Nat.add_assoc])

def reloadTrace (ap fp : Addr) (R J : Nat) : List Leak :=
  [.addr (wa fp 3), .addr (wa ap (8 * R)), .addr (wa fp (8 * R + 8 * J + 7)), .addr (wa fp (8 * R + 8 * J + 8)),
   .addr (wa fp (8 * R + 8 * J + 9)), .addr (wa fp (8 * R + 8 * J + 10)), .addr (wa fp (8 * R + 8 * J + 11)),
   .addr (wa fp (8 * R + 8 * J + 12)), .addr (wa fp (8 * R + 8 * J + 13)), .addr (wa fp (8 * R + 8 * J + 14)),
   .addr (wa fp 3)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `reload` before column block `J`: adds `t`'s words `8R + 8J` on, and the carry slot 3's mask holds, into the
accumulator, its carry out the new mask. -/
theorem reload_ok (s : S) (k R J : Nat) (ap np fp : Addr) (a v : Nat → BitVec 64) (c : Bool)
    (hRJ : R < J) (hJ : 8 * J + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R + 8)) (hrdi : s.vg.gpr .rdi = wa fp (8 * R + 8 * J + 7))
    (hrsp : s.vg.gpr .rsp = fp) (hrbx : s.vg.gpr .rbx = 0)
    (hs3 : s.vg.mem.readW (wa fp 3) 64 = 0 - (BitVec.ofBool c).setWidth 64)
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i)
    (hv : ∀ p, 8 * R + 8 * J + 7 ≤ p → p < 8 * R + 8 * J + 15 → s.vg.mem.readW (wa fp p) 64 = v p) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.reload s = some (s', reloadTrace ap fp R J) ∧
      ∃ c' : Bool,
      s'.vg.mem = s.vg.mem.writeW (wa fp 3) (0 - (BitVec.ofBool c').setWidth 64) ∧
      s'.vg.gpr .rdi = wa fp (8 * R + 8 * J + 15) ∧
      s'.vg.gpr .rdx = a (8 * R) ∧
      s'.vg.gpr .rbx = 0 ∧
      s'.vg.cf = some false ∧
      s'.vg.of = some false ∧
      (s'.vg.gpr .r8).toNat + (s'.vg.gpr .r9).toNat * 2 ^ 64 + (s'.vg.gpr .r10).toNat * 2 ^ 128 +
        (s'.vg.gpr .r11).toNat * 2 ^ 192 + (s'.vg.gpr .r12).toNat * 2 ^ 256 + (s'.vg.gpr .r13).toNat * 2 ^ 320 +
        (s'.vg.gpr .r14).toNat * 2 ^ 384 + (s'.vg.gpr .r15).toNat * 2 ^ 448 + c'.toNat * 2 ^ 512 =
        (s.vg.gpr .r8).toNat + (s.vg.gpr .r9).toNat * 2 ^ 64 + (s.vg.gpr .r10).toNat * 2 ^ 128 +
        (s.vg.gpr .r11).toNat * 2 ^ 192 + (s.vg.gpr .r12).toNat * 2 ^ 256 + (s.vg.gpr .r13).toNat * 2 ^ 320 +
        (s.vg.gpr .r14).toNat * 2 ^ 384 + (s.vg.gpr .r15).toNat * 2 ^ 448 + (v (8 * R + 8 * J + 7)).toNat + (v (8 * R + 8 * J + 8)).toNat * 2 ^ 64 +
        (v (8 * R + 8 * J + 9)).toNat * 2 ^ 128 + (v (8 * R + 8 * J + 10)).toNat * 2 ^ 192 +
        (v (8 * R + 8 * J + 11)).toNat * 2 ^ 256 + (v (8 * R + 8 * J + 12)).toNat * 2 ^ 320 +
        (v (8 * R + 8 * J + 13)).toNat * 2 ^ 384 + (v (8 * R + 8 * J + 14)).toNat * 2 ^ 448 + c.toNat ∧
      Frame s s' [.rax, .rbx, .rdx, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.reload, hrsi, hrdi, hrsp, hrbx, hs3, hA, hv, ↓BitVec.ofNat_add_ofNat,
    ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub, neg_mask_ne,
    sub_mask_borrow, sub_mask_borrow', neg_neg', signExtend_m8]
  all_goals first | decide | acct | (simp only [wa, Nat.add_assoc])

/-- The carry out of adding `c` into the words `xs`, least significant first. -/
def chainC : List (BitVec 64) → Bool → Bool
  | [], c => c
  | x :: xs, c => chainC xs (adcC x 0 c)

/-- Comparing two words of the frame, the first at or past the second, below `2^63`, neither borrows nor
overflows. -/
theorem frame_cmp_cf (fp : Addr) (p q : Nat) (h : fp.toNat + 8 * (p + 1) ≤ 2 ^ 63) (hq : q ≤ p) :
    decide ((wa fp p).toNat < (wa fp q).toNat) = false := by
  simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

theorem frame_cmp_of (fp : Addr) (p q : Nat) (h : fp.toNat + 8 * (p + 1) ≤ 2 ^ 63) (hq : q ≤ p) :
    subOverflow (wa fp p) (wa fp q) (wa fp p - wa fp q) = false := by
  have m : ∀ x : BitVec 64, x.toNat < 2 ^ 63 → x.msb = false := fun x hx => by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  have e1 : (wa fp p).toNat = fp.toNat + 8 * p := by
    simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have e2 : (wa fp q).toNat = fp.toNat + 8 * q := by
    simp only [wa, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have h1 := m _ (by omega : (wa fp p).toNat < 2 ^ 63)
  have h2 := m _ (by omega : (wa fp q).toNat < 2 ^ 63)
  unfold subOverflow
  rw [h1, h2]
  rfl

def brkTrace (ap fp : Addr) (R k : Nat) : List Leak :=
  [.addr (wa fp 3), .addr (wa fp 4), .addr (wa ap (8 * R + 8)), .addr (wa fp (8 * R + k + 7))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `brk` after a row's last column block: adds slot 3's carry into the accumulator, at `t`'s word `8R + k`,
stores its low word there, and compares that with slot 4, the next row's start. -/
theorem brk_ok (s : S) (k R : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (c : Bool)
    (hR : 8 * R + 16 ≤ k) (ar : Arr s k ap np fp) (h63 : fp.toNat + 8 * (2 * k + 9) ≤ 2 ^ 63)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R + 8)) (hrdi : s.vg.gpr .rdi = wa fp (8 * R + k + 7))
    (hrsp : s.vg.gpr .rsp = fp) (hrbx : s.vg.gpr .rbx = 0)
    (hs3 : s.vg.mem.readW (wa fp 3) 64 = 0 - (BitVec.ofBool c).setWidth 64)
    (hs4 : s.vg.mem.readW (wa fp 4) 64 = wa fp (16 * R + 23))
    (hA : ∀ i < k, s.vg.mem.readW (wa ap i) 64 = a i) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.brk s = some (s', brkTrace ap fp R k) ∧
      s'.vg.mem = s.vg.mem.writeW (wa fp (8 * R + k + 7)) (s'.vg.gpr .r8) ∧
      s'.vg.gpr .rbp = 0 ∧
      s'.vg.gpr .rcx = wa fp (16 * R + 23) ∧
      s'.vg.gpr .rdx = a (8 * R + 8) ∧
      s'.vg.cf = some false ∧
      s'.vg.of = some false ∧
      s'.vg.zf = some (wa fp (8 * R + k + 7) - wa fp (16 * R + 23) == 0) ∧
      (s'.vg.gpr .r8).toNat + (s'.vg.gpr .r9).toNat * 2 ^ 64 + (s'.vg.gpr .r10).toNat * 2 ^ 128 +
        (s'.vg.gpr .r11).toNat * 2 ^ 192 + (s'.vg.gpr .r12).toNat * 2 ^ 256 + (s'.vg.gpr .r13).toNat * 2 ^ 320 +
        (s'.vg.gpr .r14).toNat * 2 ^ 384 + (s'.vg.gpr .r15).toNat * 2 ^ 448 + (chainC (accR s) c).toNat * 2 ^ 512 =
        (s.vg.gpr .r8).toNat + (s.vg.gpr .r9).toNat * 2 ^ 64 + (s.vg.gpr .r10).toNat * 2 ^ 128 +
        (s.vg.gpr .r11).toNat * 2 ^ 192 + (s.vg.gpr .r12).toNat * 2 ^ 256 + (s.vg.gpr .r13).toNat * 2 ^ 320 +
        (s.vg.gpr .r14).toNat * 2 ^ 384 + (s.vg.gpr .r15).toNat * 2 ^ 448 + c.toNat ∧
      Frame s s' [.rbx, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.brk, hrsi, hrdi, hrsp, hrbx, hs3, hs4, hA, ↓BitVec.ofNat_add_ofNat, ofNat_idx,
    BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub, neg_mask_ne, sub_mask_borrow, sub_mask_borrow', neg_neg']
  all_goals try (simp (disch := omega) only [frame_cmp_cf, frame_cmp_of]; done)
  all_goals try (simp only [wa, Nat.add_assoc]; done)
  all_goals try decide
  all_goals simp only [chainC, accR]
  all_goals acct

def spillTrace (fp : Addr) (R k : Nat) : List Leak :=
  [.addr (wa fp (8 * R + k + 8)), .addr (wa fp (16 * R + 24)), .addr (wa fp (8 * R + k + 9)),
   .addr (wa fp (16 * R + 25)), .addr (wa fp (8 * R + k + 10)), .addr (wa fp (16 * R + 26)),
   .addr (wa fp (8 * R + k + 11)), .addr (wa fp (16 * R + 27)), .addr (wa fp (8 * R + k + 12)),
   .addr (wa fp (16 * R + 28)), .addr (wa fp (8 * R + k + 13)), .addr (wa fp (16 * R + 29)),
   .addr (wa fp (8 * R + k + 14)), .addr (wa fp (16 * R + 30))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `spill` when the row ended past the next's start: stores `r9..r15` after `t`'s word `8R + k`, and loads
them from the next row's words `16R + 17` on. -/
theorem spill_ok (s : S) (k R : Nat) (ap np fp : Addr) (v : Nat → BitVec 64)
    (hR : 16 * R + 24 ≤ 8 * R + k) (ar : Arr s k ap np fp)
    (hrdi : s.vg.gpr .rdi = wa fp (8 * R + k + 7)) (hrcx : s.vg.gpr .rcx = wa fp (16 * R + 23))
    (hv : ∀ p, 16 * R + 24 ≤ p → p < 16 * R + 31 → s.vg.mem.readW (wa fp p) 64 = v p) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.spill s = some (s', spillTrace fp R k) ∧
      s'.vg.mem = ((((((s.vg.mem.writeW (wa fp (8 * R + k + 8)) (s.vg.gpr .r9)).writeW (wa fp (8 * R + k + 9))
        (s.vg.gpr .r10)).writeW (wa fp (8 * R + k + 10)) (s.vg.gpr .r11)).writeW (wa fp (8 * R + k + 11))
        (s.vg.gpr .r12)).writeW (wa fp (8 * R + k + 12)) (s.vg.gpr .r13)).writeW (wa fp (8 * R + k + 13))
        (s.vg.gpr .r14)).writeW (wa fp (8 * R + k + 14)) (s.vg.gpr .r15) ∧
      s'.vg.gpr .rdi = wa fp (16 * R + 23) ∧
      s'.vg.gpr .r9 = v (16 * R + 24) ∧ s'.vg.gpr .r10 = v (16 * R + 25) ∧ s'.vg.gpr .r11 = v (16 * R + 26) ∧
      s'.vg.gpr .r12 = v (16 * R + 27) ∧ s'.vg.gpr .r13 = v (16 * R + 28) ∧ s'.vg.gpr .r14 = v (16 * R + 29) ∧
      s'.vg.gpr .r15 = v (16 * R + 30) ∧ s'.vg.cf = s.vg.cf ∧ s'.vg.of = s.vg.of ∧
      Frame s s' [.rdi, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.spill, hrdi, hrcx, hv, ↓BitVec.ofNat_add_ofNat, ofNat_idx]
  all_goals first | rfl | simp only [wa, Nat.add_assoc]

end rind.x86_64.sqrx8x
