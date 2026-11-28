import Rind.X86_64.Sqrx8xBlocks

/-! # bn_sqrx8x_internal's shift-and-add blocks, run

`outerBreak`, which stores the last pass's words and starts the shift; `shift`, which doubles eight of `t`'s words
and adds the squares of four of `a`'s, but the last two words' sums; `shiftNext`, which finishes them and loads
the next; and `shiftEnd`, which finishes the last and sets up the reduction. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 4096

namespace rind.x86_64.sqrx8x

/-- The words `shift` reads and writes, from `a`'s word `4i` and `t`'s `8i`. -/
def shiftTrace (ap fp : Addr) (i : Nat) : List Leak :=
  [.addr (wa ap (4 * i + 1)), .addr (wa fp (8 * i + 11)), .addr (wa fp (8 * i + 12)), .addr (wa fp (8 * i + 7)),
   .addr (wa fp (8 * i + 8)), .addr (wa ap (4 * i + 2)), .addr (wa fp (8 * i + 13)), .addr (wa fp (8 * i + 14)),
   .addr (wa fp (8 * i + 9)), .addr (wa fp (8 * i + 10)), .addr (wa ap (4 * i + 3)), .addr (wa fp (8 * i + 15)),
   .addr (wa fp (8 * i + 16)), .addr (wa fp (8 * i + 11)), .addr (wa fp (8 * i + 12))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `shift` at `t`'s word `8i`: `r10` and `r11` are its first two words doubled, the carries `cf` into the first
and `of` into the third, `r12` and `r13` the next two; it stores six words, leaving the seventh in `rax`, the
eighth's three addends in `rbx`, `r13` and `cf`, and the ninth doubled in `r10`, its carry out in `of`. -/
theorem shift_ok (s : S) (k i : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (c o : Bool)
    (hi : 4 * i + 4 ≤ k) (ar : Arr s k ap np fp)
    (hrc : s.vg.gpr .rsi + s.vg.gpr .rcx * 1#64 = wa ap (4 * i)) (hrdi : s.vg.gpr .rdi = wa fp (8 * i + 7))
    (hrdx : s.vg.gpr .rdx = a (4 * i)) (hcf : s.vg.cf = some c) (hof : s.vg.of = some o)
    (hA : ∀ j < k, s.vg.mem.readW (wa ap j) 64 = a j) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.shift s = some (s', shiftTrace ap fp i) ∧
      ∃ (w0 w1 w2 w3 w4 w5 : BitVec 64) (c' o' : Bool),
      s'.vg.mem = (((((s.vg.mem.writeW (wa fp (8 * i + 7)) w0).writeW (wa fp (8 * i + 8)) w1).writeW
        (wa fp (8 * i + 9)) w2).writeW (wa fp (8 * i + 10)) w3).writeW (wa fp (8 * i + 11)) w4).writeW
        (wa fp (8 * i + 12)) w5 ∧
      s'.vg.cf = some c' ∧ s'.vg.of = some o' ∧
      s'.vg.gpr .rcx = s.vg.gpr .rcx + 32#64 ∧ s'.vg.gpr .rdx = a (4 * i + 3) ∧
      s'.vg.gpr .r11 = s.vg.mem.readW (wa fp (8 * i + 16)) 64 ∧
      w0.toNat + w1.toNat * 2 ^ 64 + w2.toNat * 2 ^ 128 + w3.toNat * 2 ^ 192 + w4.toNat * 2 ^ 256 +
        w5.toNat * 2 ^ 320 + (s'.vg.gpr .rax).toNat * 2 ^ 384 +
        ((s'.vg.gpr .rbx).toNat + (s'.vg.gpr .r13).toNat + c'.toNat) * 2 ^ 448 +
        ((s'.vg.gpr .r10).toNat + o'.toNat * 2 ^ 64) * 2 ^ 512 =
        (s.vg.gpr .r10).toNat + c.toNat + (s.vg.gpr .r11).toNat * 2 ^ 64 + o.toNat * 2 ^ 128 +
        2 * ((s.vg.gpr .r12).toNat * 2 ^ 128 + (s.vg.gpr .r13).toNat * 2 ^ 192 +
          (s.vg.mem.readW (wa fp (8 * i + 11)) 64).toNat * 2 ^ 256 +
          (s.vg.mem.readW (wa fp (8 * i + 12)) 64).toNat * 2 ^ 320 +
          (s.vg.mem.readW (wa fp (8 * i + 13)) 64).toNat * 2 ^ 384 +
          (s.vg.mem.readW (wa fp (8 * i + 14)) 64).toNat * 2 ^ 448 +
          (s.vg.mem.readW (wa fp (8 * i + 15)) 64).toNat * 2 ^ 512) +
        (a (4 * i)).toNat * (a (4 * i)).toNat + (a (4 * i + 1)).toNat * (a (4 * i + 1)).toNat * 2 ^ 128 +
        (a (4 * i + 2)).toNat * (a (4 * i + 2)).toNat * 2 ^ 256 +
        (a (4 * i + 3)).toNat * (a (4 * i + 3)).toNat * 2 ^ 384 ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .r10, .r11, .r12, .r13] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.shift, hrc, hrdi, hrdx, hcf, hof, hA, ↓BitVec.ofNat_add_ofNat, ofNat_idx]
  all_goals first | acct | (rw [show (4#64 : BitVec 64) * 8#64 = 32#64 by decide])

/-- `lea rcx, [rbp + r9 - 64]`: `np`'s last eight words. -/
theorem np_end (np : Addr) (k : Nat) (hk : 8 ≤ k ∧ k < 2 ^ 29) :
    np + BitVec.ofNat 64 (8 * k) * 1#64 + 18446744073709551552#64 = wa np (k - 8) := by
  simp only [wa]; bv_omega

def shiftNextTrace (ap fp : Addr) (i : Nat) : List Leak :=
  [.addr (wa ap (4 * i + 4)), .addr (wa fp (8 * i + 17)), .addr (wa fp (8 * i + 18)), .addr (wa fp (8 * i + 13)),
   .addr (wa fp (8 * i + 14))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `shiftNext` after `shift` at `t`'s word `8i`: stores its seventh and eighth words, doubles the tenth into
`r11`, loads the next two into `r12` and `r13` and `a`'s next word into `rdx`, and steps `rdi` on. -/
theorem shiftNext_ok (s : S) (k i : Nat) (ap np fp : Addr) (a : Nat → BitVec 64) (c o : Bool)
    (hi : 4 * i + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrc : s.vg.gpr .rsi + s.vg.gpr .rcx * 1#64 = wa ap (4 * i + 4)) (hrdi : s.vg.gpr .rdi = wa fp (8 * i + 7))
    (hcf : s.vg.cf = some c) (hof : s.vg.of = some o) (hA : ∀ j < k, s.vg.mem.readW (wa ap j) 64 = a j) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.shiftNext s = some (s', shiftNextTrace ap fp i) ∧
      ∃ c' o' : Bool,
      s'.vg.mem = (s.vg.mem.writeW (wa fp (8 * i + 13)) (s.vg.gpr .rax)).writeW (wa fp (8 * i + 14))
        (s'.vg.gpr .rbx) ∧
      s'.vg.cf = some c' ∧ s'.vg.of = some o' ∧ s'.vg.gpr .rdx = a (4 * i + 4) ∧
      s'.vg.gpr .r12 = s.vg.mem.readW (wa fp (8 * i + 17)) 64 ∧
      s'.vg.gpr .r13 = s.vg.mem.readW (wa fp (8 * i + 18)) 64 ∧ s'.vg.gpr .rdi = wa fp (8 * i + 15) ∧
      (s'.vg.gpr .rbx).toNat + c'.toNat * 2 ^ 64 = (s.vg.gpr .rbx).toNat + (s.vg.gpr .r13).toNat + c.toNat ∧
      (s'.vg.gpr .r11).toNat + o'.toNat * 2 ^ 64 = 2 * (s.vg.gpr .r11).toNat + o.toNat ∧
      Frame s s' [.rbx, .rdx, .rdi, .r11, .r12, .r13] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [Rind.X86_64.Sqrx8x.shiftNext, hrc, hrdi, hcf, hof, hA, ↓BitVec.ofNat_add_ofNat, ofNat_idx]
  all_goals acct

def shiftEndTrace (fp : Addr) (i : Nat) : List Leak :=
  [.addr (wa fp (8 * i + 13)), .addr (wa fp (8 * i + 14)), .addr (wa fp 5), .addr (wa fp 7), .addr (wa fp 1),
   .addr (wa fp 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `shiftEnd` after the last `shift`, at `t`'s word `8i`: stores its seventh and eighth words, the latter's carry
out dropped, and sets up the reduction: `np` in `rbp`, `n0` in `rbx`, `t`'s first word in `rdx`, `rax` and the
carries zero, slot 1 `np`'s last eight words, slot 2 the end of `t`'s `2k`, and `rdi` at `t`. -/
theorem shiftEnd_ok (s : S) (k i : Nat) (ap np fp : Addr) (c : Bool)
    (hk8 : 8 ≤ k) (hi : 8 * i + 8 = 2 * k) (ar : Arr s k ap np fp)
    (hrdi : s.vg.gpr .rdi = wa fp (8 * i + 7)) (hrsp : s.vg.gpr .rsp = fp) (hcf : s.vg.cf = some c)
    (hx2 : (s.vg.xmm .xmm2).setWidth 64 = np) (hr9 : s.vg.gpr .r9 = BitVec.ofNat 64 (8 * k)) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.shiftEnd s = some (s', shiftEndTrace fp i) ∧
      ∃ w : BitVec 64,
      s'.vg.mem = (((s.vg.mem.writeW (wa fp (8 * i + 13)) (s.vg.gpr .rax)).writeW (wa fp (8 * i + 14)) w).writeW
        (wa fp 1) (wa np (k - 8))).writeW (wa fp 2) (wa fp (8 * i + 15)) ∧
      w.toNat + (adcC (s.vg.gpr .rbx) (s.vg.gpr .r13) c).toNat * 2 ^ 64 =
        (s.vg.gpr .rbx).toNat + (s.vg.gpr .r13).toNat + c.toNat ∧
      s'.vg.gpr .rbp = np ∧ s'.vg.gpr .rax = 0 ∧ s'.vg.cf = some false ∧ s'.vg.of = some false ∧
      s'.vg.gpr .rbx = s.vg.mem.readW (wa fp 5) 64 ∧ s'.vg.gpr .rdx = s.vg.mem.readW (wa fp 7) 64 ∧
      s'.vg.gpr .rdi = wa fp 7 ∧
      Frame s s' [.rax, .rbx, .rcx, .rdx, .rdi, .rbp] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  have hk' : 8 ≤ k ∧ k < 2 ^ 29 := ⟨hk8, hk⟩
  sqrx_blockx [Rind.X86_64.Sqrx8x.shiftEnd, hrdi, hrsp, hcf, extract_lo, hx2, hr9, np_end np k hk', xmm_setMem,
    xmm_setReg, xmm_arithFlags, xmm_setFlags,
    BitVec.xor_self, ↓BitVec.ofNat_add_ofNat, ofNat_idx]
  all_goals acct

def outerBreakTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa fp (16 * R + 16)), .addr (wa fp (16 * R + 17)), .addr (wa fp (16 * R + 18)),
   .addr (wa fp (16 * R + 19)), .addr (wa fp (16 * R + 20)), .addr (wa fp (16 * R + 21)), .addr (wa ap 0),
   .addr (wa fp 8), .addr (wa fp 1), .addr (wa fp 9), .addr (wa fp 10)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `outerBreak` after the last row block `R`'s triangle: stores `r9` to `r14` at `t`'s words `16R + 9` on, and
starts the shift at `t`'s first word: `rcx` `-8k`, `a`'s first word in `rdx`, `t`'s second doubled in `r11`, its
carry in `of`, the third and fourth in `r12` and `r13`, `r10` and `cf` zero, and `8k` in `r9`. -/
theorem outerBreak_ok (s : S) (k R : Nat) (ap np fp : Addr) (a : Nat → BitVec 64)
    (hR : 8 * R + 8 = k) (ar : Arr s k ap np fp)
    (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hrc : s.vg.gpr .rsi + (s.vg.xmm .xmm3).setWidth 64 * 1#64 = wa ap 0)
    (hA : ∀ j < k, s.vg.mem.readW (wa ap j) 64 = a j) :
    ∃ s', execBlock I Rind.X86_64.Sqrx8x.outerBreak s = some (s', outerBreakTrace ap fp R) ∧
      ∃ o' : Bool,
      s'.vg.mem = (((((s.vg.mem.writeW (wa fp (16 * R + 16)) (s.vg.gpr .r9)).writeW (wa fp (16 * R + 17))
        (s.vg.gpr .r10)).writeW (wa fp (16 * R + 18)) (s.vg.gpr .r11)).writeW (wa fp (16 * R + 19))
        (s.vg.gpr .r12)).writeW (wa fp (16 * R + 20)) (s.vg.gpr .r13)).writeW (wa fp (16 * R + 21))
        (s.vg.gpr .r14) ∧
      s'.vg.of = some o' ∧ s'.vg.cf = some false ∧
      s'.vg.gpr .rcx = (s.vg.xmm .xmm3).setWidth 64 ∧ s'.vg.gpr .rdi = wa fp 7 ∧ s'.vg.gpr .rdx = a 0 ∧
      s'.vg.gpr .r10 = 0 ∧ s'.vg.gpr .r9 = s.vg.mem.readW (wa fp 1) 64 ∧
      s'.vg.gpr .r12 = s.vg.mem.readW (wa fp 9) 64 ∧ s'.vg.gpr .r13 = s.vg.mem.readW (wa fp 10) 64 ∧
      (s'.vg.gpr .r11).toNat + o'.toNat * 2 ^ 64 = 2 * (s.vg.mem.readW (wa fp 8) 64).toNat ∧
      Frame s s' [.rcx, .rdx, .rdi, .r9, .r10, .r11, .r12, .r13] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  have h8 : wa fp 8 = fp + 64#64 := by simp [wa]
  sqrx_blockx [Rind.X86_64.Sqrx8x.outerBreak, hrdi, hrsp, extract_lo, hrc, hA, BitVec.xor_self, xmm_setMem,
    xmm_setReg, xmm_arithFlags, xmm_setFlags,
    ↓BitVec.ofNat_add_ofNat, ofNat_idx]
  all_goals acct

end rind.x86_64.sqrx8x
