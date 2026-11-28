import Rind.X86_64.Sqrx8xSpec

/-! # bn_sqrx8x_internal's triangle, block by block -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false

namespace rind.x86_64.sqrx8x

/-- Runs a block as `sqrx_block` does, but leaves the goals it does not close by `rfl`, and opens existentials,
whose witnesses the memory's equation, first, fixes. -/
syntax "sqrx_blockx " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| sqrx_blockx [$xs,*]) => `(tactic| (
    apply ex_of_eq
    · rw [execBlock_acc]
      sqrx_run [$xs,*]
      rfl
    · rfl
    repeat' (first | apply And.intro | apply Exists.intro)
    all_goals try refine Frame.mk (fun r hr => ?_) ?_ ?_ ?_ rfl
    all_goals try simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    all_goals try simp (config := { maxSteps := 4000000 }) only [gpr_setReg, mem_setReg, wr_setReg, xmm_setReg,
      others_setReg, gpr_arithFlags, mem_arithFlags, wr_arithFlags, xmm_arithFlags, others_arithFlags, gpr_setFlags,
      mem_setFlags, wr_setFlags, xmm_setFlags, others_setFlags, gpr_setMem, mem_setMem, wr_setMem, xmm_setMem,
      others_setMem, cf_arithFlags, cf_setReg, cf_setFlags, cf_setMem, of_setReg, of_setFlags, of_arithFlags,
      of_setMem, zf_setReg, zf_setFlags, zf_arithFlags, zf_setMem, reduceCtorEq, ↓reduceIte, *]
    all_goals first
      | with_reducible rfl
      | skip))

theorem hsum_append (ws : List (BitVec 64)) (w : BitVec 64) :
    hsum (ws ++ [w]) = hsum ws + w.toNat * 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => show w.toNat + 2 ^ 64 * 0 = 0 + w.toNat * 2 ^ (64 * 0); omega
  | cons x ws ih =>
    rw [List.cons_append, hsum, ih, hsum, List.length_cons, show 64 * (ws.length + 1) = 64 + 64 * ws.length by ring,
      Nat.pow_add]
    ring

theorem hsum_lt (ws : List (BitVec 64)) : hsum ws < 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => show 0 < 2 ^ (64 * 0); omega
  | cons x ws ih =>
    rw [hsum, List.length_cons, show 64 * (ws.length + 1) = 64 + 64 * ws.length by ring, Nat.pow_add]
    have := x.isLt
    have : 2 ^ 64 * hsum ws + 2 ^ 64 ≤ 2 ^ 64 * 2 ^ (64 * ws.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    omega

/-- The products `b i · b j`, `i < j`, of eight words, each at its weight. -/
def diag8 (b : Nat → BitVec 64) : Nat :=
  (b 0).toNat * (b 1).toNat * 2 ^ 64 +
    (b 0).toNat * (b 2).toNat * 2 ^ 128 +
    (b 0).toNat * (b 3).toNat * 2 ^ 192 +
    (b 0).toNat * (b 4).toNat * 2 ^ 256 +
    (b 0).toNat * (b 5).toNat * 2 ^ 320 +
    (b 0).toNat * (b 6).toNat * 2 ^ 384 +
    (b 0).toNat * (b 7).toNat * 2 ^ 448 +
    (b 1).toNat * (b 2).toNat * 2 ^ 192 +
    (b 1).toNat * (b 3).toNat * 2 ^ 256 +
    (b 1).toNat * (b 4).toNat * 2 ^ 320 +
    (b 1).toNat * (b 5).toNat * 2 ^ 384 +
    (b 1).toNat * (b 6).toNat * 2 ^ 448 +
    (b 1).toNat * (b 7).toNat * 2 ^ 512 +
    (b 2).toNat * (b 3).toNat * 2 ^ 320 +
    (b 2).toNat * (b 4).toNat * 2 ^ 384 +
    (b 2).toNat * (b 5).toNat * 2 ^ 448 +
    (b 2).toNat * (b 6).toNat * 2 ^ 512 +
    (b 2).toNat * (b 7).toNat * 2 ^ 576 +
    (b 3).toNat * (b 4).toNat * 2 ^ 448 +
    (b 3).toNat * (b 5).toNat * 2 ^ 512 +
    (b 3).toNat * (b 6).toNat * 2 ^ 576 +
    (b 3).toNat * (b 7).toNat * 2 ^ 640 +
    (b 4).toNat * (b 5).toNat * 2 ^ 576 +
    (b 4).toNat * (b 6).toNat * 2 ^ 640 +
    (b 4).toNat * (b 7).toNat * 2 ^ 704 +
    (b 5).toNat * (b 6).toNat * 2 ^ 704 +
    (b 5).toNat * (b 7).toNat * 2 ^ 768 +
    (b 6).toNat * (b 7).toNat * 2 ^ 832

/-- An index past a constant, moved on by another: the constants summed, as the run leaves them. -/
theorem ofNat_idx (n a b : Nat) : BitVec.ofNat 64 (n + a + b) = BitVec.ofNat 64 (n + (a + b)) := by
  rw [Nat.add_assoc]

/-- The words `tri` reads from `a`, from word `8I`, and `t`, at word `16I`. -/
def triTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa ap (8 * R + 1)), .addr (wa ap (8 * R + 2)), .addr (wa ap (8 * R + 3)), .addr (wa ap (8 * R + 4)),
   .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)), .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 1)),
   .addr (wa fp (16 * R + 15)), .addr (wa fp (16 * R + 8)), .addr (wa fp (16 * R + 9)), .addr (wa ap (8 * R + 2)),
   .addr (wa ap (8 * R + 3)), .addr (wa ap (8 * R + 4)), .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)),
   .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 2)), .addr (wa fp (16 * R + 10)), .addr (wa fp (16 * R + 11)),
   .addr (wa ap (8 * R + 3)), .addr (wa ap (8 * R + 4)), .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)),
   .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 3)), .addr (wa fp (16 * R + 12)), .addr (wa fp (16 * R + 13)),
   .addr (wa ap (8 * R + 4)), .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)), .addr (wa ap (8 * R + 7)),
   .addr (wa ap (8 * R + 4)), .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)), .addr (wa fp (16 * R + 14)),
   .addr (wa fp (16 * R + 15)), .addr (wa ap (8 * R + 7)), .addr (wa fp 2)]

end rind.x86_64.sqrx8x
