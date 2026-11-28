import Rind.X86_64.Sqrx8xTri

/-! # bn_sqrx8x_internal's `tri`, in chunks

`tri` runs as six chunks, cut where its carry chains restart, so that each runs symbolically from opaque
inputs: words at their weights (as powers of `2^64` from `t`'s word `16R`), and the halves of the products a
chunk leaves for the next. Each chunk's lemma relates its outputs' weighted sum, with the carries it leaves, to
its inputs' and its products'. -/

open VG VG.X86_64 rind.x86_64.asm rind.x86_64.acct rind.x86_64.mul4x rind.x86_64.mulx4x

set_option linter.unusedSimpArgs false
-- The chunks share one signature; not every chunk uses every argument.
set_option linter.unusedVariables false
set_option exponentiation.threshold 4096

namespace rind.x86_64.sqrx8x

open Rind.X86_64.Mul4x in
/-- `tri`'s instructions 0 to 26. -/
def triA : List Rind.X86_64.Instr :=
  [.vg (.mulx .rax .r8 (.mem (m .rsi 8))),
   .vg (.adcx .r8 (.reg .r9)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.mulx .rax .r9 (.mem (m .rsi 16))),
   .vg (.adcx .r9 (.reg .r10)),
   .vg (.adox .r11 (.reg .rax)),
   .vg (.mulx .rax .r10 (.mem (m .rsi 24))),
   .vg (.adcx .r10 (.reg .r11)),
   .vg (.adox .r12 (.reg .rax)),
   .vg (.mulx .rax .r11 (.mem (m .rsi 32))),
   .vg (.adcx .r11 (.reg .r12)),
   .vg (.adox .r13 (.reg .rax)),
   .vg (.mulx .rax .r12 (.mem (m .rsi 40))),
   .vg (.adcx .r12 (.reg .r13)),
   .vg (.adox .r14 (.reg .rax)),
   .vg (.mulx .rax .r13 (.mem (m .rsi 48))),
   .vg (.adcx .r13 (.reg .r14)),
   .vg (.adox .rax (.reg .r15)),
   .vg (.mulx .r15 .r14 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 8))),
   .vg (.adcx .r14 (.reg .rax)),
   .vg (.adox .r15 (.reg .rbp)),
   .vg (.alu .adc .r15 (.mem (m .rdi 64))),
   .vg (.store (m .rdi 8) .r8),
   .vg (.store (m .rdi 16) .r9),
   .vg (.alu .sbb .rcx (.reg .rcx)),
   .vg (.alu .xor .rbp (.reg .rbp))]

open Rind.X86_64.Mul4x in
/-- `tri`'s instructions 27 to 48. -/
def triB : List Rind.X86_64.Instr :=
  [.vg (.mulx .rbx .r8 (.mem (m .rsi 16))),
   .vg (.mulx .rax .r9 (.mem (m .rsi 24))),
   .vg (.adcx .r8 (.reg .r10)),
   .vg (.adox .r9 (.reg .rbx)),
   .vg (.mulx .rbx .r10 (.mem (m .rsi 32))),
   .vg (.adcx .r9 (.reg .r11)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.mulx .rax .r11 (.mem (m .rsi 40))),
   .vg (.adcx .r10 (.reg .r12)),
   .vg (.adox .r11 (.reg .rbx)),
   .vg (.mulx .rbx .r12 (.mem (m .rsi 48))),
   .vg (.adcx .r11 (.reg .r13)),
   .vg (.adox .r12 (.reg .r14)),
   .vg (.mulx .r14 .r13 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 16))),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .rbx)),
   .vg (.adcx .r13 (.reg .r15)),
   .vg (.adox .r14 (.reg .rbp)),
   .vg (.adcx .r14 (.reg .rbp)),
   .vg (.store (m .rdi 24) .r8),
   .vg (.store (m .rdi 32) .r9)]

open Rind.X86_64.Mul4x in
/-- `tri`'s instructions 49 to 68. -/
def triC : List Rind.X86_64.Instr :=
  [.vg (.mulx .rbx .r8 (.mem (m .rsi 24))),
   .vg (.mulx .rax .r9 (.mem (m .rsi 32))),
   .vg (.adcx .r8 (.reg .r10)),
   .vg (.adox .r9 (.reg .rbx)),
   .vg (.mulx .rbx .r10 (.mem (m .rsi 40))),
   .vg (.adcx .r9 (.reg .r11)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.mulx .rax .r11 (.mem (m .rsi 48))),
   .vg (.adcx .r10 (.reg .r12)),
   .vg (.adox .r11 (.reg .r13)),
   .vg (.mulx .r13 .r12 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 24))),
   .vg (.adcx .r11 (.reg .rbx)),
   .vg (.adox .r12 (.reg .rax)),
   .vg (.adcx .r12 (.reg .r14)),
   .vg (.store (m .rdi 40) .r8),
   .vg (.store (m .rdi 48) .r9),
   .vg (.mulx .rax .r8 (.mem (m .rsi 32))),
   .vg (.adox .r13 (.reg .rbp)),
   .vg (.adcx .r13 (.reg .rbp))]

open Rind.X86_64.Mul4x in
/-- `tri`'s instructions 69 to 87. -/
def triD : List Rind.X86_64.Instr :=
  [.vg (.mulx .rbx .r9 (.mem (m .rsi 40))),
   .vg (.adcx .r8 (.reg .r10)),
   .vg (.adox .r9 (.reg .rax)),
   .vg (.mulx .rax .r10 (.mem (m .rsi 48))),
   .vg (.adcx .r9 (.reg .r11)),
   .vg (.adox .r10 (.reg .r12)),
   .vg (.mulx .r12 .r11 (.mem (m .rsi 56))),
   .vg (.mov .rdx (.mem (m .rsi 32))),
   .vg (.mov .r14 (.mem (m .rsi 40))),
   .vg (.adcx .r10 (.reg .rbx)),
   .vg (.adox .r11 (.reg .rax)),
   .vg (.mov .r15 (.mem (m .rsi 48))),
   .vg (.adcx .r11 (.reg .r13)),
   .vg (.adox .r12 (.reg .rbp)),
   .vg (.adcx .r12 (.reg .rbp)),
   .vg (.store (m .rdi 56) .r8),
   .vg (.store (m .rdi 64) .r9),
   .vg (.mulx .rax .r9 (.reg .r14)),
   .vg (.mov .r8 (.mem (m .rsi 56)))]

open Rind.X86_64.Mul4x in
/-- `tri`'s instructions 88 to 99. -/
def triE : List Rind.X86_64.Instr :=
  [.vg (.adcx .r9 (.reg .r10)),
   .vg (.mulx .rbx .r10 (.reg .r15)),
   .vg (.adox .r10 (.reg .rax)),
   .vg (.adcx .r10 (.reg .r11)),
   .vg (.mulx .rax .r11 (.reg .r8)),
   .vg (.mov .rdx (.reg .r14)),
   .vg (.adox .r11 (.reg .rbx)),
   .vg (.adcx .r11 (.reg .r12)),
   .vg (.adcx .rax (.reg .rbp)),
   .vg (.mulx .rbx .r14 (.reg .r15)),
   .vg (.mulx .r13 .r12 (.reg .r8)),
   .vg (.mov .rdx (.reg .r15))]

open Rind.X86_64.Mul4x in
/-- `tri`'s instructions 100 to 108. -/
def triF : List Rind.X86_64.Instr :=
  [.lea .rsi (m .rsi 64),
   .vg (.adcx .r11 (.reg .r14)),
   .vg (.adox .r12 (.reg .rbx)),
   .vg (.adcx .r12 (.reg .rax)),
   .vg (.adox .r13 (.reg .rbp)),
   .vg (.mulx .r14 .r8 (.reg .r8)),
   .vg (.adcx .r13 (.reg .r8)),
   .vg (.adcx .r14 (.reg .rbp)),
   .vg (.alu .cmp .rsi (.mem (m .rsp 16)))]

def triATrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa ap (8 * R + 1)), .addr (wa ap (8 * R + 2)), .addr (wa ap (8 * R + 3)), .addr (wa ap (8 * R + 4)),
   .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)), .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 1)),
   .addr (wa fp (16 * R + 15)), .addr (wa fp (16 * R + 8)), .addr (wa fp (16 * R + 9))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triA_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64) (u8 : BitVec 64)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hrbp : s.vg.gpr .rbp = 0) (hrdx : s.vg.gpr .rdx = b 0)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false)
    (hu : s.vg.mem.readW (wa fp (16 * R + 15)) 64 = u8) :
    ∃ s', execBlock I triA s = some (s', triATrace ap fp R) ∧
      ∃ (w0 w1 : BitVec 64) (mc : Bool),
      s'.vg.mem = (s.vg.mem.writeW (wa fp (16 * R + 8)) w0).writeW (wa fp (16 * R + 9)) w1 ∧
      s'.vg.gpr .rdx = b 1 ∧
      s'.vg.gpr .rcx = 0 - (BitVec.ofBool mc).setWidth 64 ∧
      s'.vg.gpr .rbp = 0 ∧
      s'.vg.cf = some false ∧
      s'.vg.of = some false ∧
      w1.toNat * 2 ^ 128 + w0.toNat * 2 ^ 64 + (s'.vg.gpr .r10).toNat * 2 ^ 192 + (s'.vg.gpr .r11).toNat * 2 ^ 256 +
        (s'.vg.gpr .r12).toNat * 2 ^ 320 + (s'.vg.gpr .r13).toNat * 2 ^ 384 +
        (s'.vg.gpr .r14).toNat * 2 ^ 448 + (s'.vg.gpr .r15).toNat * 2 ^ 512 + mc.toNat * 2 ^ 576 =
        (s.vg.gpr .r10).toNat * 2 ^ 128 + (s.vg.gpr .r11).toNat * 2 ^ 192 + (s.vg.gpr .r12).toNat * 2 ^ 256 +
        (s.vg.gpr .r13).toNat * 2 ^ 320 + (s.vg.gpr .r14).toNat * 2 ^ 384 + (s.vg.gpr .r15).toNat * 2 ^ 448 +
        (s.vg.gpr .r9).toNat * 2 ^ 64 + (b 0).toNat * (b 1).toNat * 2 ^ 64 +
        (b 0).toNat * (b 2).toNat * 2 ^ 128 + (b 0).toNat * (b 3).toNat * 2 ^ 192 +
        (b 0).toNat * (b 4).toNat * 2 ^ 256 + (b 0).toNat * (b 5).toNat * 2 ^ 320 +
        (b 0).toNat * (b 6).toNat * 2 ^ 384 + (b 0).toNat * (b 7).toNat * 2 ^ 448 + u8.toNat * 2 ^ 512 ∧
      Frame s s' [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [triA, hrsi, hrdi, hrsp, hA, hrbp, hrdx, hcf, hof, hu, ↓BitVec.ofNat_add_ofNat, ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub]
  all_goals acct

def triBTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa ap (8 * R + 2)), .addr (wa ap (8 * R + 3)), .addr (wa ap (8 * R + 4)), .addr (wa ap (8 * R + 5)),
   .addr (wa ap (8 * R + 6)), .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 2)),
   .addr (wa fp (16 * R + 10)), .addr (wa fp (16 * R + 11))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triB_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hrbp : s.vg.gpr .rbp = 0) (hrdx : s.vg.gpr .rdx = b 1)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false) :
    ∃ s', execBlock I triB s = some (s', triBTrace ap fp R) ∧
      ∃ (w0 w1 : BitVec 64) (cf' of' : Bool),
      s'.vg.mem = (s.vg.mem.writeW (wa fp (16 * R + 10)) w0).writeW (wa fp (16 * R + 11)) w1 ∧
      s'.vg.cf = some cf' ∧
      s'.vg.of = some of' ∧
      s'.vg.gpr .rdx = b 2 ∧
      w1.toNat * 2 ^ 256 + w0.toNat * 2 ^ 192 + (s'.vg.gpr .r10).toNat * 2 ^ 320 + (s'.vg.gpr .r11).toNat * 2 ^ 384 +
        (s'.vg.gpr .r12).toNat * 2 ^ 448 + (s'.vg.gpr .r13).toNat * 2 ^ 512 +
        (s'.vg.gpr .r14).toNat * 2 ^ 576 + cf'.toNat * 2 ^ 640 + of'.toNat * 2 ^ 640 =
        (s.vg.gpr .r10).toNat * 2 ^ 192 + (s.vg.gpr .r11).toNat * 2 ^ 256 + (s.vg.gpr .r12).toNat * 2 ^ 320 +
        (s.vg.gpr .r13).toNat * 2 ^ 384 + (s.vg.gpr .r14).toNat * 2 ^ 448 + (s.vg.gpr .r15).toNat * 2 ^ 512 +
        (b 1).toNat * (b 2).toNat * 2 ^ 192 + (b 1).toNat * (b 3).toNat * 2 ^ 256 +
        (b 1).toNat * (b 4).toNat * 2 ^ 320 + (b 1).toNat * (b 5).toNat * 2 ^ 384 +
        (b 1).toNat * (b 6).toNat * 2 ^ 448 + (b 1).toNat * (b 7).toNat * 2 ^ 512 ∧
      Frame s s' [.rax, .rbx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13, .r14] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [triB, hrsi, hrdi, hrsp, hA, hrbp, hrdx, hcf, hof, ↓BitVec.ofNat_add_ofNat, ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub]
  all_goals acct

def triCTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa ap (8 * R + 3)), .addr (wa ap (8 * R + 4)), .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)),
   .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 3)), .addr (wa fp (16 * R + 12)),
   .addr (wa fp (16 * R + 13)), .addr (wa ap (8 * R + 4))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triC_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hrbp : s.vg.gpr .rbp = 0) (hrdx : s.vg.gpr .rdx = b 2)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false) :
    ∃ s', execBlock I triC s = some (s', triCTrace ap fp R) ∧
      ∃ (w0 w1 : BitVec 64) (cf' of' : Bool),
      s'.vg.mem = (s.vg.mem.writeW (wa fp (16 * R + 12)) w0).writeW (wa fp (16 * R + 13)) w1 ∧
      s'.vg.cf = some cf' ∧
      s'.vg.of = some of' ∧
      s'.vg.gpr .r8 = mulLo (b 3) (b 4) ∧
      s'.vg.gpr .rax = mulHi (b 3) (b 4) ∧
      s'.vg.gpr .rdx = b 3 ∧
      w1.toNat * 2 ^ 384 + w0.toNat * 2 ^ 320 + (s'.vg.gpr .r10).toNat * 2 ^ 448 + (s'.vg.gpr .r11).toNat * 2 ^ 512 +
        (s'.vg.gpr .r12).toNat * 2 ^ 576 + (s'.vg.gpr .r13).toNat * 2 ^ 640 + cf'.toNat * 2 ^ 704 +
        of'.toNat * 2 ^ 704 =
        (s.vg.gpr .r10).toNat * 2 ^ 320 + (s.vg.gpr .r11).toNat * 2 ^ 384 + (s.vg.gpr .r12).toNat * 2 ^ 448 +
        (s.vg.gpr .r13).toNat * 2 ^ 512 + (s.vg.gpr .r14).toNat * 2 ^ 576 +
        (b 2).toNat * (b 3).toNat * 2 ^ 320 + (b 2).toNat * (b 4).toNat * 2 ^ 384 +
        (b 2).toNat * (b 5).toNat * 2 ^ 448 + (b 2).toNat * (b 6).toNat * 2 ^ 512 +
        (b 2).toNat * (b 7).toNat * 2 ^ 576 ∧
      Frame s s' [.rax, .rbx, .rdx, .r8, .r9, .r10, .r11, .r12, .r13] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [triC, hrsi, hrdi, hrsp, hA, hrbp, hrdx, hcf, hof, ↓BitVec.ofNat_add_ofNat, ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub]
  all_goals acct

def triDTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)), .addr (wa ap (8 * R + 7)), .addr (wa ap (8 * R + 4)),
   .addr (wa ap (8 * R + 5)), .addr (wa ap (8 * R + 6)), .addr (wa fp (16 * R + 14)),
   .addr (wa fp (16 * R + 15)), .addr (wa ap (8 * R + 7))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triD_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hr8 : s.vg.gpr .r8 = mulLo (b 3) (b 4)) (hrax : s.vg.gpr .rax = mulHi (b 3) (b 4)) (hrbp : s.vg.gpr .rbp = 0)
    (hrdx : s.vg.gpr .rdx = b 3)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false) :
    ∃ s', execBlock I triD s = some (s', triDTrace ap fp R) ∧
      ∃ (w0 w1 : BitVec 64) (cf' of' : Bool),
      s'.vg.mem = (s.vg.mem.writeW (wa fp (16 * R + 14)) w0).writeW (wa fp (16 * R + 15)) w1 ∧
      s'.vg.cf = some cf' ∧
      s'.vg.of = some of' ∧
      s'.vg.gpr .r14 = b 5 ∧
      s'.vg.gpr .r15 = b 6 ∧
      s'.vg.gpr .r8 = b 7 ∧
      s'.vg.gpr .r9 = mulLo (b 4) (b 5) ∧
      s'.vg.gpr .rax = mulHi (b 4) (b 5) ∧
      s'.vg.gpr .rdx = b 4 ∧
      w1.toNat * 2 ^ 512 + w0.toNat * 2 ^ 448 + (s'.vg.gpr .r10).toNat * 2 ^ 576 + (s'.vg.gpr .r11).toNat * 2 ^ 640 +
        (s'.vg.gpr .r12).toNat * 2 ^ 704 + cf'.toNat * 2 ^ 768 + of'.toNat * 2 ^ 768 =
        (s.vg.gpr .r10).toNat * 2 ^ 448 + (s.vg.gpr .r11).toNat * 2 ^ 512 + (s.vg.gpr .r12).toNat * 2 ^ 576 +
        (s.vg.gpr .r13).toNat * 2 ^ 640 + (b 3).toNat * (b 4).toNat * 2 ^ 448 +
        (b 3).toNat * (b 5).toNat * 2 ^ 512 + (b 3).toNat * (b 6).toNat * 2 ^ 576 +
        (b 3).toNat * (b 7).toNat * 2 ^ 640 ∧
      Frame s s' [.rax, .rbx, .rdx, .r8, .r9, .r10, .r11, .r12, .r14, .r15] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [triD, hrsi, hrdi, hrsp, hA, hr8, hrax, hrbp, hrdx, hcf, hof, ↓BitVec.ofNat_add_ofNat, ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub]
  all_goals acct

def triETrace (ap fp : Addr) (R : Nat) : List Leak :=
  []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triE_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hr14 : s.vg.gpr .r14 = b 5) (hr15 : s.vg.gpr .r15 = b 6) (hr8 : s.vg.gpr .r8 = b 7)
    (hr9 : s.vg.gpr .r9 = mulLo (b 4) (b 5)) (hrax : s.vg.gpr .rax = mulHi (b 4) (b 5))
    (hrbp : s.vg.gpr .rbp = 0) (hrdx : s.vg.gpr .rdx = b 4)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some false) :
    ∃ s', execBlock I triE s = some (s', triETrace ap fp R) ∧
      ∃ (cf' of' : Bool),
      s'.vg.mem = s.vg.mem ∧
      s'.vg.cf = some cf' ∧
      s'.vg.of = some of' ∧
      s'.vg.gpr .r12 = mulLo (b 5) (b 7) ∧
      s'.vg.gpr .r13 = mulHi (b 5) (b 7) ∧
      s'.vg.gpr .r14 = mulLo (b 5) (b 6) ∧
      s'.vg.gpr .r8 = b 7 ∧
      s'.vg.gpr .rbx = mulHi (b 5) (b 6) ∧
      s'.vg.gpr .rdx = b 6 ∧
      (s'.vg.gpr .r10).toNat * 2 ^ 640 + (s'.vg.gpr .r11).toNat * 2 ^ 704 + (s'.vg.gpr .r9).toNat * 2 ^ 576 +
        (s'.vg.gpr .rax).toNat * 2 ^ 768 + cf'.toNat * 2 ^ 832 + of'.toNat * 2 ^ 768 =
        (s.vg.gpr .r10).toNat * 2 ^ 576 + (s.vg.gpr .r11).toNat * 2 ^ 640 + (s.vg.gpr .r12).toNat * 2 ^ 704 +
        (b 4).toNat * (b 5).toNat * 2 ^ 576 + (b 4).toNat * (b 6).toNat * 2 ^ 640 +
        (b 4).toNat * (b 7).toNat * 2 ^ 704 ∧
      Frame s s' [.rax, .rbx, .rdx, .r9, .r10, .r11, .r12, .r13, .r14] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [triE, hrsi, hrdi, hrsp, hA, hr14, hr15, hr8, hr9, hrax, hrbp, hrdx, hcf, hof, ↓BitVec.ofNat_add_ofNat, ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub]
  all_goals acct

def triFTrace (ap fp : Addr) (R : Nat) : List Leak :=
  [.addr (wa fp 2)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triF_ok (s : S) (k R : Nat) (ap np fp : Addr) (b : Nat → BitVec 64) (of : Bool)
    (hR : 8 * R + 8 ≤ k) (ar : Arr s k ap np fp)
    (hrsi : s.vg.gpr .rsi = wa ap (8 * R)) (hrdi : s.vg.gpr .rdi = wa fp (16 * R + 7)) (hrsp : s.vg.gpr .rsp = fp)
    (hA : ∀ i < 8, s.vg.mem.readW (wa ap (8 * R + i)) 64 = b i)
    (hr12 : s.vg.gpr .r12 = mulLo (b 5) (b 7)) (hr13 : s.vg.gpr .r13 = mulHi (b 5) (b 7))
    (hr14 : s.vg.gpr .r14 = mulLo (b 5) (b 6)) (hr8 : s.vg.gpr .r8 = b 7) (hrbp : s.vg.gpr .rbp = 0)
    (hrbx : s.vg.gpr .rbx = mulHi (b 5) (b 6)) (hrdx : s.vg.gpr .rdx = b 6)
    (hcf : s.vg.cf = some false) (hof : s.vg.of = some of) :
    ∃ s', execBlock I triF s = some (s', triFTrace ap fp R) ∧
      s'.vg.mem = s.vg.mem ∧
      s'.vg.gpr .rsi = wa ap (8 * R + 8) ∧
      s'.vg.zf = some (wa ap (8 * R + 8) - s.vg.mem.readW (wa fp 2) 64 == 0) ∧
      (s'.vg.gpr .r10).toNat * 2 ^ 640 + (s'.vg.gpr .r11).toNat * 2 ^ 704 + (s'.vg.gpr .r12).toNat * 2 ^ 768 +
        (s'.vg.gpr .r13).toNat * 2 ^ 832 + (s'.vg.gpr .r14).toNat * 2 ^ 896 + (s'.vg.gpr .r9).toNat * 2 ^ 576 =
        (s.vg.gpr .r10).toNat * 2 ^ 640 + (s.vg.gpr .r11).toNat * 2 ^ 704 + (s.vg.gpr .r9).toNat * 2 ^ 576 +
        (s.vg.gpr .rax).toNat * 2 ^ 768 + (b 5).toNat * (b 7).toNat * 2 ^ 768 +
        (b 5).toNat * (b 6).toNat * 2 ^ 704 + (b 6).toNat * (b 7).toNat * 2 ^ 832 + of.toNat * 2 ^ 768 ∧
      Frame s s' [.rsi, .r8, .r11, .r12, .r13, .r14] := by
  obtain ⟨hk, hap, hnp, hfp, sepA, sepN, rA, rN, LF, hLF, rF⟩ := ar
  sqrx_blockx [triF, hrsi, hrdi, hrsp, hA, hr12, hr13, hr14, hr8, hrbp, hrbx, hrdx, hcf, hof, ↓BitVec.ofNat_add_ofNat, ofNat_idx, BitVec.xor_self, BitVec.sub_self, BitVec.zero_sub]
  all_goals acct

end rind.x86_64.sqrx8x
