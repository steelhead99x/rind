module

public import VerifiedGarbage.Impl.Weierstrass.X86_64.NafPrep

/-! Public width-five/seven/nine recoding, skipping known zero digits: bytes for widths five
and seven, sixteen-bit words for nine. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.FastNaf
open VG VG.X86_64 VG.Impl.Mont.X86_64

def shift (w : Nat) : List Instr :=
  [.shift .shr .r8 w,.mov .rax (.reg .r9),.shift .shl .rax (64-w),.alu .or .r8 (.reg .rax),
   .shift .shr .r9 w,.mov .rax (.reg .r10),.shift .shl .rax (64-w),.alu .or .r9 (.reg .rax),
   .shift .shr .r10 w,.mov .rax (.reg .r11),.shift .shl .rax (64-w),.alu .or .r10 (.reg .rax),
   .shift .shr .r11 w,.mov .rax (.reg .r12),.shift .shl .rax (64-w),.alu .or .r11 (.reg .rax),
   .shift .shr .r12 w]

/-- The scalar's registers shifted right by `w` bits, through `rax`. -/
def shiftN (n w : Nat) : List Instr :=
  let rs := Naf.sregs n
  (rs.zip rs.tail).flatMap (fun (a, b) =>
    [.shift .shr a w,.mov .rax (.reg b),.shift .shl .rax (64-w),.alu .or a (.reg .rax)]) ++
  [.shift .shr (Naf.stop n) w]

def choose (w : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm (BitVec.ofNat 32 (2^w-1))),
    .alu .cmp .rcx (.imm (BitVec.ofNat 32 (2^(w-1))))])
    (.ite .b (.block []) (.block [.alu .sub .rcx (.imm (BitVec.ofNat 32 (2^w)))]))

def advance (w : Nat) : List Instr := [.alu .add .rbx (.imm (BitVec.ofNat 32 w))]

/-- A step of the recoding for a scalar of `n` words: `64 n + 1` digits. -/
def stepN (n dst w : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)]) <|
  .seq (.ite .e (.block (shiftN n 1++advance 1))
    (.seq (choose w) (.block (Naf.subtractDigitN n++[.store8 (tbl dst) .rcx]++shiftN n w++advance w))))
    (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))])

/-- The digits of a scalar of `n` words, into `8 n + 1` zeroed words at `dst`. -/
def prepN (n src dst w : Nat) : Prog isa :=
  .seq (.block (Naf.initN n src++setConst (8*n+1) dst 0)) (.loop (stepN n dst w) .b)

/-- The digits as sixteen-bit words, indexed by `rbx`. -/
def tbl16 (d : Nat) : MemOp := { base := .rdi, index := some .rbx, scale := 2, disp := d }

/-- `stepN` for width nine, storing each digit as a sixteen-bit word. -/
def stepN16 (n dst : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)]) <|
  .seq (.ite .e (.block (shiftN n 1++advance 1))
    (.seq (choose 9) (.block (Naf.subtractDigitN n++[.store16 (tbl16 dst) .rcx]++shiftN n 9++advance 9))))
    (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))])

/-- The width-nine digits of a scalar of `n` words, into `16 n + 1` zeroed words at `dst`. -/
def prepN16 (n src dst : Nat) : Prog isa :=
  .seq (.block (Naf.initN n src++setConst (16*n+1) dst 0)) (.loop (stepN16 n dst) .b)

/-! ### Without branches on the scalar's bits (BMI2)

`stepN` takes a branch on each bit that is not skipped and on each digit's sign, which the processor
cannot predict for a scalar it has not seen. `stepB` does the same to the scalar and to the table
with neither, for the widths five and nine. On an Intel Xeon (Emerald Rapids),
`vg_ecdsa_p256_verify_ifma` with it took 1.4% less time over different signatures in turn, and 0.7%
more over one signature again and again, whose branches the processor learns. -/

/-- The scalar's registers shifted right by the count in `rdx`, which is from 1 to 63, with 64 less
that count in `rcx`, through `rax`. -/
def shiftV (n : Nat) : List Instr :=
  let rs := Naf.sregs n
  (rs.zip rs.tail).flatMap (fun (a, b) =>
    [.shiftx .shrx a a .rdx, .shiftx .shlx .rax b .rcx, .alu .or a (.reg .rax)]) ++
  [.shiftx .shrx (Naf.stop n) (Naf.stop n) .rdx]

/-- `rcx`: the scalar's signed digit of `w` bits if the scalar is odd, zero if it is even. -/
def digitB (w : Nat) : List Instr :=
  [.mov .rcx (.reg .r8), .alu .and .rcx (.imm (BitVec.ofNat 32 (2^w-1))),
   .alu .xor .rcx (.imm (BitVec.ofNat 32 (2^(w-1)))), .alu .sub .rcx (.imm (BitVec.ofNat 32 (2^(w-1)))),
   .mov .rax (.reg .r8), .alu .and .rax (.imm 1), .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax),
   .alu .and .rcx (.reg .rdx)]

/-- From the digit in `rcx`, which is odd or zero: in `rdx`, how far the scalar is shifted, `1 + 2^e`
(the width, for `e` two or three) after a digit that is odd and one after zero; in `rcx`, 64 less that. -/
def countB (e : Nat) : List Instr :=
  [.alu .and .rcx (.imm 1), .mov .rdx (.reg .rcx), .shift .shl .rdx e, .alu .add .rdx (.imm 1),
   .mov32 .rcx (.imm 64), .alu .sub .rcx (.reg .rdx)]

/-- `stepN` for width five, without branches but the loop's: the digit or zero stored, and the scalar
shifted by five or one. -/
def stepB (n dst : Nat) : Prog isa :=
  .block (digitB 5 ++ (Naf.subtractDigitN n ++ ([.store8 (tbl dst) .rcx] ++ (countB 2 ++ (shiftV n ++
    [.alu .add .rbx (.reg .rdx), .alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))])))))

/-- `prepN` for width five, by `stepB`. -/
def prepB (n src dst : Nat) : Prog isa :=
  .seq (.block (Naf.initN n src++setConst (8*n+1) dst 0)) (.loop (stepB n dst) .b)

/-- `stepN16`, without branches but the loop's. -/
def stepB16 (n dst : Nat) : Prog isa :=
  .block (digitB 9 ++ (Naf.subtractDigitN n ++ ([.store16 (tbl16 dst) .rcx] ++ (countB 3 ++ (shiftV n ++
    [.alu .add .rbx (.reg .rdx), .alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))])))))

/-- `prepN16`, by `stepB16`. -/
def prepB16 (n src dst : Nat) : Prog isa :=
  .seq (.block (Naf.initN n src++setConst (16*n+1) dst 0)) (.loop (stepB16 n dst) .b)

end VG.Impl.Weierstrass.X86_64.FastNaf
