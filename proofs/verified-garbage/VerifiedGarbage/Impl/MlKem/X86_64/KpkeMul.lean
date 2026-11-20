module

public import VerifiedGarbage.Impl.MlKem.X86_64.KpkeAccY

/-!
# ML-KEM on x86-64: the products of K-PKE in one call

`vg_mlkem*_decrypt_mul(w = rdi, s = rsi, u = rdx, scratch = rcx)`
(`Proof/MlKem/KpkeMulContract.lean`) computes `NTT⁻¹(ŝ^⊺ ∘ NTT(u'))` with the code
of `vg_mlkem_ntt`, `vg_mlkem_multiply_ntts`, `vg_mlkem_add` and
`vg_mlkem_inv_ntt` (or their AVX2 versions, `Bodies`) inlined, rather than called, which is most of the cost of a call. It keeps `scratch` in `rbx`, `w` in
`rbp`, `ŝ[j]` in `r12`, `u'[j]` in `r13` and the count of the `k` terms
left in `r14`, and saves its caller's values of them (and of `r15`) at
`scratch + 3072`.
It sums the products in an accumulator at `w`, in the backend's own form
(`Bodies`): it sets up the table of the products (`Bodies.tab`) and zeroes
the accumulator; then for each `j`, it computes `NTT(u'[j])` to
`scratch + 1024` (`Bodies.nttO`: the NTT's code, but for the pointer its
last step stores through, `r10`) and adds its product with `ŝ[j]` to the
accumulator (`Bodies.mulAcc`); then `NTT⁻¹` of the accumulator, to `w`.
The code it inlines uses the first 1024 bytes of `scratch` as their
working space, and `scratch + 2048` and `scratch + 3328` for the products.

`vg_mlkem*_keygen_mul(t = rdi, s = rsi, a = rdx, e = rcx, scratch = r8)`
computes `ŝ = NTT(s)`, in place, and `t̂ = Â ∘ ŝ + NTT(e)` the same way, in
one MXCSR region. It keeps `scratch` in `rbx`, `ŝ` in `r12`, the row of `Â`
in `r13` and the count in `r14`. A first loop computes `NTT(s[j])` in place
and `NTT(e[j])` to `t[j]` (`nttK`, with `t[j]` in `rbp` and `e[j]` in
`r15`); then, for each row `i` (`rowK`, with `t[i]` in `r15`), it sums the
products `Â[i, j] ×_T ŝ[j]` in the accumulator at `scratch + 1024` (in
`rbp`), the first stored there (`Bodies.mulSet`) and the others added
(`Bodies.mulAcc`), and adds the sum to `t[i]` (`Bodies.fin`).

With AVX2, `encryptMulYg` and `Kpke16.dmInnerY` go row by row instead: a first
loop computes each `NTT(y[j])` (or `NTT(u'[j])`) to an accumulator at
`scratch + 1024 + 512 j` (`nttTermY`, with the next accumulator in `r9`);
then each output, from a row of products of those accumulators with the
polynomials of a column of `Â`, of `t̂` or of `ŝ` (`rowEY`), stored as an
accumulator in the output, and `NTT⁻¹` of it in place (`rowInvY`).

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- The code of the polynomial arithmetic of one backend, without the MXCSR
prologue and epilogue of its functions, around an accumulator of a sum of
products in a form of the backend's own: `u32`s with SSE2 (`Bodies.sse`),
words with AVX2 (`KpkeAccY.lean`). -/
structure Bodies where
  /-- `NTT` of the polynomial at `rdi` to the one at `r10`, with the working
  space at `rsi`. -/
  nttO : Prog isa
  /-- `NTT⁻¹` of the accumulator at `rdi`, to the polynomial at `rdi`, with
  the working space at `rsi`. -/
  inv : Prog isa
  /-- The accumulator at `rdi` of the zero polynomial. -/
  zero : Prog isa
  /-- Whatever `mulAcc` reads from `scratch = rcx + 3328` (256 bytes). -/
  tab : List Instr
  /-- The accumulator `o` at `rdi = rbp + 1024 o` plus `f = rsi ×_T g = rdx`,
  with the working space at `rcx` (1024 bytes) and at `rcx + 2048` (1024
  bytes), what `tab` left at `rcx + 3328`, and `rbx` equal to `rcx`. -/
  mulAcc : Nat → Prog isa
  /-- The polynomial at `rdi` plus the accumulator at `rsi`, to `rdi`. -/
  fin : Prog isa
  /-- The accumulator at `rdi` of `f = rsi ×_T g = rdx`, with what `mulAcc`
  has. -/
  mulSet : Prog isa
  /-- A row of `keygen_mul` of its own, if the backend has one: given `k`,
  the polynomial at `rdi` plus the sum of the `k` products of the
  polynomials from `rsi` and from `rdx` (1024 bytes apart), with what `tab`
  left at `rcx + 3328`; without one, the row goes through the accumulator
  (`mulSet`, `mulAcc`, `fin`). -/
  kgRow : Option (Nat → Prog isa)

/-- `vg_mlkem_ntt`'s code, storing to `r10`. -/
def nttOB : Prog isa :=
  .seq vpro (.seq (vlay vbfly 128 1 2) (.seq (vlay vbfly 64 2 2) (.seq (vlay vbfly 32 4 2)
    (.seq (vlay vbfly 16 8 2) (.seq (vlay vbfly 8 16 2) (.seq (vlay4 vbfly 32 0x50 4)
      (.seq (vlay2 vbfly 64 0xE4 8) (.seq (.block [.mov .rdi (.reg .r10)]) vepi))))))))

/-- `vg_mlkem_inv_ntt`'s code. -/
def nttInvB : Prog isa :=
  .seq vpro (.seq (vlay2 vibfly 124 0x1B (-8)) (.seq (vlay4 vibfly 62 0x05 (-4))
    (.seq (vlay vibfly 8 31 (-2)) (.seq (vlay vibfly 16 15 (-2)) (.seq (vlay vibfly 32 7 (-2))
      (.seq (vlay vibfly 64 3 (-2)) (.seq (vlay vibfly 128 1 (-2)) (.seq vscale vepi))))))))

/-- `vg_mlkem_multiply_ntts`'s code. -/
def mulB : Prog isa := .seq (.block [.mov .r10 (.reg .rcx)]) (.seq (.block mulPro) (rcxLoop 16 mulBody))

/-- The polynomial at `rdi`, zeroed, sixteen bytes at a time. -/
def zeroB : Prog isa :=
  .seq (.block [xb .pxor .xmm0 .xmm0]) (rcxLoop 64 [.movdquStore (at_ .rdi 0) .xmm0, .alu .add .rdi (.imm 16)])

/-- `rdi += rsi ×_T rdx`, for `rdi = rbp + 1024 o`: the product to `rcx + 2048`,
with `vg_mlkem_multiply_ntts`'s code, then added to `rdi` (from `rbp` again)
with `vg_mlkem_add`'s; `rbx` is `rcx` (`scratch`). -/
def mulAccB (o : Nat) : Prog isa :=
  .seq (.block (leaR .rdi .rcx 2048))
    (.seq mulB (.seq (.block ([.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * o)))] ++
      leaR .rsi .rbx 2048)) X86_64.add))

/-- `vg_mlkem_ntt_avx2`'s code, storing to `r10`. -/
def nttOBY : Prog isa := nttR NttR.passBsR10

def Bodies.sse : Bodies := ⟨nttOB, nttInvB, zeroB, [], mulAccB, X86_64.add, mulB, none⟩

def Bodies.avx2 : Bodies := ⟨nttOBY, nttInvAccY, zeroAccY, tabAccY, fun _ => mulAccY, finAccY, mulSetY, some rowY⟩

namespace KpkeMul

/-- The callee-saved registers and where in `scratch` they are saved (`rbx`,
through which they are loaded back, last). -/
def slots : List (Reg × Nat) := [(.rbp, 3072), (.r12, 3080), (.r13, 3088), (.r14, 3096), (.r15, 3104), (.rbx, 3112)]

/-- Save them through `rcx` (`scratch`). -/
def save : List Instr := slots.map fun p => .store (at_ .rcx p.2) p.1

/-- Load them back through `rbx` (`scratch`). -/
def restore : List Instr := slots.map fun p => .mov p.1 (.mem (at_ .rbx p.2))

/-- The table of the products, and the accumulator at `rbp` zeroed. -/
def start (B : Bodies) : Prog isa :=
  .seq (.block ([.mov .rcx (.reg .rbx)] ++ B.tab ++ [.mov .rdi (.reg .rbp)])) B.zero

/-- A term of the sum: `NTT(u'[j])` to `scratch + 1024`, and its product with
`ŝ[j]` added to the accumulator; then the next `j`. -/
def term (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbx), .alu .add .r10 (.imm 1024)])
    (.seq B.nttO (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .r12), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)])
    (.seq (B.mulAcc 0) (.block [.alu .add .r12 (.imm 1024), .alu .add .r13 (.imm 1024), .alu .sub .r14 (.imm 1)]))))


/-! ### `vg_mlkem*_encrypt_mul` -/

/-- A term of sum `o`: `f ×_T ŷ[j]`, with `f` at `rsi` (set by `fs`) and
`ŷ[j]` at `scratch + 1024`, added to the accumulator of `u[o]` (at
`rbp + 1024 o`). -/
def prodAcc (B : Bodies) (fs : List Instr) (o : Nat) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * o)))] ++ fs ++
      [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024), .mov .rcx (.reg .rbx)])) (B.mulAcc o)

/-- The terms `j` of the sums `i, …, i + n - 1` of `Â^⊺ ∘ ŷ`: `Â[j, i] ×_T ŷ[j]`, with row `j` of `Â`
at `r12`. -/
def innerE (B : Bodies) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, n + 1 => .seq (prodAcc B [.mov .rsi (.reg .r12), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * i)))] i)
    (innerE B (i + 1) n)

/-- The terms `j`: `ŷ[j] = NTT(y[j])` to `scratch + 1024`, those of the `k`
sums of `Â^⊺ ∘ ŷ`, and that of `t̂^⊺ ∘ ŷ` (`t̂[j]` at `r15`); then the next `j`. -/
def termE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbx), .alu .add .r10 (.imm 1024)])
    (.seq B.nttO (.seq (innerE B 0 k) (.seq (prodAcc B [.mov .rsi (.reg .r15)] k)
      (.block [.alu .add .r12 (.imm (BitVec.ofNat 32 (1024 * k))), .alu .add .r13 (.imm 1024),
        .alu .add .r15 (.imm 1024), .alu .sub .r14 (.imm 1)]))))

/-- `NTT⁻¹` of each of the `k + 1` sums. -/
def invE (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)])
    (.seq B.inv (.block [.alu .add .rbp (.imm 1024), .alu .sub .r15 (.imm 1)]))

/-- Save the callee-saved registers through `r8` (`scratch`). -/
def saveE : List Instr := slots.map fun p => .store (at_ .r8 p.2) p.1

/-- The accumulators of `u[i], …, u[i + n - 1]` (at `rbp + 1024 i`, …) zeroed. -/
def zeroE (B : Bodies) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | i, n + 1 => .seq (.seq (.block [.mov .rdi (.reg .rbp), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * i)))])
    B.zero) (zeroE B (i + 1) n)

/-- The table of the products, and the `k + 1` accumulators zeroed. -/
def startE (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block ([.mov .rcx (.reg .rbx)] ++ B.tab)) (zeroE B 0 (k + 1))

/-! ### `vg_mlkem*_keygen_mul` -/

/-- `NTT(s[j])` in place (at `r12`) and `NTT(e[j])` (at `r15`, by `nttE`,
`se` bytes apart) to `t[j]` (at `rbp`); then the next `j`. -/
def nttKg (B : Bodies) (nttE : Prog isa) (se : BitVec 32) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r12), .mov .rsi (.reg .rbx), .mov .r10 (.reg .r12)])
    (.seq B.nttO (.seq (.block [.mov .rdi (.reg .r15), .mov .rsi (.reg .rbx), .mov .r10 (.reg .rbp)])
      (.seq nttE (.block [.alu .add .r12 (.imm 1024), .alu .add .r15 (.imm se), .alu .add .rbp (.imm 1024),
        .alu .sub .r14 (.imm 1)]))))

/-- `nttKg` of `e` as `u32`s. -/
def nttK (B : Bodies) : Prog isa := nttKg B B.nttO 1024

/-- `nttKg` with AVX2, of `e` as `u16`s. -/
def nttK16 : Prog isa := nttKg Bodies.avx2 (nttR16 NttR.passBsR10) 512

/-- Term `j` of row `i`: `Â[i, j] ×_T ŝ[j]`, with row `i` of `Â` at `r13` and
`ŝ` at `r12`, added to the accumulator at `rbp`. -/
def prodK (B : Bodies) (j : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * j))),
      .mov .rdx (.reg .r12), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * j))), .mov .rcx (.reg .rbx)])
    (B.mulAcc 0)

/-- Term `0` of row `i`, stored to the accumulator. -/
def prodSetK (B : Bodies) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .r13), .mov .rdx (.reg .r12), .mov .rcx (.reg .rbx)]) B.mulSet

/-- The terms `j, …, j + n - 1` of a row. -/
def innerK (B : Bodies) : Nat → Nat → Prog isa
  | _, 0 => .block []
  | j, n + 1 => .seq (prodK B j) (innerK B (j + 1) n)

/-- Row `i`: the first term stored to the accumulator, the other `k - 1`
added, and the sum added to `t[i] = NTT(e[i])` (at `r15`); then the next
`i`. -/
def rowK (B : Bodies) (k : Nat) : Prog isa :=
  .seq (prodSetK B) (.seq (innerK B 1 (k - 1))
    (.seq (.seq (.block [.mov .rdi (.reg .r15), .mov .rsi (.reg .rbp)]) B.fin)
      (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 (1024 * k))), .alu .add .r15 (.imm 1024),
        .alu .sub .r14 (.imm 1)])))

/-- `rowKR` with the polynomials of a row of `Â` `ra` bytes apart. -/
def rowKRs (r : Nat → Prog isa) (k ra : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r15), .mov .rsi (.reg .r13), .mov .rdx (.reg .r12), .mov .rcx (.reg .rbx)])
    (.seq (r k) (.block [.alu .add .r13 (.imm (BitVec.ofNat 32 (ra * k))), .alu .add .r15 (.imm 1024),
      .alu .sub .r14 (.imm 1)]))

/-- Row `i` with the backend's own row `r`: `t[i]` (at `r15`) plus the
products of row `i` of `Â` (at `r13`) and `ŝ` (at `r12`); then the next
`i`. -/
def rowKR (r : Nat → Prog isa) (k : Nat) : Prog isa := rowKRs r k 1024

/-- Row `i` of `keygen_mul`: the backend's own row, or through the
accumulator. -/
def rowOf (B : Bodies) (k : Nat) : Prog isa :=
  match B.kgRow with
  | some r => rowKR r k
  | none => rowK B k

/-- Between the loops: `ŝ` at `r12` and `t` at `r15` again, the accumulator
at `rbp = scratch + 1024`, and the table of the products. -/
def midK (B : Bodies) (k : Nat) : List Instr :=
  [.alu .sub .r12 (.imm (BitVec.ofNat 32 (1024 * k))), .mov .r15 (.reg .rbp),
    .alu .sub .r15 (.imm (BitVec.ofNat 32 (1024 * k))), .mov .rbp (.reg .rbx), .alu .add .rbp (.imm 1024),
    .mov .rcx (.reg .rbx)] ++ B.tab ++ [.mov32 .r14 (.imm (BitVec.ofNat 32 k))]

/-! ### `encrypt_mul` and `decrypt_mul` row by row, with AVX2 -/

/-- `NTT` of the polynomial at `rdi` to the accumulator at `r10`, with `S` at
`rsi + oS`. -/
def nttAccY : Prog isa := nttR NttR.passBsAccR10

/-- `nttAccY` of the polynomial of `u16`s at `rdi`. -/
def nttAccY16 : Prog isa := nttR16 NttR.passBsAccR10

/-- `NTT` (the code `ntt`) of the next polynomial (at `r13`, `sy` bytes
apart) to the next accumulator (at `r9`). -/
def nttTermYg (ntt : Prog isa) (sy : BitVec 32) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r13), .mov .rsi (.reg .rbx), .mov .r10 (.reg .r9)])
    (.seq ntt (.block [.alu .add .r13 (.imm sy), .alu .add .r9 (.imm 512), .alu .sub .r14 (.imm 1)]))

/-- `nttTermYg` of polynomials of `u32`s. -/
def nttTermY : Prog isa := nttTermYg nttAccY 1024

/-- `nttTermYg` of polynomials of `u16`s. -/
def nttTermY16 : Prog isa := nttTermYg nttAccY16 512

/-- The table of the products, and `r9` at the first accumulator, at
`scratch + 1024`. -/
def startY : List Instr :=
  [.mov .rcx (.reg .rbx)] ++ tabAccY ++ [.mov .r9 (.reg .rbx), .alu .add .r9 (.imm 1024)]

/-- The polynomial at `rbp`: `NTT⁻¹` of the `k` products of the polynomials
from `f` (`fs`), `o` bytes apart, and the accumulators from
`scratch + 1024`. -/
def rowInvYg (fs : List Instr) (row : Prog isa) : Prog isa :=
  .seq (.block ([.mov .rdi (.reg .rbp)] ++ fs ++ [.mov .rdx (.reg .rbx), .alu .add .rdx (.imm 1024),
      .mov .rcx (.reg .rbx)]))
    (.seq row (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)]) nttInvAccY))

/-- `rowInvYg` of the polynomials of `u32`s from `f`, `o` bytes apart. -/
def rowInvY (fs : List Instr) (o k : Nat) : Prog isa := rowInvYg fs (rowEY o k)

/-- Row `i < k` of `encrypt_mul` with the row of products `row`: `u[i]` (at
`rbp`) from column `i` of `Â` (at `r12`, whose columns are `sa` bytes
apart); then the next `i`. -/
def rowAYg (row : Prog isa) (sa : BitVec 32) : Prog isa :=
  .seq (rowInvYg [.mov .rsi (.reg .r12)] row)
    (.block [.alu .add .rbp (.imm 1024), .alu .add .r12 (.imm sa), .alu .sub .r14 (.imm 1)])

/-- `rowAYg` of `Â` as `u16`s. -/
def rowAY16 (k : Nat) : Prog isa := rowAYg (rowEY16 (512 * k) k) 512

end KpkeMul

open KpkeMul in
/-- `encrypt_mul` with AVX2, with the `NTT`s of `y` computed by `term` and the
rows of `Â` by `rowA`: `ŷ[j] = NTT(y[j])` to the accumulators at
`scratch + 1024 + 512 j`, then each `u[i]`, and `v`, from them in one row of
products and `NTT⁻¹`. -/
def encryptMulYg (term rowA : Prog isa) (k : Nat) : Prog isa :=
  .seq (.block (saveE ++ [.mov .rbx (.reg .r8), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rcx),
      .mov .r15 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (.seq (.block startY) (.seq (.loop term .ne)
      (.seq (.block [.mov32 .r14 (.imm (BitVec.ofNat 32 k))]) (.seq (.loop rowA .ne)
        (rowInvY [.mov .rsi (.reg .r15)] 1024 k)))))
    (.block restore))

open KpkeMul in
/-- `encryptMulYg` reading `Â` as `k²` polynomials of `u16`s (`rowEY16`) and
`y` as `k` of `u16`s (`nttTermY16`). -/
def encryptMul16Y (k : Nat) : Prog isa := encryptMulYg nttTermY16 (rowAY16 k) k

open KpkeMul in
/-- `vg_mlkem*_keygen_mul` of rank `k`, with the code of `B`, the `NTT`s of
`s` and `e` by `term` and the rows `row`. -/
def keygenMulg (term row : Prog isa) (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (saveE ++ [.mov .rbx (.reg .r8), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx),
      .mov .r15 (.reg .rcx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (.seq (.loop term .ne) (.seq (.block (midK B k)) (.loop row .ne)))
    (.block restore))

open KpkeMul in
/-- `vg_mlkem*_keygen_mul` of rank `k`, with the code of `B`. -/
def keygenMul (B : Bodies) (k : Nat) : Prog isa := keygenMulg (nttK B) (rowOf B k) B k

open KpkeMul in
/-- `keygenMul` with AVX2, reading `Â` as `k²` polynomials of `u16`s (`rowY16`)
and `e` as `k` (`nttK16`). -/
def keygenMul16Y (k : Nat) : Prog isa := keygenMulg nttK16 (rowKRs rowY16 k 512) Bodies.avx2 k

open KpkeMul in
/-- `vg_mlkem*_decrypt_mul` of rank `k`, with the code of `B`. -/
def decryptMul (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (save ++ [.mov .rbx (.reg .rcx), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx),
      .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (.seq (start B) (.seq (.loop (term B) .ne)
      (.seq (.block [.mov .rdi (.reg .rbp), .mov .rsi (.reg .rbx)]) B.inv)))
    (.block restore))

open KpkeMul in
/-- `vg_mlkem*_encrypt_mul` of rank `k`, with the code of `B`. -/
def encryptMul (B : Bodies) (k : Nat) : Prog isa :=
  .seq (.block (saveE ++ [.mov .rbx (.reg .r8), .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rcx),
      .mov .r15 (.reg .rdx), .mov32 .r14 (.imm (BitVec.ofNat 32 k))]))
    (.seq (.seq (startE B k) (.seq (.loop (termE B k) .ne)
      (.seq (.block [.mov32 .r15 (.imm (BitVec.ofNat 32 (k + 1)))]) (.loop (invE B) .ne))))
    (.block restore))

end VG.Impl.MlKem.X86_64
