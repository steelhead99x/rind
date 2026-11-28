/-- `[b + d]` -/
def m (b : Reg) (d : Int) : MemOp := { base := b, disp := d }

/-- `[b + i + d]` -/
def mi (b i : Reg) (d : Int) : MemOp := { base := b, index := some i, disp := d }

/-- `d` bytes past the static of constants, RIP-relative. -/
def k (d : Int) : SymOp := { name := constsName, disp := d }

/-- An SSE instruction. -/
def x (o : XOp) : Instr := .vg (.xop o)

/-- An AVX instruction. -/
def v (o : VOp) : Instr := .vg (.vop o)

/-- The programs in order. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [a] => a
  | a :: r => .seq a (seqs r)

