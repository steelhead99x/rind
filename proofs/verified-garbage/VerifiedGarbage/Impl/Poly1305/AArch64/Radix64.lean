module

public import VerifiedGarbage.Impl.Poly1305.AArch64

/-!
# Poly1305 radix-64 arithmetic on AArch64

The accumulator occupies x4:x5:x6, the clamped key x7:x8, and 5*x8/4
is kept in x17. x9–x16 are temporary registers. The canonical 128-byte
state and all pointer/length registers x0–x3 are unchanged.
-/

@[expose] public section

namespace VG.Impl.Poly1305.AArch64.Radix64
open VG.AArch64

def setup : List Instr :=
  const64 .x16 0x0ffffffc0fffffff ++
  ([.ldr .x .x7 .x0 24, .logic .and .x .x7 .x7 .x16] : List Instr) ++
  const64 .x16 0x0ffffffc0ffffffc ++
  ([.ldr .x .x8 .x0 32, .logic .and .x .x8 .x8 .x16,
   .lsr .x .x17 .x8 2, .add .x .x17 .x17 .x8,
   .ldr .x .x4 .x0 0, .ldr .x .x5 .x0 8, .ldr .x .x6 .x0 16] : List Instr)

/-- A two-word product, where neither destination aliases an input. -/
def mulTo (lo hi a b : Reg) : List Instr :=
  [.mul .x lo a b, .umulh hi a b]

/-- A product added to a two-word accumulator. Its high carry is dead, so ADC avoids writing flags. -/
def mulAdd (lo hi a b : Reg) : List Instr :=
  [.mul .x .x13 a b, .umulh .x14 a b, .adds .x lo lo .x13, .adc .x hi hi .x14]

/-- A product known to fit one word added to a two-word accumulator. -/
def mulAddSmall (lo hi a b : Reg) : List Instr :=
  [.mul .x .x13 a b, .movz .x .x14 0 0, .adds .x lo lo .x13, .adc .x hi hi .x14]

def addBlock (pad : Bool) : List Instr :=
  [.ldr .x .x13 .x1 0, .ldr .x .x14 .x1 8, .movz .x .x15 (if pad then 1 else 0) 0,
   .adds .x .x4 .x4 .x13, .adcs .x .x5 .x5 .x14, .adc .x .x6 .x6 .x15]

def products : List Instr :=
  mulTo .x9 .x10 .x4 .x7 ++ mulAdd .x9 .x10 .x5 .x17 ++
  mulTo .x11 .x12 .x4 .x8 ++ mulAdd .x11 .x12 .x5 .x7 ++
  mulAddSmall .x11 .x12 .x6 .x17 ++ ([.mul .x .x13 .x6 .x7] : List Instr)

/-- Combine the two wide products and the small product into three words. -/
def combine : List Instr := [.adds .x .x11 .x11 .x10, .adc .x .x12 .x12 .x13]

/-- Fold the high word t into t mod 4 and 5*(t/4) = (t & ~3) + (t >> 2), whose
two terms are computed side by side (one step shorter than `t - (t & 3)`). -/
def fold : List Instr :=
  [.addImm .x .x4 .x9 0, .addImm .x .x5 .x11 0,
   .movz .x .x14 3 0, .bicRor .x .x13 .x12 .x14 0, .logic .and .x .x6 .x12 .x14,
   .lsr .x .x12 .x12 2, .add .x .x13 .x13 .x12]

def addLow : List Instr :=
  [.movz .x .x14 0 0, .adds .x .x4 .x4 .x13, .adcs .x .x5 .x5 .x14,
   .adc .x .x6 .x6 .x14]

def absorb (pad : Bool) : List Instr := addBlock pad ++ products ++ combine ++ fold ++ addLow

def plus5 : List Instr :=
  [.movz .x .x13 5 0, .movz .x .x14 0 0, .adds .x .x9 .x4 .x13,
   .adcs .x .x10 .x5 .x14, .adc .x .x11 .x6 .x14]

def mask : List Instr :=
  [.lsr .x .x12 .x11 2, .movz .x .x14 0 0, .sub .x .x12 .x14 .x12,
   .movz .x .x14 3 0, .logic .and .x .x11 .x11 .x14]

def selectLimb (h g : Reg) : List Instr :=
  [.logic .eor .x .x13 g h, .logic .and .x .x13 .x13 .x12, .logic .eor .x h h .x13]

def reduce : List Instr := plus5 ++ mask ++
  selectLimb .x4 .x9 ++ selectLimb .x5 .x10 ++ selectLimb .x6 .x11

def storeH : List Instr := [.str .x .x4 .x0 0, .str .x .x5 .x0 8, .str .x .x6 .x0 16]

def blocks : Prog isa :=
  .seq (.block setup)
    (.seq (.ite (.zero .x .x2) (.block [])
      (.loop (.block (absorb true ++ advance)) (.nonzero .x .x2)))
      (.block (reduce ++ storeH)))

def fill : Prog isa :=
  .seq count
  (.seq (.ite (.zero .x .x10) (.block []) copyIn)
  (.seq (.block [.addImm .x .x2 .x1 0, .subImm .x .x12 .x9 16])
    (.ite (.zero .x .x12) (.block (([.addImm .x .x1 .x0 56] : List Instr) ++ absorb true)) (.block []))))

/-- Absorbs the whole blocks of the data, from `x1`, counting them in `x2`. -/
def whole : Prog isa :=
  .seq (.block [.addImm .x .x1 .x2 0, .lsr .x .x2 .x3 4])
    (.ite (.zero .x .x2) (.block [])
      (.loop (.block (absorb true ++ ([.addImm .x .x1 .x1 16, .subImm .x .x3 .x3 16,
        .lsr .x .x2 .x3 4] : List Instr))) (.nonzero .x .x2)))

/-- Copies the rest of the data into the (empty) buffer. -/
def rest : Prog isa :=
  .ite (.zero .x .x3) (.block [])
    (.seq (.block [.addImm .x .x10 .x3 0, .addImm .x .x11 .x0 0]) copyIn)

def update : Prog isa :=
  .seq (.block (setup ++ ([.movz .x .x9 15 0, .logic .and .x .x9 .x1 .x9] : List Instr)))
  (.seq (.ite (.zero .x .x9) (.block []) fill)
  (.seq whole
  (.seq rest
    (.block (reduce ++ storeH)))))

def lastBlock : Prog isa :=
  .seq (.block [.movz .x .x11 0 0, .add .x .x9 .x0 .x2, .movz .x .x10 16 0, .sub .x .x10 .x10 .x2])
  (.seq (.loop (.block zeroBody) (.nonzero .x .x10))
    (.block (([.movz .x .x11 1 0, .add .x .x9 .x0 .x2, .strb .x11 .x9 56, .addImm .x .x1 .x0 56] : List Instr) ++
      absorb false)))

def addS : List Instr :=
  [.ldr .x .x13 .x0 40, .ldr .x .x14 .x0 48, .adds .x .x4 .x4 .x13,
   .adc .x .x5 .x5 .x14]

def storeTag : List Instr := [.str .x .x4 .x3 0, .str .x .x5 .x3 8]

def finalize : Prog isa :=
  .seq (.block (([.addImm .x .x3 .x2 0, .movz .x .x2 15 0, .logic .and .x .x2 .x1 .x2] : List Instr) ++ setup))
  (.seq (.ite (.zero .x .x2) (.block []) lastBlock)
    (.block (reduce ++ addS ++ storeTag)))

end VG.Impl.Poly1305.AArch64.Radix64
