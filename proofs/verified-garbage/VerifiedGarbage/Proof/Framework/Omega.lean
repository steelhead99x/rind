module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Closure
public meta import Lean.Meta.Tactic.Assert
public meta import Lean.Meta.Tactic.Clear

/-!
# `omega` in large contexts

Untrusted: this only changes how proofs are found.

`omega` and `bv_omega` use every hypothesis in the local context (`bv_omega`
first rewrites every one of them with `simp … at *`). In the middle of a long
proof about machine states most hypotheses are facts about memory, regions
or states that they cannot use, and looking at them costs a tenth of a second
or more per call; and preprocessing each fact about `/` and `%` introduces
new variables and constraints, which every call pays for and the kernel
checks. Two ways to run them on less:

* `omega_arith` selects (in)equations between natural numbers, integers or
  bit vectors, and propositional combinations of them, that are connected to
  the goal (see `relevantFacts`). It tries smaller problems first, since the
  kernel's check of an `omega` certificate grows with every fact in it: the
  facts sharing an atom with the goal, then those within two steps of it, then
  every connected fact. `bv_omega_arith`
  clears other hypotheses before preprocessing;
* `omega_using [h₁, …, hₙ]` and `bv_omega_using [h₁, …, hₙ]` use only the
  facts `h₁, …, hₙ` (any terms). `omega_using` passes them directly to
  the solver; `bv_omega_using` clears other hypotheses before preprocessing.

Both first try to close the goal without `omega` (`Abs.close`). The goal and the facts
are restated over variables, `∀ x₁ … xₙ, F₁ → … → Fₖ → G`, with a variable for each term
that is not arithmetic (with what `omega` knows of such a term by its shape: `x.toNat < 2 ^ w`,
`↑i < n`), and that statement is proven by `VG.Arith.prove?` as an auxiliary theorem, which
serves every goal of its shape in the declaration. Where that does not prove it, they go
on as they did before, with `omega` on the goal itself.

## `VG.Arith`: linear arithmetic that the kernel checks quickly

The kernel takes ten milliseconds or more to check an `omega` certificate for a typical
goal of these proofs, whatever the size of the terms in it: it evaluates `omega`'s own
normalization of every fact, on lists of integers. `VG.Arith.prove?` proves goals of
the same kind (linear equations and inequalities over `Nat`, with `/` and `%` by
numerals, `-`, and `¬`, `∧`, `∨`, `→`, `↔`) by terms the kernel checks by applying
lemmas, in about a millisecond, and finds them faster than `omega` does:

* each side of each fact is put in a normal form, `M a₁ x₁ (M a₂ x₂ (… k))` for
  `a₁ * x₁ + (a₂ * x₂ + (… + k))` with the atoms in a fixed order, by one lemma for each
  `+` and `*` of the term (`ad`, `mu`, `mur`) and one for each monomial that merging two
  forms moves (`mm`, `ml`, `mr`, `sm`). The coefficients stay unevaluated sums and
  products of numerals (`Nat.add`, `Nat.mul`);
* `x / k`, `x % k` and `x - y` are atoms, with the facts that define them (`dv1`, `dv2`,
  `md1`, `md2`, `sub_cases`);
* the facts, the negated goal and `0 ≤ x` for every atom are combined by Fourier–Motzkin
  elimination, rounding where every coefficient has a common divisor (`fm`). That search
  runs here, untrusted; its derivation is replayed on the normal forms by `sc`, `pl` and
  `cut`;
* the result is a fact `L ≤ R` whose left side has the larger coefficients and the larger
  constant, which `zs`, `zl` and `zk` refute. Only there does the kernel evaluate the
  coefficients: one comparison of numerals for each atom;
* a case split (`∨`, `≠`, `-`, `↔`, `→`) is an `Or.elim`, with a derivation for each case.

It gives up, and `omega` runs, on what it does not read (integers, `min`, a product of
two terms that are not numerals is an atom) and where the search needs more than rounding.
-/

public section

namespace VG.Arith

/-! ### Normal forms -/

/-- A monomial in front of the rest of a linear form: `a * x + r`. -/
def M (a x r : Nat) : Nat := a * x + r

/-! The sum of two forms (`kk`, `mm`, `ml`, `mr`) and a numeral times a form (`sk`, `sm`,
`zm`), one monomial at a time; an atom (`atm`); and the form of a term from those of its
parts (`ad`, `mu`, `mur`, `su`). -/

theorem kk (k l : Nat) : k + l = Nat.add k l := rfl
theorem mm {a b x r s t : Nat} (h : r + s = t) : M a x r + M b x s = M (Nat.add a b) x t := by
  subst h; simp only [M, Nat.add_eq, Nat.add_mul]; omega
theorem ml {a x r S t : Nat} (h : r + S = t) : M a x r + S = M a x t := by
  subst h; simp only [M]; omega
theorem mr {R b y s t : Nat} (h : R + s = t) : R + M b y s = M b y t := by
  subst h; simp only [M]; omega
theorem sk (c k : Nat) : c * k = Nat.mul c k := rfl
theorem sm {c a x r t : Nat} (h : c * r = t) : c * M a x r = M (Nat.mul c a) x t := by
  subst h; simp only [M, Nat.mul_eq, Nat.mul_add, Nat.mul_assoc]
theorem zm (t : Nat) : nat_lit 0 * t = nat_lit 0 := Nat.zero_mul t
theorem atm (x : Nat) : x = M (nat_lit 1) x (nat_lit 0) := by
  show x = 1 * x + 0; omega
theorem ad {s t Fs Ft F : Nat} (hs : s = Fs) (ht : t = Ft) (hm : Fs + Ft = F) : s + t = F := by
  subst hs ht; exact hm
theorem mu {c c' t Ft F : Nat} (hc : c = c') (ht : t = Ft) (hm : c' * Ft = F) : c * t = F := by
  subst hc ht; exact hm
theorem mur {c c' t Ft F : Nat} (hc : c = c') (ht : t = Ft) (hm : c' * Ft = F) : t * c = F := by
  subst hc ht; rw [Nat.mul_comm]; exact hm
theorem su {t Ft F : Nat} (ht : t = Ft) (hm : Ft + nat_lit 1 = F) : Nat.succ t = F := by
  subst ht; exact hm
/-! A fact about terms, as a fact `L ≤ R` about their forms. -/

theorem fle {l r L R : Nat} (hl : l = L) (hr : r = R) (h : l ≤ r) : L ≤ R := hl ▸ hr ▸ h
theorem flt {l r L R L' : Nat} (hl : l = L) (hr : r = R) (hm : L + nat_lit 1 = L') (h : l < r) : L' ≤ R := by
  subst hl hr hm; exact h
theorem fnle {l r L R R' : Nat} (hl : l = L) (hr : r = R) (hm : R + nat_lit 1 = R') (h : ¬ l ≤ r) : R' ≤ L := by
  subst hl hr hm; exact Nat.lt_of_not_le h
theorem fnlt {l r L R : Nat} (hl : l = L) (hr : r = R) (h : ¬ l < r) : R ≤ L := by
  subst hl hr; exact Nat.le_of_not_lt h
theorem feq1 {l r L R : Nat} (hl : l = L) (hr : r = R) (h : l = r) : L ≤ R := by
  subst hl hr; exact Nat.le_of_eq h
theorem feq2 {l r L R : Nat} (hl : l = L) (hr : r = R) (h : l = r) : R ≤ L := by
  subst hl hr; exact Nat.le_of_eq h.symm
theorem ne_cases {l r : Nat} (h : l ≠ r) : l < r ∨ r < l := Nat.lt_or_gt_of_ne h
/-! Derivations: a numeral times a fact (`sc`), the sum of two (`pl`), and a fact whose
coefficients all have the divisor `g`, divided by it with its constants rounded (`cut`: `D`
is what makes the coefficients of both sides multiples of `g`). -/

theorem sc {L R L' R' : Nat} (c : Nat) (h : L ≤ R) (hl : c * L = L') (hr : c * R = R') : L' ≤ R' := by
  subst hl hr; exact Nat.mul_le_mul_left c h
theorem pl {L₁ R₁ L₂ R₂ L R : Nat} (h₁ : L₁ ≤ R₁) (h₂ : L₂ ≤ R₂) (hl : L₁ + L₂ = L) (hr : R₁ + R₂ = R) :
    L ≤ R := by
  subst hl hr; exact Nat.add_le_add h₁ h₂
/-! The end of a derivation: `L ≤ R` is absurd when `L` has the larger coefficients (`zs`,
and `zl` for an atom only `L` has) and the larger constant (`zk`). The kernel evaluates
the comparisons. -/

theorem zs {a b x r s : Nat} (c : Nat.ble b a = true) (h : M a x r ≤ M b x s) : r ≤ s := by
  have := Nat.mul_le_mul_right x (Nat.le_of_ble_eq_true c); simp only [M] at h; omega
theorem zl {a x r S : Nat} (h : M a x r ≤ S) : r ≤ S := by simp only [M] at h; omega
theorem zk {k l : Nat} (c : Nat.ble (Nat.add l (nat_lit 1)) k = true) (h : k ≤ l) : False := by
  have := Nat.le_of_ble_eq_true c; simp only [Nat.add_eq] at this; omega
theorem nn (p : Prop) (h : ¬¬p) : p := Classical.not_not.mp h
theorem nand (a b : Prop) (h : ¬(a ∧ b)) : ¬a ∨ ¬b := Classical.not_and_iff_not_or_not.mp h
/-! What holds of every atom (`sl`), of `a - b` (`sub_cases`), `a / k` (`dv1`, `dv2`) and
`a % k` (`md1`, `md2`); and the cases of a proposition (`ne_cases`, `nn`, `nand`, `iffc`,
`niffc`, `impc`, `nimp`). -/

theorem sl (x : Nat) : nat_lit 0 ≤ M (nat_lit 1) x (nat_lit 0) := Nat.zero_le _
theorem cut {L R D X Y L' R' L'' R'' : Nat} (g kl kr q p : Nat) (h : L ≤ R)
    (hl : L + D = X) (hl' : g * L' + kl = X) (hr : R + D = Y) (hr' : g * R' + kr = Y)
    (c : Nat.ble (g * q + kr) (kl + g * p + (g - 1)) = true)
    (hg : Nat.ble 1 g = true) (hml : L' + q = L'') (hmr : R' + p = R'') : L'' ≤ R'' := by
  have c := Nat.le_of_ble_eq_true c
  have hg := Nat.le_of_ble_eq_true hg
  subst hml hmr
  have h1 : g * L' + kl ≤ g * R' + kr := by omega
  have h2 : g * (L' + q) < g * (R' + p + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]; omega
  have := Nat.lt_of_mul_lt_mul_left h2
  omega
theorem iffc (a b : Prop) (h : a ↔ b) : (a ∧ b) ∨ (¬a ∧ ¬b) := by
  cases Classical.em a with
  | inl ha => exact Or.inl ⟨ha, h.mp ha⟩
  | inr ha => exact Or.inr ⟨ha, fun hb => ha (h.mpr hb)⟩
theorem niffc (a b : Prop) (h : ¬(a ↔ b)) : (a ∧ ¬b) ∨ (¬a ∧ b) := by
  cases Classical.em a with
  | inl ha => exact Or.inl ⟨ha, fun hb => h ⟨fun _ => hb, fun _ => ha⟩⟩
  | inr ha => exact Or.inr ⟨ha, Classical.byContradiction fun hb => h ⟨fun x => absurd x ha, fun x => absurd x hb⟩⟩
theorem impc (a b : Prop) (h : a → b) : ¬a ∨ b := by
  cases Classical.em a with
  | inl ha => exact Or.inr (h ha)
  | inr ha => exact Or.inl ha
theorem nimp (a b : Prop) (h : ¬(a → b)) : a ∧ ¬b :=
  ⟨Classical.byContradiction fun ha => h fun x => absurd x ha, fun hb => h fun _ => hb⟩
theorem sub_cases (a b : Nat) : (b ≤ a ∧ a - b + b = a) ∨ (a < b ∧ a - b = 0) := by omega
theorem dv1 (a k : Nat) : k * (a / k) ≤ a := Nat.mul_div_le a k
theorem dv2 (a k : Nat) (hk : Nat.ble (nat_lit 1) k = true) : a < k * (a / k) + k := by
  have := Nat.lt_mul_div_succ a (Nat.le_of_ble_eq_true hk)
  rwa [Nat.mul_add, Nat.mul_one] at this
theorem md1 (a k : Nat) : a % k + k * (a / k) = a := Nat.mod_add_div a k
theorem md2 (a k : Nat) (hk : Nat.ble (nat_lit 1) k = true) : a % k < k :=
  Nat.mod_lt a (Nat.le_of_ble_eq_true hk)

end VG.Arith

end

public meta section

namespace VG.Omega

open Lean Meta Elab Tactic

/-- Whether `e` is a type `omega` reasons about: `Nat`, `Int`, `Fin n` or `BitVec w`. -/
def isArithType (e : Expr) : Bool :=
  e.isConstOf ``Nat || e.isConstOf ``Int || e.isAppOfArity ``BitVec 1 || e.isConstOf ``Fin ||
    e.isAppOfArity ``Fin 1

/-- Whether `p` is a fact `omega` may use: (in)equations over `Nat`, `Int` or
`BitVec`, `Dvd`, and `¬`, `∧`, `∨`, `↔`, `→` of those. -/
partial def isArithProp (p : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  match p.getAppFn.constName?, p.getAppNumArgs with
  | some ``Eq, 3 | some ``Ne, 3 | some ``LE.le, 4 | some ``LT.lt, 4 | some ``GE.ge, 4
  | some ``GT.gt, 4 | some ``Dvd.dvd, 4 => return isArithType (p.getArg! 0)
  | some ``Not, 1 => isArithProp (p.getArg! 0)
  | some ``And, 2 | some ``Or, 2 | some ``Iff, 2 =>
    return (← isArithProp (p.getArg! 0)) && (← isArithProp (p.getArg! 1))
  | _, _ =>
    if p.isArrow then return (← isArithProp p.bindingDomain!) && (← isArithProp p.bindingBody!)
    else return p.isConstOf ``False || p.isConstOf ``True

/-- Clears every hypothesis `omega` cannot use (and that nothing else depends on). -/
def clearNonArith : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  for d in (← getLCtx).getFVarIds.reverse do
    let some ld := (← getLCtx).find? d | continue
    if ld.isImplementationDetail || ld.isLet then continue
    let ty ← instantiateMVars ld.type
    unless ← isProp ty do continue
    if ← isArithProp ty then continue
    try g ← g.clear d catch _ => pure ()
  replaceMainGoal [g]

/-- Adds the facts `hs` to the main goal as new hypotheses, and clears every
other hypothesis that is a proposition. -/
def keepOnly (hs : Array Term) : TacticM Unit := do
  let mut g ← getMainGoal
  -- Elaborate every fact in the original context, then add them as new hypotheses.
  let facts ← g.withContext do
    hs.mapM fun h => do
      let e ← Term.elabTerm h none
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      pure (e, ← instantiateMVars (← inferType e))
  let mut keep : Array FVarId := #[]
  for (e, ty) in facts do
    let (fv, g') ← (← g.assert (← mkFreshUserName `h) ty e).intro1P
    keep := keep.push fv
    g := g'
  let g' ← g.withContext do
    let mut g := g
    for fv in (← getLCtx).getFVarIds.reverse do
      if keep.contains fv then continue
      let d ← fv.getDecl
      if d.isImplementationDetail then continue
      if ← isProp d.type then
        g ← g.tryClear fv
    pure g
  replaceMainGoal [g']

/-- Run the arithmetic solver on these facts and the negation of the goal. -/
def omegaFromFacts (facts : Array Expr) (exactTypeOnly := false) : TacticM Unit := do
  recordExtraModUse (isMeta := false) `Init.Omega
  liftMetaFinishingTactic fun g => g.withContext do
    let target ← g.getType
    for fact in facts do
      let factType ← inferType fact
      let sameType ← if exactTypeOnly then pure (factType == target)
        else withReducibleAndInstances <| isDefEq factType target
      if sameType then
        g.assign fact
        return
    let oldCtx ← getLCtx
    let some g ← g.falseOrByContra | return ()
    g.withContext do
      -- Include the negated goal and any hypotheses introduced from it.
      let newFacts := (← getLocalHyps).filter fun h => !oldCtx.contains h.fvarId!
      let type ← g.getType
      let result ← mkFreshExprSyntheticOpaqueMVar type
      Lean.Elab.Tactic.Omega.omega (facts.toList ++ newFacts.toList) result.mvarId!
      -- Keep the same auxiliary-theorem boundary as Lean's `omega` tactic.
      let proof ← mkAuxTheorem type (← instantiateMVarsProfiling result) (zetaDelta := true)
      g.assign proof

end VG.Omega

namespace VG.Arith

open Lean Meta Elab Tactic

/-- The value of a closed numeral expression. -/
partial def lit? (e : Expr) : Option Nat :=
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    let nat (t : Expr) : Bool := t.isConstOf ``Nat
    match_expr e with
    | OfNat.ofNat α n _ => if nat α then lit? n else none
    | HAdd.hAdd α _ _ _ a b => if nat α then do some ((← lit? a) + (← lit? b)) else none
    | HMul.hMul α _ _ _ a b => if nat α then do some ((← lit? a) * (← lit? b)) else none
    | HSub.hSub α _ _ _ a b => if nat α then do some ((← lit? a) - (← lit? b)) else none
    | HDiv.hDiv α _ _ _ a b => if nat α then do some ((← lit? a) / (← lit? b)) else none
    | HMod.hMod α _ _ _ a b => if nat α then do some ((← lit? a) % (← lit? b)) else none
    | HPow.hPow α β _ _ a b =>
      if nat α && nat β then do
        let b ← lit? b
        if b > 65536 then none else some ((← lit? a) ^ b)
      else none
    | Nat.succ a => do some ((← lit? a) + 1)
    | _ => none

/-- A linear form: monomials (atom, coefficient, the coefficient's expression) by increasing
atom, a constant, and the expressions of its suffixes (`sfx[i]`: from monomial `i` on). -/
structure Form where
  ms : Array (Nat × Nat × Expr)
  k : Nat
  sfx : Array Expr
  deriving Inhabited

def Form.expr (f : Form) : Expr := f.sfx[0]!
def Form.kE (f : Form) : Expr := f.sfx[f.ms.size]!

structure Fact where
  L : Form
  R : Form
  pf : Expr
  deriving Inhabited

structure Split where
  pf : Expr
  P : Expr
  Q : Expr
  deriving Inhabited

structure St where
  atoms : Array Expr := #[]
  /-- proofs of facts about atoms (`/`, `%`, `-`) not yet read -/
  queue : Array Expr := #[]
  gfacts : Array Fact := #[]
  gsplits : Array Split := #[]
  fuel : Nat := 24

abbrev AM := StateRefT St MetaM

def natE : Expr := mkConst ``Nat
def c (n : Name) : Expr := mkConst n

def mkForm (ms : Array (Nat × Nat × Expr)) (k : Nat) (kE : Expr) : AM Form := do
  let atoms := (← get).atoms
  let mut sfx := Array.replicate (ms.size + 1) kE
  for i' in [0:ms.size] do
    let i := ms.size - 1 - i'
    let (x, _, ce) := ms[i]!
    sfx := sfx.set! i (mkApp3 (c ``M) ce atoms[x]! sfx[i + 1]!)
  return { ms, k, sfx }

def constForm (n : Nat) : AM Form := mkForm #[] n (mkRawNatLit n)

/-- `F + G`, with a proof of `F.expr + G.expr = (F + G).expr`. -/
def addF (F G : Form) : AM (Form × Expr) := do
  let atoms := (← get).atoms
  let mut ms := #[]
  let mut i := 0
  let mut j := 0
  while i < F.ms.size || j < G.ms.size do
    if i < F.ms.size && j < G.ms.size && F.ms[i]!.1 == G.ms[j]!.1 then
      let (x, a, ae) := F.ms[i]!
      let (_, b, be) := G.ms[j]!
      ms := ms.push (x, a + b, mkApp2 (c ``Nat.add) ae be); i := i + 1; j := j + 1
    else if i < F.ms.size && (j == G.ms.size || F.ms[i]!.1 < G.ms[j]!.1) then
      ms := ms.push F.ms[i]!; i := i + 1
    else
      ms := ms.push G.ms[j]!; j := j + 1
  let H ← mkForm ms (F.k + G.k) (mkApp2 (c ``Nat.add) F.kE G.kE)
  let rec go (fuel i j p : Nat) : Expr :=
    match fuel with
    | 0 => mkApp2 (c ``kk) F.kE G.kE
    | fuel + 1 =>
      if i < F.ms.size && j < G.ms.size && F.ms[i]!.1 == G.ms[j]!.1 then
        mkApp7 (c ``mm) F.ms[i]!.2.2 G.ms[j]!.2.2 atoms[F.ms[i]!.1]! F.sfx[i + 1]! G.sfx[j + 1]! H.sfx[p + 1]!
          (go fuel (i + 1) (j + 1) (p + 1))
      else if i < F.ms.size && (j == G.ms.size || F.ms[i]!.1 < G.ms[j]!.1) then
        mkApp6 (c ``ml) F.ms[i]!.2.2 atoms[F.ms[i]!.1]! F.sfx[i + 1]! G.sfx[j]! H.sfx[p + 1]!
          (go fuel (i + 1) j (p + 1))
      else if j < G.ms.size then
        mkApp6 (c ``mr) F.sfx[i]! G.ms[j]!.2.2 atoms[G.ms[j]!.1]! G.sfx[j + 1]! H.sfx[p + 1]!
          (go fuel i (j + 1) (p + 1))
      else mkApp2 (c ``kk) F.kE G.kE
  return (H, go (F.ms.size + G.ms.size + 1) 0 0 0)

/-- `n * F`, with a proof of `n * F.expr = (n * F).expr`. -/
def scaleF (n : Nat) (F : Form) : AM (Form × Expr) := do
  if n == 0 then return (← constForm 0, mkApp (c ``zm) F.expr)
  let atoms := (← get).atoms
  let ne := mkRawNatLit n
  let H ← mkForm (F.ms.map fun (x, a, ae) => (x, n * a, mkApp2 (c ``Nat.mul) ne ae)) (n * F.k)
    (mkApp2 (c ``Nat.mul) ne F.kE)
  let mut pf := mkApp2 (c ``sk) ne F.kE
  for i' in [0:F.ms.size] do
    let i := F.ms.size - 1 - i'
    pf := mkApp6 (c ``sm) ne F.ms[i]!.2.2 atoms[F.ms[i]!.1]! F.sfx[i + 1]! H.sfx[i + 1]! pf
  return (H, pf)

def reflNat (n : Nat) : Expr := mkApp2 (mkConst ``Eq.refl [1]) natE (mkRawNatLit n)
def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (c ``Bool) (c ``Bool.true)

/-- The atom for `e`, and, the first time, the facts about it. -/
def atom (e : Expr) : AM (Form × Expr) := do
  let s ← get
  let i ← match s.atoms.findIdx? (· == e) with
    | some i => pure i
    | none =>
      set { s with atoms := s.atoms.push e }
      let nat (t : Expr) : Bool := t.isConstOf ``Nat
      let push (p : Expr) : AM Unit := modify fun s => { s with queue := s.queue.push p }
      match_expr e with
      | HSub.hSub α _ _ _ a b => if nat α then push (mkApp2 (c ``sub_cases) a b)
      | HDiv.hDiv α _ _ _ a k =>
        if nat α then
          if let some n := lit? k then
            if n ≥ 1 then
              push (mkApp2 (c ``dv1) a k); push (mkApp3 (c ``dv2) a k reflTrue)
      | HMod.hMod α _ _ _ a k =>
        if nat α then
          if let some n := lit? k then
            if n ≥ 1 then
              push (mkApp2 (c ``md1) a k); push (mkApp3 (c ``md2) a k reflTrue)
      | _ => pure ()
      pure s.atoms.size
  let F ← mkForm #[(i, 1, mkRawNatLit 1)] 0 (mkRawNatLit 0)
  return (F, mkApp (c ``atm) e)

/-- The linear form of `e : Nat`, with a proof of `e = F.expr`. -/
partial def norm (e : Expr) : AM (Form × Expr) := do
  let e := e.consumeMData
  if let some n := lit? e then return (← constForm n, reflNat n)
  let nat (t : Expr) : Bool := t.isConstOf ``Nat
  match_expr e with
  | HAdd.hAdd α _ _ _ a b =>
    unless nat α do return ← atom e
    let (Fa, pa) ← norm a
    let (Fb, pb) ← norm b
    let (F, pm) ← addF Fa Fb
    return (F, mkApp8 (c ``ad) a b Fa.expr Fb.expr F.expr pa pb pm)
  | HMul.hMul α _ _ _ a b =>
    unless nat α do return ← atom e
    if let some n := lit? a then
      let (Fb, pb) ← norm b
      let (F, pm) ← scaleF n Fb
      return (F, mkApp8 (c ``mu) a (mkRawNatLit n) b Fb.expr F.expr (reflNat n) pb pm)
    else if let some n := lit? b then
      let (Fa, pa) ← norm a
      let (F, pm) ← scaleF n Fa
      return (F, mkApp8 (c ``mur) b (mkRawNatLit n) a Fa.expr F.expr (reflNat n) pa pm)
    else atom e
  | Nat.succ a =>
    let (Fa, pa) ← norm a
    let (F, pm) ← addF Fa (← constForm 1)
    return (F, mkApp5 (c ``su) a Fa.expr F.expr pa pm)
  | _ => atom e

/-- What a branch knows: facts, case splits not taken, and a proof of `False` if one was given. -/
structure Ctx where
  facts : Array Fact := #[]
  splits : Array Split := #[]
  absurd : Option Expr := none

/-- Read the proposition `P`, proven by `h`. -/
partial def addProp (P h : Expr) (cx : Ctx) : AM Ctx := do
  let P := P.consumeMData
  let nat (t : Expr) : Bool := t.isConstOf ``Nat
  let le (a b : Expr) (h : Expr) (cx : Ctx) : AM Ctx := do
    let (L, pl) ← norm a
    let (R, pr) ← norm b
    return { cx with facts := cx.facts.push ⟨L, R, mkApp7 (c ``fle) a b L.expr R.expr pl pr h⟩ }
  let lt (a b : Expr) (h : Expr) (cx : Ctx) : AM Ctx := do
    let (L, pl) ← norm a
    let (R, pr) ← norm b
    let (L', pm) ← addF L (← constForm 1)
    return { cx with facts := cx.facts.push ⟨L', R, mkApp9 (c ``flt) a b L.expr R.expr L'.expr pl pr pm h⟩ }
  let nle (a b : Expr) (h : Expr) (cx : Ctx) : AM Ctx := do
    let (L, pl) ← norm a
    let (R, pr) ← norm b
    let (R', pm) ← addF R (← constForm 1)
    return { cx with facts := cx.facts.push ⟨R', L, mkApp9 (c ``fnle) a b L.expr R.expr R'.expr pl pr pm h⟩ }
  let nlt (a b : Expr) (h : Expr) (cx : Ctx) : AM Ctx := do
    let (L, pl) ← norm a
    let (R, pr) ← norm b
    return { cx with facts := cx.facts.push ⟨R, L, mkApp7 (c ``fnlt) a b L.expr R.expr pl pr h⟩ }
  let ne (a b : Expr) (h : Expr) (cx : Ctx) : AM Ctx := do
    let lt₁ ← mkAppM ``LT.lt #[a, b]
    let lt₂ ← mkAppM ``LT.lt #[b, a]
    return { cx with splits := cx.splits.push ⟨mkApp3 (c ``ne_cases) a b h, lt₁, lt₂⟩ }
  if P.isArrow then
    let A := P.bindingDomain!
    let B := P.bindingBody!
    unless (← isProp A) && (← isProp B) do return cx
    let sp : Split := ⟨mkApp3 (c ``impc) A B h, mkNot A, B⟩
    return { cx with splits := cx.splits.push sp }
  match_expr P with
  | Iff A B =>
    let sp : Split := ⟨mkApp3 (c ``iffc) A B h, mkAnd A B, mkAnd (mkNot A) (mkNot B)⟩
    return { cx with splits := cx.splits.push sp }
  | LE.le α _ a b => if nat α then le a b h cx else return cx
  | LT.lt α _ a b => if nat α then lt a b h cx else return cx
  | GE.ge α _ a b => if nat α then le b a h cx else return cx
  | GT.gt α _ a b => if nat α then lt b a h cx else return cx
  | Eq α a b =>
    unless nat α do return cx
    let (L, pl) ← norm a
    let (R, pr) ← norm b
    let f₁ : Fact := ⟨L, R, mkApp7 (c ``feq1) a b L.expr R.expr pl pr h⟩
    let f₂ : Fact := ⟨R, L, mkApp7 (c ``feq2) a b L.expr R.expr pl pr h⟩
    return { cx with facts := (cx.facts.push f₁).push f₂ }
  | Ne α a b => if nat α then ne a b h cx else return cx
  | And A B =>
    let cx ← addProp A (mkApp3 (c ``And.left) A B h) cx
    addProp B (mkApp3 (c ``And.right) A B h) cx
  | Or A B => return { cx with splits := cx.splits.push ⟨h, A, B⟩ }
  | False => return { cx with absurd := some h }
  | Not Q =>
    let Q := Q.consumeMData
    if Q.isArrow then
      let A := Q.bindingDomain!
      let B := Q.bindingBody!
      unless (← isProp A) && (← isProp B) do return cx
      return ← addProp (mkAnd A (mkNot B)) (mkApp3 (c ``nimp) A B h) cx
    match_expr Q with
    | Iff A B =>
      let sp : Split := ⟨mkApp3 (c ``niffc) A B h, mkAnd A (mkNot B), mkAnd (mkNot A) B⟩
      return { cx with splits := cx.splits.push sp }
    | LE.le α _ a b => if nat α then nle a b h cx else return cx
    | LT.lt α _ a b => if nat α then nlt a b h cx else return cx
    | GE.ge α _ a b => if nat α then nle b a h cx else return cx
    | GT.gt α _ a b => if nat α then nlt b a h cx else return cx
    | Eq α a b => if nat α then ne a b h cx else return cx
    | Ne α a b =>
      if nat α then addProp (← mkEq a b) (mkApp2 (c ``nn) (← mkEq a b) h) cx else return cx
    | Not R => addProp R (mkApp2 (c ``nn) R h) cx
    | Or A B =>
      let cx ← addProp (mkNot A) (.lam `a A (mkApp h (mkApp3 (c ``Or.inl) A B (.bvar 0))) .default) cx
      addProp (mkNot B) (.lam `b B (mkApp h (mkApp3 (c ``Or.inr) A B (.bvar 0))) .default) cx
    | And A B =>
      let sp : Split := ⟨mkApp3 (c ``nand) A B h, mkNot A, mkNot B⟩
      return { cx with splits := cx.splits.push sp }
    | True => return { cx with absurd := some (mkApp h (c ``True.intro)) }
    | _ => return cx
  | _ => return cx

/-- Read the queued facts about atoms. -/
partial def drain : AM Unit := do
  let q := (← get).queue
  if q.isEmpty then return
  modify fun s => { s with queue := #[] }
  for p in q do
    let cx ← addProp (← instantiateMVars (← inferType p)) p {}
    modify fun s => { s with gfacts := s.gfacts ++ cx.facts, gsplits := s.gsplits ++ cx.splits }
  drain

/-- How a constraint follows from the facts. -/
inductive Prov where
  | fact (i : Nat)
  | comb (a : Nat) (p : Prov) (b : Nat) (q : Prov)
  | cut (g : Nat) (p : Prov)
  deriving Inhabited

/-- A constraint `co · x + k ≥ 0`. -/
structure Cn where
  co : Array Int
  k : Int
  pv : Prov
  deriving Inhabited

/-- Divide by the coefficients' common divisor, rounding the constant down. -/
def tighten (cn : Cn) : Cn :=
  let g := cn.co.foldl (fun g x => Nat.gcd g x.natAbs) 0
  if g > 1 && cn.k.emod g != 0 then ⟨cn.co.map (·.ediv g), cn.k.ediv g, .cut g cn.pv⟩ else cn

/-- Fourier–Motzkin with rounding: a derivation of a constraint `k ≥ 0` with `k < 0`. The
constraints include `x ≥ 0` for every atom. -/
def fm (n : Nat) (cs : Array Cn) : Option Prov := Id.run do
  let mut cs := cs.map tighten
  let mut todo := (List.range n).toArray
  while !todo.isEmpty do
    for cn in cs do
      if cn.co.all (· == 0) && cn.k < 0 then return some cn.pv
    -- the atom with the smallest coefficients, then the fewest combinations
    let key (v : Nat) : Nat × Nat := Id.run do
      let mut mx := 0
      let mut pos := 0
      let mut neg := 0
      for cn in cs do
        let a := cn.co[v]!
        if a > 0 then pos := pos + 1
        if a < 0 then neg := neg + 1
        mx := max mx a.natAbs
      return (mx, pos * neg)
    let mut best := todo[0]!
    let mut bk := key best
    for v in todo do
      let kv := key v
      if kv.1 < bk.1 || (kv.1 == bk.1 && kv.2 < bk.2) then best := v; bk := kv
    let v := best
    todo := todo.filter (· != v)
    let mut pos : Array Cn := #[]
    let mut neg : Array Cn := #[]
    let mut new : Array Cn := #[]
    for cn in cs do
      let a := cn.co[v]!
      if a > 0 then pos := pos.push cn else if a < 0 then neg := neg.push cn else new := new.push cn
    for p in pos do
      for q in neg do
        let a := p.co[v]!.toNat
        let b := (-q.co[v]!).toNat
        let g := Nat.gcd a b
        let a := a / g
        let b := b / g
        let co := p.co.zipWith (fun x y => (b : Int) * x + (a : Int) * y) q.co
        let k := (b : Int) * p.k + (a : Int) * q.k
        if co.all (· == 0) && k ≥ 0 then continue
        new := new.push (tighten ⟨co, k, .comb b p.pv a q.pv⟩)
        if new.size > 120 then return none
    cs := new
  for cn in cs do
    if cn.co.all (· == 0) && cn.k < 0 then return some cn.pv
  return none

def scaleFact (k : Nat) (f : Fact) : AM Fact := do
  if k == 1 then return f
  let (L, pl) ← scaleF k f.L
  let (R, pr) ← scaleF k f.R
  return ⟨L, R, mkAppN (c ``sc) #[f.L.expr, f.R.expr, L.expr, R.expr, mkRawNatLit k, f.pf, pl, pr]⟩

/-- The fact a derivation proves. -/
partial def build (facts : Array Fact) : Prov → AM Fact
  | .fact i => pure facts[i]!
  | .comb a p b q => do
    let f ← scaleFact a (← build facts p)
    let g ← scaleFact b (← build facts q)
    let (L, pl) ← addF f.L g.L
    let (R, pr) ← addF f.R g.R
    return ⟨L, R, mkAppN (c ``pl) #[f.L.expr, f.R.expr, g.L.expr, g.R.expr, L.expr, R.expr, f.pf, g.pf, pl, pr]⟩
  | .cut g p => do
    let f ← build facts p
    let n := (← get).atoms.size
    let mut aL : Array Nat := Array.replicate n 0
    let mut aR : Array Nat := Array.replicate n 0
    for (x, a, _) in f.L.ms do aL := aL.set! x a
    for (x, a, _) in f.R.ms do aR := aR.set! x a
    let mut dm := #[]
    let mut lm := #[]
    let mut rm := #[]
    for x in [0:n] do
      let d := (g - aL[x]! % g) % g
      if d > 0 then dm := dm.push (x, d, mkRawNatLit d)
      if aL[x]! + d > 0 then lm := lm.push (x, (aL[x]! + d) / g, mkRawNatLit ((aL[x]! + d) / g))
      if aR[x]! + d > 0 then rm := rm.push (x, (aR[x]! + d) / g, mkRawNatLit ((aR[x]! + d) / g))
    let zero := mkRawNatLit 0
    let D ← mkForm dm 0 zero
    let L' ← mkForm lm 0 zero
    let R' ← mkForm rm 0 zero
    let (X, hl) ← addF f.L D
    let (Y, hr) ← addF f.R D
    let side (F' : Form) (k : Nat) : AM Expr := do
      let (G, pg) ← scaleF g F'
      let (X', pa) ← addF G (← constForm k)
      return mkApp8 (c ``ad) (mkNatMul (mkRawNatLit g) F'.expr) (mkRawNatLit k) G.expr (mkRawNatLit k) X'.expr
        pg (reflNat k) pa
    let hl' ← side L' f.L.k
    let hr' ← side R' f.R.k
    let t := ((f.R.k : Int) - f.L.k).ediv g
    let q := if t < 0 then (-t).toNat else 0
    let p := if t < 0 then 0 else t.toNat
    let (L'', hml) ← addF L' (← constForm q)
    let (R'', hmr) ← addF R' (← constForm p)
    return ⟨L'', R'', mkAppN (c ``cut) #[f.L.expr, f.R.expr, D.expr, X.expr, Y.expr, L'.expr, R'.expr, L''.expr, R''.expr,
      mkRawNatLit g, mkRawNatLit f.L.k, mkRawNatLit f.R.k, mkRawNatLit q, mkRawNatLit p, f.pf, hl, hl', hr, hr',
      reflTrue, reflTrue, hml, hmr]⟩

/-- A proof of `False` from the facts, if Fourier–Motzkin finds one. -/
def farkas (facts : Array Fact) : AM (Option Expr) := do
  let atoms := (← get).atoms
  let n := atoms.size
  -- every atom is `≥ 0`
  let mut facts := facts
  for x in [0:n] do
    facts := facts.push ⟨← constForm 0, ← mkForm #[(x, 1, mkRawNatLit 1)] 0 (mkRawNatLit 0), mkApp (c ``sl) atoms[x]!⟩
  let cs := facts.mapIdx fun i f => Id.run do
    let mut co : Array Int := Array.replicate n 0
    for (x, a, _) in f.R.ms do co := co.modify x (· + a)
    for (x, a, _) in f.L.ms do co := co.modify x (· - a)
    return (⟨co, (f.R.k : Int) - f.L.k, .fact i⟩ : Cn)
  let some pv := fm n cs | return none
  let f ← build facts pv
  -- left coefficients are at least the right ones, and the left constant is larger
  let mut h := f.pf
  let mut i := 0
  let mut j := 0
  while i < f.L.ms.size do
    let (x, a, ae) := f.L.ms[i]!
    if j < f.R.ms.size && f.R.ms[j]!.1 == x then
      let (_, b, be) := f.R.ms[j]!
      if b > a then return none
      h := mkApp7 (c ``zs) ae be atoms[x]! f.L.sfx[i + 1]! f.R.sfx[j + 1]! reflTrue h
      i := i + 1; j := j + 1
    else if j == f.R.ms.size || x < f.R.ms[j]!.1 then
      h := mkApp5 (c ``zl) ae atoms[x]! f.L.sfx[i + 1]! f.R.sfx[j]! h
      i := i + 1
    else return none
  if j < f.R.ms.size || f.L.k ≤ f.R.k then return none
  return some (mkApp4 (c ``zk) f.L.kE f.R.kE reflTrue h)

/-- A proof of `False` in the branch `cx`, splitting cases. `gskip`: global splits taken. -/
partial def solve (cx : Ctx) (gskip : Array Nat) : AM (Option Expr) := do
  if let some h := cx.absurd then return some h
  drain
  let s ← get
  if s.fuel == 0 then return none
  set { s with fuel := s.fuel - 1 }
  if let some pf ← farkas (cx.facts ++ s.gfacts) then return some pf
  -- a case split: the branch's own first
  let branch (sp : Split) (cx : Ctx) (gskip : Array Nat) : AM (Option Expr) := do
    let some p₁ ← withLocalDeclD `h sp.P fun h => do
        let some pf ← solve (← addProp sp.P h cx) gskip | return none
        return some (← mkLambdaFVars #[h] pf) | return none
    let some p₂ ← withLocalDeclD `h sp.Q fun h => do
        let some pf ← solve (← addProp sp.Q h cx) gskip | return none
        return some (← mkLambdaFVars #[h] pf) | return none
    return some (mkApp6 (c ``Or.elim) sp.P sp.Q (c ``False) sp.pf p₁ p₂)
  if h : 0 < cx.splits.size then
    return ← branch cx.splits[0] { cx with splits := cx.splits.extract 1 cx.splits.size } gskip
  for i in [0:s.gsplits.size] do
    unless gskip.contains i do
      return ← branch s.gsplits[i]! cx (gskip.push i)
  return none

/-- A proof of `goal` from the facts `hs` (proofs), by linear arithmetic over `Nat`. -/
def prove? (goal : Expr) (hs : Array Expr) : MetaM (Option Expr) := do
  let run : AM (Option Expr) := do
    let mut cx : Ctx := {}
    for h in hs do
      cx ← addProp (← instantiateMVars (← inferType h)) h cx
    let goal := goal.consumeMData
    if goal.isConstOf ``False then return ← solve cx #[]
    withLocalDeclD `hn (mkNot goal) fun hn => do
      let some pf ← solve (← addProp (mkNot goal) hn cx) #[] | return none
      return some (mkApp2 (c ``Classical.byContradiction) goal (← mkLambdaFVars #[hn] pf))
  run.run' {}

end VG.Arith

namespace VG.Omega

open Lean Meta Elab Tactic

namespace Abs

/-- The atoms read so far: each term with the variable that stands for it. -/
structure St where
  atoms : Array Expr := #[]
  vars : Array Expr := #[]
  types : Array Expr := #[]
  /-- proofs of what `omega` knows of an atom by its shape: `x.toNat < 2 ^ w`, `↑i < n` -/
  known : Array Expr := #[]

abbrev M := StateRefT St MetaM

def isNum (α : Expr) : Bool := α.isConstOf ``Nat || α.isConstOf ``Int

def closed (e : Expr) : Bool := !e.hasFVar && !e.hasMVar && !e.hasLooseBVars

/-- The variable for the term `e : α`. -/
def atom (α e : Expr) : OptionT M Expr := do
  if e.hasMVar || e.hasLooseBVars then failure
  let s ← get
  match s.atoms.findIdx? (· == e) with
  | some i => return s.vars[i]!
  | none =>
    let x := mkFVar (← mkFreshFVarId)
    let known := match_expr e with
      | BitVec.toNat w v => s.known.push (mkApp2 (mkConst ``BitVec.isLt) w v)
      | Fin.val n i => s.known.push (mkApp2 (mkConst ``Fin.isLt) n i)
      | _ => s.known
    set { s with atoms := s.atoms.push e, vars := s.vars.push x, types := s.types.push α, known }
    return x

/-- `e : α` (`Nat` or `Int`) with every subterm that is not arithmetic replaced by a variable. -/
partial def term (α : Expr) (e : Expr) : OptionT M Expr := do
  let e := e.consumeMData
  if e.isRawNatLit then return e
  let f := e.getAppFn
  let args := e.getAppArgs
  let some c := f.constName? | atom α e
  let bin (i j : Nat) : OptionT M Expr := do
    -- homogeneous binary operation: type arguments first, then the instance
    unless (args.extract 0 (i - 1)).all (· == α) && closed args[i - 1]! do return ← atom α e
    return mkAppN f (args.set! i (← term α args[i]!) |>.set! j (← term α args[j]!))
  match c, args.size with
  | ``OfNat.ofNat, 3 => if args[1]!.isRawNatLit && closed args[2]! then return e else atom α e
  | ``HAdd.hAdd, 6 | ``HSub.hSub, 6 | ``HMul.hMul, 6 | ``HDiv.hDiv, 6 | ``HMod.hMod, 6 => bin 4 5
  | ``Min.min, 4 | ``Max.max, 4 => bin 2 3
  | ``HPow.hPow, 6 =>
    unless args[0]! == α && args[1]!.isConstOf ``Nat && args[2]! == α && closed args[3]! do return ← atom α e
    return mkAppN f (args.set! 4 (← term α args[4]!) |>.set! 5 (← term (mkConst ``Nat) args[5]!))
  | ``Neg.neg, 3 =>
    unless args[0]! == α && closed args[1]! do return ← atom α e
    return mkAppN f (args.set! 2 (← term α args[2]!))
  | ``Nat.succ, 1 => return mkApp f (← term α args[0]!)
  | ``Nat.cast, 3 =>
    unless args[0]!.isConstOf ``Int && closed args[1]! do return ← atom α e
    return mkAppN f (args.set! 2 (← term (mkConst ``Nat) args[2]!))
  | ``Int.ofNat, 1 => return mkApp f (← term (mkConst ``Nat) args[0]!)
  | ``Int.toNat, 1 | ``Int.natAbs, 1 => return mkApp f (← term (mkConst ``Int) args[0]!)
  | _, _ => atom α e

/-- A proposition `omega` reads, with its atoms replaced by variables. -/
partial def prop (e : Expr) : OptionT M Expr := do
  let e := e.consumeMData
  if e.isArrow then
    return .forallE e.bindingName! (← prop e.bindingDomain!) (← prop e.bindingBody!) e.bindingInfo!
  let f := e.getAppFn
  let args := e.getAppArgs
  let some c := f.constName? | failure
  match c, args.size with
  | ``Eq, 3 | ``Ne, 3 =>
    unless isNum args[0]! do failure
    return mkAppN f #[args[0]!, ← term args[0]! args[1]!, ← term args[0]! args[2]!]
  | ``LE.le, 4 | ``LT.lt, 4 | ``GE.ge, 4 | ``GT.gt, 4 | ``Dvd.dvd, 4 =>
    unless isNum args[0]! && closed args[1]! do failure
    return mkAppN f #[args[0]!, args[1]!, ← term args[0]! args[2]!, ← term args[0]! args[3]!]
  | ``Not, 1 => return mkApp f (← prop args[0]!)
  | ``And, 2 | ``Or, 2 | ``Iff, 2 => return mkApp2 f (← prop args[0]!) (← prop args[1]!)
  | ``True, 0 | ``False, 0 => return e
  | _, _ => failure

/-- Proves the goal from the facts through a theorem about variables alone:
`∀ x₁ … xₙ, F₁ → … → Fₖ → G`, with a variable for every term of the goal and the facts
that is not arithmetic. One such theorem serves every goal of its shape in a declaration
(Lean's cache of auxiliary lemmas finds it by its statement), and
it is proven by `VG.Arith.prove?`. `false`, with the goal as it was, if the goal is not one
`prop` reads or that does not prove the statement. -/
def close (g : MVarId) (facts : Array Expr) (minimal := false) : MetaM Bool := g.withContext do
  let goal ← instantiateMVars (← g.getType)
  let read : M (Option (Expr × Array (Expr × Expr) × Nat)) := do
    let some goal' ← (prop goal).run | return none
    let mut fs := #[]
    for h in facts do
      let ty ← instantiateMVars (← inferType h)
      let saved ← get
      match ← (prop ty).run with
      | some ty' => fs := fs.push (h, ty')
      | none => set saved
    let given := fs.size
    -- what holds of the atoms by their shape, which `omega` adds itself
    let mut i := 0
    while i < (← get).known.size do
      let h := (← get).known[i]!
      let saved ← get
      match ← (prop (← instantiateMVars (← inferType h))).run with
      | some ty' => fs := fs.push (h, ty')
      | none => set { saved with known := (← get).known }
      i := i + 1
    return some (goal', fs, given)
  let (some (goal', fs, given), st) ← read.run {} | return false
  let mut body := goal'
  for (_, ty') in fs.reverse do
    body := .forallE `h ty' body .default
  body := body.abstract st.vars
  for i in [0:st.vars.size] do
    let j := st.vars.size - 1 - i
    body := .forallE ((`x).appendIndexAfter j) st.types[j]! body .default
  let stmt := body
  -- in an empty context: the proof may use nothing of this goal's
  let m ← withLCtx {} {} <| mkFreshExprSyntheticOpaqueMVar stmt
  let (xs, g₁) ← m.mvarId!.introNP st.vars.size
  let (hs, g₁) ← g₁.introNP fs.size
  let lin ← g₁.withContext do
    match ← VG.Arith.prove? (← instantiateMVars (← g₁.getType)) (hs.map mkFVar) with
    | some pf => g₁.assign pf; pure true
    | none => pure false
  -- Nothing else is tried on the statement about variables: `omega` knows less there than
  -- on the goal itself, and can take seconds to fail where it proves the goal at once.
  unless lin do return false
  -- With `minimal`, the theorem states and is applied to only the facts its proof uses, as
  -- `omega`'s proof would mention only those: for a proof that ends up inside a statement (an
  -- index bound), which should depend on no hypothesis it does not need. Otherwise every
  -- fact given is used, as far as the unused-variables linter can tell (and of the facts
  -- added here, those the proof uses).
  let (name, args) ← g₁.withContext do
    let pf ← instantiateMVars (mkMVar g₁)
    let goalTy ← instantiateMVars (← g₁.getType)
    let usedH := (Array.range hs.size).filter fun i => (!minimal && i < given) || pf.containsFVar hs[i]!
    let hTypes ← usedH.mapM fun i => do instantiateMVars (← hs[i]!.getType)
    let usedX := (Array.range xs.size).filter fun i =>
      goalTy.containsFVar xs[i]! || pf.containsFVar xs[i]! || hTypes.any (·.containsFVar xs[i]!)
    let fvars := usedX.map (mkFVar xs[·]!) ++ usedH.map (mkFVar hs[·]!)
    let name ← mkAuxLemma [] (← mkForallFVars fvars goalTy) (← mkLambdaFVars fvars pf)
    pure (name, usedX.map (st.atoms[·]!) ++ usedH.map (fs[·]!.1))
  -- Behind an auxiliary theorem of the goal's context, as `omega`'s proofs are: the atoms are
  -- not there for a later `rw` to find.
  g.assign (← mkAuxTheorem goal (mkAppN (mkConst name) args) (zetaDelta := true))
  return true

end Abs

/-- Close the main goal from `facts` through a theorem about its shape (`Abs.close`), if that
can. -/
def tryClose (facts : Array Expr) (minimal := false) : TacticM Bool := do
  let saved ← saveState
  let g ← getMainGoal
  let rest := (← getGoals).tail
  -- whatever goes wrong in there, the caller's own way is still to come
  if ← tryCatchRuntimeEx (Abs.close g facts minimal) (fun _ => do saved.restore; pure false) then
    setGoals rest
    return true
  return false

/-- Elaborate exactly the facts selected by the caller. A fact that is the
goal closes it only if its type is the goal's (unifying every fact with the
goal first costs more than the solver); if the solver then fails, try again
with a fact the goal is equal to up to unfolding. -/
def omegaWith (hs : Array Term) : TacticM Unit := do
  let facts ← withMainContext do
    hs.mapM fun h => do
      let e ← Term.elabTerm h none
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars e
  let saved ← saveState
  -- The goal as one of the facts, then through a theorem about its shape (`Abs.close`).
  let g ← getMainGoal
  let target ← g.withContext do instantiateMVars (← g.getType)
  for fact in facts do
    if (← g.withContext (inferType fact)) == target then
      g.assign fact
      replaceMainGoal []
      return
  if ← tryClose facts then return
  try omegaFromFacts facts (exactTypeOnly := true)
  catch _ =>
    saved.restore
    omegaFromFacts facts

/-- Adds the atoms of the arithmetic term or fact `e` to `acc`: its maximal
subterms that are not arithmetic operations, casts or numerals. -/
partial def atoms (e : Expr) (acc : Std.HashSet Expr) : MetaM (Std.HashSet Expr) := do
  let e := (← instantiateMVars e).consumeMData
  match e.getAppFn.constName?, e.getAppNumArgs with
  -- `omega` takes `x ^ k` for a `k` with atoms as an atom: its exponent's atoms do not
  -- connect it to other facts.
  | some ``HPow.hPow, 6 =>
    if (← atoms e.appArg! {}).isEmpty then atoms e.appFn!.appArg! acc
    else return acc.insert e
  | some ``HAdd.hAdd, 6 | some ``HSub.hSub, 6 | some ``HMul.hMul, 6 | some ``HDiv.hDiv, 6
  | some ``HMod.hMod, 6 | some ``Min.min, 4 | some ``Max.max, 4
  | some ``Eq, 3 | some ``Ne, 3 | some ``LE.le, 4 | some ``LT.lt, 4 | some ``GE.ge, 4
  | some ``GT.gt, 4 | some ``Dvd.dvd, 4 | some ``And, 2 | some ``Or, 2 | some ``Iff, 2 =>
    atoms e.appArg! (← atoms e.appFn!.appArg! acc)
  | some ``Not, 1 | some ``Nat.succ, 1 | some ``Nat.cast, 3 | some ``Int.ofNat, 1
  | some ``BitVec.toNat, 2 | some ``BitVec.ofNat, 2 | some ``Int.toNat, 1 | some ``Int.natAbs, 1
  | some ``Neg.neg, 3 => atoms e.appArg! acc
  | some ``OfNat.ofNat, 3 => return acc
  | _, _ =>
    if e.isRawNatLit || e.isConstOf ``False || e.isConstOf ``True then return acc
    if e.isArrow then return ← atoms e.bindingBody! (← atoms e.bindingDomain! acc)
    return acc.insert e

/-- The atom `x` of a fact `x = t`, if `x` is an atom. -/
def definedAtom? (ty : Expr) : MetaM (Option Expr) := do
  let ty := (← instantiateMVars ty).consumeMData
  let_expr Eq _ x _ := ty | return none
  let x := x.consumeMData
  let s ← atoms x {}
  return if s.size == 1 && s.contains x then some x else none

/-- The facts among `hs` connected to the goal: starting from the goal's
atoms, a fact is taken when it shares an atom with those taken so far (an
equation `x = t` of an atom `x`, only when `x` is among them), and adds its
atoms. Every fact `omega` adds to its problem makes its proof term larger,
which the kernel checks; equations such as a layout's offsets (`l.oE = …`),
in the context of every goal about one, made each proof several times
larger. -/
def relevantFacts (hs : Array Expr) (goal : Expr) : MetaM (Array Expr) := do
  let mut seen ← atoms goal {}
  if seen.isEmpty then return hs
  let mut infos : Array (Std.HashSet Expr × Option Expr) := #[]
  for h in hs do
    let ty ← inferType h
    infos := infos.push (← atoms ty {}, ← definedAtom? ty)
  let mut taken := Array.replicate hs.size false
  let mut changed := true
  while changed do
    changed := false
    for i in [:infos.size] do
      if taken[i]! then continue
      let (as, d) := infos[i]!
      if match d with | some x => seen.contains x | none => as.any seen.contains then
        taken := taken.set! i true
        seen := as.fold (·.insert ·) seen
        changed := true
  return (hs.zip taken).filterMap fun (h, t) => if t then some h else none

/-- `relevantFacts`, taking facts in at most `depth` rounds from the goal. -/
def relevantFactsDepth (hs : Array Expr) (goal : Expr) (depth : Nat) : MetaM (Array Expr) := do
  let mut seen ← atoms goal {}
  if seen.isEmpty then return #[]
  let mut infos : Array (Std.HashSet Expr × Option Expr) := #[]
  for h in hs do
    let ty ← inferType h
    infos := infos.push (← atoms ty {}, ← definedAtom? ty)
  let mut taken := Array.replicate hs.size false
  for _ in [0:depth] do
    let seen0 := seen
    let mut changed := false
    for i in [:infos.size] do
      if taken[i]! then continue
      let (as, d) := infos[i]!
      if match d with | some x => seen0.contains x | none => as.any seen0.contains then
        taken := taken.set! i true
        seen := as.fold (·.insert ·) seen
        changed := true
    if !changed then break
  return (hs.zip taken).filterMap fun (h, t) => if t then some h else none

/-- Select arithmetic hypotheses without repeatedly clearing the context. -/
def omegaArithFull : TacticM Unit := do
  let (facts, all) ← withMainContext do
    let all ← (← getLocalHyps).filterM fun h => do isArithProp (← inferType h)
    pure (← relevantFacts all (← getMainTarget), all)
  -- Most arithmetic goals need the solver, so avoid unifying every fact first.
  -- Retry the original path for goals that need a definitionally equal fact,
  -- then with every arithmetic fact.
  if ← tryClose facts then return
  let saved ← saveState
  try omegaFromFacts facts (exactTypeOnly := true)
  catch _ =>
    saved.restore
    if facts.size == all.size then omegaFromFacts facts
    else
      try omegaFromFacts facts
      catch _ =>
        saved.restore
        omegaFromFacts all

/-- `omega_arith`: `omega` on the facts within one and two rounds of the goal,
then `omegaArithFull`. -/
def omegaArith : TacticM Unit := do
  let stages ← withMainContext do
    let all ← (← getLocalHyps).filterM fun h => do isArithProp (← inferType h)
    let goal ← getMainTarget
    let full ← relevantFacts all goal
    let mut st : Array (Array Expr) := #[]
    for d in [1, 2] do
      let f ← relevantFactsDepth all goal d
      if f.size < full.size && st.all (·.size < f.size) then st := st.push f
    pure st
  for f in stages do
    if ← tryClose f then return
  omegaArithFull

/-- `omega` on the arithmetic facts connected to the goal, once: `omega_arith`
without its retries, for index bounds (`Framework/GetElem.lean`), where Lean
core's rules follow if it fails. -/
def omegaArithOnce : TacticM Unit := do
  let facts ← withMainContext do
    let all ← (← getLocalHyps).filterM fun h => do isArithProp (← inferType h)
    relevantFacts all (← getMainTarget)
  if ← tryClose facts (minimal := true) then return
  omegaFromFacts facts (exactTypeOnly := true)

/-- Clears every hypothesis `omega` cannot use. -/
elab "clear_non_arith" : tactic => clearNonArith

/-- `omega` using only the given facts, not the local context. -/
syntax (name := omegaUsing) "omega_using " "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| omega_using [$hs,*]) => omegaWith hs.getElems

/-- `bv_omega` using only the given facts, not the local context. -/
syntax (name := bvOmegaUsing) "bv_omega_using " "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| bv_omega_using [$hs,*]) => do
    keepOnly hs.getElems
    evalTactic (← `(tactic| bv_omega))

end VG.Omega

/-- `omega` using the arithmetic hypotheses in the local context. -/
elab "omega_arith" : tactic => VG.Omega.omegaArith

/-- `omega_arith` without its retries (`omegaArithOnce`). -/
elab "omega_arith_once" : tactic => VG.Omega.omegaArithOnce

/-- `bv_omega`, after clearing the hypotheses it cannot use. -/
macro "bv_omega_arith" : tactic => `(tactic| (clear_non_arith; bv_omega))

/-- `decide` if the goal is about numerals only (as the side conditions of
lemmas about literal offsets are, once instantiated), and `omega` otherwise.
`omega` first collects every arithmetic hypothesis in the context, a tenth of
a second or more deep in a proof about states; `decide` does not look at the
context. -/
macro "lit_omega" : tactic => `(tactic| first | decide | omega)

/-! ## Index identities by evaluation

Proofs about lanes and words are full of small identities between indices,
with `/` and `%` by literals, about variables with literal bounds (`e < 8`,
`l < 2`): `4 * ((e - 4) / 2) + 8 = 4 * (e / 2)` when `4 ≤ e`. `omega`
proves each, but its proof of a division or remainder is a large term,
which the kernel checks in tens of milliseconds every time.

`bdd_omega` proves such a goal by evaluation instead: when every variable of
the goal is a natural number with a literal bound among the hypotheses, it
states the goal for all values below the bounds, assuming the hypotheses
about those variables alone, and has the kernel evaluate it
(`decide +kernel`). Otherwise, or if that fails, it is `omega`.
-/

namespace VG

open Lean Meta Elab Tactic

/-- The literal `n` of a hypothesis `x < n` (or `x ≤ n - 1` as `x ≤ n`), for the
free variable `x`. -/
private def litBound? (x : FVarId) (ty : Expr) : MetaM (Option Nat) := do
  let ty ← instantiateMVars ty
  match ty.getAppFnArgs with
  | (``LT.lt, #[.const ``Nat [], _, a, b]) =>
    if a.isFVarOf x then return (← getNatValue? b) else return none
  | (``LE.le, #[.const ``Nat [], _, a, b]) =>
    if a.isFVarOf x then return (← getNatValue? b).map (· + 1) else return none
  | _ => return none
where
  getNatValue? (e : Expr) : MetaM (Option Nat) := do
    let e ← instantiateMVars e
    return e.nat? <|> e.rawNatLit?

/-- Whether `ty` is an arithmetic fact `bdd_omega` may assume: a comparison of
natural numbers, or its negation. -/
private partial def isArith (ty : Expr) : Bool :=
  match ty.getAppFnArgs with
  | (``Not, #[p]) => isArith p
  | (``LT.lt, #[.const ``Nat [], _, _, _]) | (``LE.le, #[.const ``Nat [], _, _, _]) => true
  | (``Eq, #[.const ``Nat [], _, _]) | (``Ne, #[.const ``Nat [], _, _]) => true
  | _ => false

/-- Tries to prove the main goal by evaluation over the bounded variables (see
"Index identities by evaluation"); returns whether it did. -/
private def bddDecide (maxCases : Nat) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  if tgt.hasMVar then return false
  let xs := (collectFVars {} tgt).fvarIds
  if xs.isEmpty then return false
  let lctx ← getLCtx
  -- Each variable: a natural number with a literal bound.
  let mut bounds : Array (FVarId × FVarId × Nat) := #[]
  for x in xs do
    let some d := lctx.find? x | return false
    unless (← whnfR d.type).isConstOf ``Nat do return false
    let mut best : Option (FVarId × Nat) := none
    for h in lctx do
      if h.isImplementationDetail then continue
      if let some n ← litBound? x h.type then
        if best.all (n < ·.2) then best := some (h.fvarId, n)
    let some (h, n) := best | return false
    bounds := bounds.push (x, h, n)
  if bounds.foldl (fun p (_, _, n) => p * n) 1 > maxCases then return false
  -- The other facts about these variables alone.
  let xset := xs.foldl (fun s x => s.insert x) ({} : Std.HashSet FVarId)
  let used := bounds.foldl (fun s (_, h, _) => s.insert h) ({} : Std.HashSet FVarId)
  let mut facts : Array FVarId := #[]
  for h in lctx do
    if h.isImplementationDetail || used.contains h.fvarId || xset.contains h.fvarId then continue
    let ty ← instantiateMVars h.type
    unless isArith ty do continue
    let fv := (collectFVars {} ty).fvarIds
    if !fv.isEmpty && fv.all xset.contains then facts := facts.push h.fvarId
  -- `∀ x₁, x₁ < n₁ → … → facts → goal`, by evaluation.
  let binders := bounds.foldl (fun a (x, h, _) => a.push (.fvar x) |>.push (.fvar h)) #[]
  let binders := binders ++ facts.map Expr.fvar
  let stmt ← mkForallFVars binders tgt
  if stmt.hasFVar then return false
  let m ← mkFreshExprSyntheticOpaqueMVar stmt
  let saved ← saveState
  try
    setGoals [m.mvarId!]
    evalTactic (← `(tactic| decide +kernel))
    let p ← instantiateMVars m
    g.assign (mkAppN p binders)
    setGoals []
    return true
  catch _ =>
    saved.restore
    return false

/-- `omega`, or, for a goal whose variables all have literal bounds among the
hypotheses (with at most `n` values in all, 64 if not given), the kernel's
evaluation of the goal for every value (see "Index identities by evaluation"). -/
elab "bdd_omega" n:(ppSpace num)? : tactic => do
  unless ← bddDecide (n.map (·.getNat) |>.getD 64) do evalTactic (← `(tactic| omega))

end VG
