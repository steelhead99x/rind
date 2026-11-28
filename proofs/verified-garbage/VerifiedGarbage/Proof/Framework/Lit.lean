module

public import Lean.Elab.Command
public meta import Lean.Elab.Command
public import Lean.Elab.Tactic.Rewrite
public meta import Lean.Elab.Tactic.Rewrite
public import Lean.Meta.Eval
public meta import Lean.Meta.Eval
public import Lean.Util.ShareCommon
public meta import Lean.Util.ShareCommon
public import VerifiedGarbage.TCB.Code

/-!
# Code as literals, for the kernel

The kernel evaluates code (the constant-time analysis, `Artifact.spSafe`, and
checks of every instruction), and most of that time can go into building the
instruction lists, which the code builds with functions (`List.append`,
`flatMap`, the round functions...), each structurally recursive: more than
the checks themselves, and again in every module that evaluates the code.

`materialize_code foo` evaluates `foo` (in compiled code) and defines
`foo.lit`, the same code written out as a literal, and
`foo.lit_eq : foo = foo.lit`, which the kernel checks once, by evaluation.
A proof about `foo.lit` is then a proof about `foo`. Code that calls a
function already materialized (`.call n g` with `g.lit` defined) refers to
`g.lit` rather than repeating it, so the kernel checks the callee's
instructions once for every caller (in `g.lit_eq`).

`lit_decide` proves a goal by `decide +kernel` after rewriting the code in
it that has a literal (`rw_lit`); `taint_decide` does the same.
-/

@[expose] public section

namespace VG

deriving instance Lean.ToExpr for Code

open Lean Meta Elab Command

namespace Lit

/-- The functions `materialize_code` has materialized, whose literals the
literals of their callers refer to: each `N` with a theorem `N.lit_eq`, in the
modules of this project (`VerifiedGarbage…`) and the current one. They are
found by name rather than recorded in an environment extension, whose
`initialize` the emitter's audit refuses (`TCB/Audit.lean`). -/
meta def litNames (env : Environment) : Array Name := Id.run do
  let add (acc : Array Name) (n : Name) : Array Name :=
    match n with
    | .str p "lit_eq" => if env.contains (.str p "lit") then acc.push p else acc
    | _ => acc
  let mut out := #[]
  -- (`moduleNames` builds the array on every use.)
  let mods := env.header.moduleNames
  for h : i in [0:mods.size] do
    if mods[i].getRoot.toString.startsWith "VerifiedGarbage" then
      out := env.header.moduleData[i]!.constNames.foldl add out
  return env.constants.foldStage2 (fun acc n _ => add acc n) out

/-- Replaces each body of a call in `e` (a literal `Code`) that is the literal of a
materialized function by a free variable, returning the abstracted literal and the
functions, in the order of the free variables. -/
meta partial def abstractCalls (lits : Array (Name × Expr)) (e : Expr) :
    StateT (Array Name) MetaM Expr := do
  if e.isAppOfArity ``Code.call 4 then
    let body := e.appArg!
    for (g, v) in lits do
      if body == v then
        let gs ← get
        let i := (gs.findIdx? (· == g)).getD gs.size
        if i == gs.size then set (gs.push g)
        return mkApp (e.appFn!) (.bvar (1000000 + i))
  match e with
  | .app f a => return .app (← abstractCalls lits f) (← abstractCalls lits a)
  | _ => return e


/-- The literal `g.lit` written out in full: with the literal of each
materialized function it calls (`h.lit`) replaced by its own, in turn. This is
the value of `g`, as `materialize` evaluated it. -/
meta partial def expandLit (g : Name) : StateT (Std.HashMap Name Expr) MetaM Expr := do
  if let some e := (← get)[g]? then return e
  let env ← getEnv
  let some v := (env.find? (g ++ `lit)).bind (·.value?)
    | throwError "materialize_code: {g ++ `lit} has no value"
  let mut sub : Std.HashMap Name Expr := {}
  for c in v.getUsedConstants do
    if let .str p "lit" := c then
      if env.contains (.str p "lit_eq") then
        sub := sub.insert c (← expandLit p)
  let e := if sub.isEmpty then v else
    v.replace fun x => match x with
      | .const c _ => sub[c]?
      | _ => none
  modify (·.insert g e)
  return e

/-- The code `lhs` of `N.lit_eq : lhs = N.lit`. -/
meta def lhsOf (N : Name) : MetaM Expr := do
  let some (_, lhs, _) := (← getConstInfo (N ++ `lit_eq)).type.eq?
    | throwError "{N ++ `lit_eq} is not an equation"
  return lhs

/-- The constants `c` with a literal (`c.lit_eq : c = c.lit`), from
`materialize_code c` or `materialize_table c`. -/
meta def litConsts (env : Environment) (names : Array Name := litNames env) : Array Name :=
  names.filter fun N => match env.find? (N ++ `lit_eq) with
    | some ci => match ci.type.eq? with
      | some (_, .const c _, _) => c == N
      | _ => false
    | none => false

/-- The constants `c` with a literal of another name (`N.lit_eq : c = N.lit`,
from `materialize_code N := c` or `materialize_value N := c`). -/
meta def litAliases (env : Environment) (names : Array Name := litNames env) : Array Name :=
  names.filterMap fun N => match env.find? (N ++ `lit_eq) with
    | some ci => match ci.type.eq? with
      | some (_, .const c _, _) => if c == N then none else some c
      | _ => none
    | none => none

/-- Whether `S` is a structure with a field that is a proof. -/
meta def hasProofFields (S : Expr) : MetaM Bool := do
  let .const S _ := S | return false
  let env ← getEnv
  unless isStructure env S do return false
  forallTelescopeReducing (getStructureCtor env S).type fun xs _ =>
    xs.anyM fun x => do isProp (← inferType x)

/-- Whether `c` is from a module that builds code (or the current module):
not the trusted base, the specifications or this framework, whose
definitions (the ISA models, ...) never lead to code with a literal, and
which `reaches` would otherwise search on every call. -/
meta def codeModule (env : Environment) (mods : Array Name) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => true
  | some i => match mods[i.toNat]?.map (·.components) with
    | some (`VerifiedGarbage :: `Proof :: `Framework :: _) => false
    | some (`VerifiedGarbage :: k :: _) => k ∈ [`Impl, `Proof, `Variants, `Generic, `Artifacts]
    | _ => false

/-- The index of the first module with one of `targets` (the number of
modules if they are all of the current one). A definition uses only
constants of its module and of the modules it imports, which come before it:
none of a module before that one leads to a target. -/
meta def firstModuleOf (env : Environment) (targets : NameSet) : Nat :=
  targets.foldl (init := env.header.moduleNames.size) fun i c =>
    match env.getModuleIdxFor? c with
    | some j => min i j.toNat
    | none => i

/-- Whether the definition `c` uses one of `targets`, directly or through
definitions of this project, memoized in the state; `first` is
`firstModuleOf targets`. -/
meta partial def reaches (targets : NameSet) (mods : Array Name) (first : Nat) (c : Name) :
    StateT (NameMap Bool) MetaM Bool := do
  if let some b := (← get).find? c then return b
  modify (·.insert c false)
  let env ← getEnv
  if let some i := env.getModuleIdxFor? c then
    if i.toNat < first then return false
  unless codeModule env mods c do return false
  let some (.defnInfo d) := env.find? c | return false
  -- Only data: unfolding a proposition could hide its `Decidable` instance.
  if d.type.getForallBody.isProp then return false
  let mut r := false
  -- Every constant used is visited (no early exit): `unfoldWhere` unfolds
  -- exactly the constants memoized as reaching, so stopping at the first one
  -- would leave the others (e.g. the second of two calls to code with a
  -- literal) folded, and the kernel would evaluate them again.
  for u in d.value.getUsedConstants do
    if targets.contains u then r := true
    else if u.getRoot == `VG && !(u matches .str _ "lit") then
      if ← reaches targets mods first u then r := true
  -- Rewriting code inside a structure with proofs about it would change the
  -- types of those proofs.
  if r then r := !(← hasProofFields d.type.getForallBody.getAppFn)
  modify (·.insert c r)
  return r

/-- `e` with the applications of the constants `p` holds of unfolded, again
in what they unfold to. A plain `Expr.replace`, which visits each shared
subterm once: the goals of `rw_lit` carry large literals (a hint of
`taint_decide`) that have nothing to unfold. -/
meta partial def unfoldWhere (env : Environment) (p : Name → Bool) (e : Expr)
    (stop : Expr → Bool := fun _ => false) : Expr :=
  e.replace fun t => if stop t then some t else match t.getAppFn with
    | .const c ls =>
      if p c then match env.find? c with
        | some (.defnInfo d) =>
          some (unfoldWhere env p ((d.value.instantiateLevelParams d.levelParams ls).betaRev
            t.getAppRevArgs) stop)
        | _ => none
      else none
    | _ => none

/-- The maximal closed subterms of `e` whose head is a definition that leads
to code with a literal (`reaches`), or one of them, given the names of the
literals (`litNames`): to a constant with a literal, its own or another's
(`materialize_value N := c`, which `unfoldToLits` rewrites as an atom), or
to the head of an application with one (`materialize_code M := f a`, a
template), as `unfoldToLits` unfolds to them. -/
meta def reachingSubterms (names : Array Name) (e : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let mods := (← getEnv).header.moduleNames
  let mut targets := (litConsts env names ++ litAliases env names).foldl (fun s c => s.insert c) ({} : NameSet)
  -- The heads of the code with a literal that is an application
  -- (`materialize_code M := f a`, a template): code that leads to one of
  -- them alone (a generic function of a curve's configuration, whose pieces
  -- have literals for that curve) is unfolded to them too.
  for M in names do
    let lhs ← lhsOf M
    if let .const c _ := lhs.getAppFn then
      if lhs.isApp && !lhs.hasLooseBVars && !targets.contains c && codeModule env mods c then
        if let some (.defnInfo _) := env.find? c then targets := targets.insert c
  if targets.isEmpty then return #[]
  let targets' := targets
  let first := firstModuleOf env targets'
  let mut memo : NameMap Bool := {}
  for u in e.getUsedConstants do
    if !targets'.contains u then
      (_, memo) ← (reaches targets' mods first u).run memo
  let memo' := memo
  let hit (c : Name) := targets'.contains c || memo'.find? c == some true
  unless e.getUsedConstants.any hit do return #[]
  let rec go (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
    if (← get).1.contains e then return
    modify fun (v, out) => (v.insert e, out)
    match e.getAppFn with
    | .const c _ =>
      if hit c && !e.hasLooseBVars && !e.hasFVar && !e.hasMVar then
        modify fun (v, out) => (v, out.push e)
        return
    | _ => pure ()
    match e with
    | .app f a => go f; go a
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  let ((), (_, out)) := (go e).run ({}, #[])
  return out

/-- For `x` (code, or a goal), a proof of `x = x'` and `x'`, where `x'` is `x`
with the definitions that lead to constants with a literal (but `N`)
unfolded, and those constants replaced by their literals; `none` if `x`
reaches none. The kernel checks the unfolding by delta reduction alone, and
then, evaluating `x'`, reads each literal rather than running again the
functions it was evaluated from: functions that build code (a register
allocator, tables of constants) are evaluated once, in their own `lit_eq`,
rather than in every literal or check of the code that uses them. -/
meta def unfoldToLits (N : Name) (x : Expr) (names? : Option (Array Name) := none) :
    MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  let names := match names? with | some n => n | none => litNames env
  let targets := (litConsts env names).foldl (fun s c => if c == N then s else s.insert c) {}
  -- The code with a literal that is an application (`materialize_code M := f a`):
  -- its occurrences are rewritten to `M.lit` as a whole (and not unfolded), so
  -- the definitions that lead to `f` are unfolded too.
  let mut atoms : Array (Name × Expr) := #[]
  for M in names do
    if M == N || targets.contains M then continue
    let lhs ← lhsOf M
    if lhs.getAppFn.isConst && !lhs.hasLooseBVars && !lhs.hasFVar && !lhs.hasMVar then
      atoms := atoms.push (M, lhs)
  let heads := atoms.foldl (fun s (_, l) => s.insert l.getAppFn.constName!) ({} : NameSet)
  let reachT := heads.foldl (fun s c => s.insert c) targets
  if reachT.isEmpty then return none
  let consts := x.getUsedConstants
  let mods := env.header.moduleNames
  let first := firstModuleOf env reachT
  let mut memo : NameMap Bool := {}
  for u in consts do
    if !reachT.contains u then
      (_, memo) ← (reaches reachT mods first u).run memo
  unless memo.any (fun _ b => b) || consts.any reachT.contains do return none
  -- The heads of the applications are unfolded where they are not one of
  -- them, if they lead to constants with a literal (or other applications).
  let mut headReach : NameSet := {}
  for c in heads do
    let some (.defnInfo d) := env.find? c | continue
    if !codeModule env mods c || d.type.getForallBody.isProp then continue
    let mut r := false
    for v in d.value.getUsedConstants do
      if reachT.contains v then r := true
      else if v.getRoot == `VG && !(v matches .str _ "lit") then
        let (b, m) ← (reaches reachT mods first v).run memo
        memo := m
        if b then r := true
    if r && !(← hasProofFields d.type.getForallBody.getAppFn) then headReach := headReach.insert c
  let memo' := memo
  let headReach' := headReach
  -- The templates (`materialize_template`): their applications are found up to
  -- definitional equality of the fixed arguments, and are not unfolded either.
  let tpls ← atoms.filterM fun (_, l) => do return (← whnfD (← inferType l)).isForall
  let isTplApp (l t : Expr) : Bool := t.getAppFn == l.getAppFn && t.getAppNumArgs == l.getAppNumArgs
  let isAtom (t : Expr) : Bool :=
    t.getAppFn.isConst && heads.contains t.getAppFn.constName! &&
      (atoms.any (·.2 == t) || tpls.any fun (_, l) => isTplApp l t)
  let e := unfoldWhere env (fun c => memo'.find? c == some true || headReach'.contains c) x isAtom
  -- What is rewritten to a literal: the constants with one, then the applications.
  let mut items : Array (Expr × Name) :=
    (e.getUsedConstants.filter targets.contains).map fun c => (mkConst c, c)
  for (M, lhs) in atoms do
    if (e.find? (· == lhs)).isSome then items := items.push (lhs, M)
  for (M, lhs) in tpls do
    let found ← IO.mkRef (#[] : Array Expr)
    e.forEach fun t => do
      if isTplApp lhs t && t != lhs && !t.hasLooseBVars then found.modify (·.push t)
    for t in ← found.get do
      -- By the kernel's check (as the proof will be), which decides closed terms
      -- (moduli, offsets) by evaluation, faster than `isDefEq`.
      if !items.any (·.1 == t) && Kernel.isDefEqGuarded (← getEnv) {} t lhs then
        items := items.push (t, M)
  if items.isEmpty then return none
  let ty ← inferType x
  let u ← getLevel ty
  let itemIdx (t : Expr) : Option Nat := items.findIdx? fun (pat, _) => match pat, t with
    | .const c _, .const c' _ => c == c'
    | pat, t => !pat.isConst && pat == t
  -- `e` with the `j`-th item replaced by its literal for `j < k`, and by `y`
  -- for `j = k`; later items are left as they are (and not looked into).
  let inst (k : Nat) (y : Option Expr) : Expr :=
    e.replace fun t => match itemIdx t with
      | some j => if j < k then some (mkConst (items[j]!.2 ++ `lit))
          else if j == k then y else some t
      | none => none
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [u]) ty x rhs
  -- `x = e` by delta, then each item rewritten to its literal.
  let mut prf := mkApp2 (mkConst ``Eq.refl [u]) ty x
  for h : k in [0:items.size] do
    let (pat, M) := items[k]
    let cty ← inferType pat
    let lvl ← getLevel cty
    let motive ← withLocalDeclD `y cty fun y => mkLambdaFVars #[y] (eqTy (inst k (some y)))
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive pat) (mkApp motive (mkConst (M ++ `lit)))
      (mkApp6 (mkConst ``congrArg [lvl, 1]) cty (mkSort 0) pat
        (mkConst (M ++ `lit)) motive (mkConst (M ++ `lit_eq))) prf
  return some (inst items.size none, prf)

/-! ### Templates

Code built by a function of a few offsets (`mulG M o a b`, a product of the
operands at `a` and `b` into `o`) is evaluated by the kernel once for each
call, in every literal of the code that calls it: P-384's ECDH evaluates over
a hundred products. `materialize_template N := f x₁ … xₖ`, for
`f x₁ … xₖ : Nat → … → Nat → α`, evaluates it once instead, with the offsets
variables: `N.lit` is a function whose body is the code with each offset
`oᵢ + c` written as such (found by evaluating the code at a few offsets far
apart and comparing them, `antiUnify`), and the kernel checks
`N.lit_eq : f x₁ … xₖ = N.lit` with the offsets free. A literal of code that
calls it then evaluates `N.lit o a b`, the body with the offsets added
(`unfoldToLits`), rather than `f`.

The function must not decide anything on its offsets (the kernel could not
decide it with them free): give a name to the code of each case
(`mulR`'s `mulG`), and a template to that. `unfoldToLits` rewrites the
applications of `f` whose fixed arguments are `x₁ … xₖ` up to definitional
equality (the modulus is reached by many paths: `p384.MP'`,
`(jwinCfg p384).M`, …). -/

/-- `(T, n)` if `e` is the literal `OfNat.ofNat T n _` (`ToExpr` of `Nat`
and of a nonnegative `Int`). -/
meta def natLitOf? (e : Expr) : Option (Expr × Nat) :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.appFn!.appArg! with
    | .lit (.natVal n) => some (e.appFn!.appFn!.appArg!, n)
    | _ => none
  else none

/-- The offsets a template is evaluated at: sample `j`'s offset `i` is
`2⁴⁰ (1 + j (i + 1)) + 2³⁶ i`, so that no two offsets differ by the same
amount in every sample. -/
meta def tplSamples (k : Nat) : Array (Array Nat) :=
  (Array.range 3).map fun j => (Array.range k).map fun i => 0x10000000000 * (1 + j * (i + 1)) + 0x1000000000 * i

/-- The value at the same place in the samples `es` of a template (of the
parameters `xs`), the same in each, but for each number that differs between
them, which is `xᵢ + c` for one `xᵢ` and `c < 2³²` in every sample. -/
meta partial def antiUnify (xs : Array Expr) (samples : Array (Array Nat)) (es : Array Expr) :
    StateT (Std.HashMap (Array Expr) Expr) MetaM Expr := do
  let e0 := es[0]!
  if es.all (· == e0) then return e0
  if let some r := (← get)[es]? then return r
  let r ← do
    if let some (T, _) := natLitOf? e0 then
      let ns := es.filterMap fun e => (natLitOf? e).map (·.2)
      unless ns.size == es.size do
        throwError "materialize_template: a number in one sample, not in another"
      let follows (i : Nat) : Option Nat := Id.run do
        let c : Int := (ns[0]! : Int) - samples[0]![i]!
        unless 0 ≤ c && c < 0x100000000 do return none
        for j in [1:ns.size] do
          unless (ns[j]! : Int) - samples[j]![i]! == c do return none
        return some c.toNat
      let some (i, c) := (List.range xs.size).findSome? fun i => (follows i).map (i, ·)
        | throwError "materialize_template: a number that follows no parameter: {ns}"
      let s := mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkConst ``Nat)
        (mkApp2 (mkConst ``instHAdd [0]) (mkConst ``Nat) (mkConst ``instAddNat)) xs[i]! (mkNatLit c)
      if T.isConstOf ``Nat then pure s
      else if T.isConstOf ``Int then pure (mkApp (mkConst ``Int.ofNat) s)
      else throwError "materialize_template: a number of type {T}"
    else
      let f := e0.getAppFn
      let n := e0.getAppNumArgs
      unless e0.isApp && es.all fun e => e.getAppFn == f && e.getAppNumArgs == n do
        throwError "materialize_template: the samples differ in shape (does the code decide on its offsets?)"
      let mut args := #[]
      for i in [0:n] do
        args := args.push (← antiUnify xs samples (es.map (·.getArg! i)))
      pure (mkAppN f args)
  modify (·.insert es r)
  return r

/-- `materialize_template N := f`: `N.lit` and `N.lit_eq : f = N.lit`, for `f`
a function of offsets (`Nat`), as above. -/
meta def materializeTemplate (N : Name) (f : Expr) : MetaM Unit := do
  if f.hasMVar || f.hasFVar then throwError "materialize_template: {f} is not closed"
  let ty ← inferType f
  forallTelescopeReducing ty fun xs body => do
    if xs.isEmpty then throwError "materialize_template: {f} is not a function"
    for x in xs do
      unless (← whnfD (← inferType x)).isConstOf ``Nat do
        throwError "materialize_template: a parameter is not a number: {x}"
    let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) body)
    let samples := tplSamples xs.size
    let es ← samples.mapM fun s => unsafe evalExpr Expr (mkConst ``Expr)
      (mkApp3 (mkConst ``ToExpr.toExpr [0]) body inst (mkAppN f (Array.map mkNatLit s)))
    let (b, _) ← (antiUnify xs samples es).run {}
    addDecl (forceExpose := true) <| .defnDecl {
      name := N ++ `lit, levelParams := [], type := ty
      value := ← mkLambdaFVars xs (ShareCommon.shareCommon' b)
      hints := .abbrev, safety := .safe }
    let u ← getLevel ty
    addDecl <| .thmDecl {
      name := N ++ `lit_eq, levelParams := [],
      type := mkApp3 (mkConst ``Eq [u]) ty f (mkConst (N ++ `lit)),
      value := mkApp2 (mkConst ``Eq.refl [u]) ty f }

/-! ### Code with its appends flattened

The kernel checks `N.lit_eq` by evaluating the code, and code is built with
`++` (`rowsF k m (r + 1) = rowsF k m r ++ rowF k m r`), nested to the left
as often as not: each instruction of `a` in `(a ++ b) ++ c` is then rebuilt
once for every `++` above it, time quadratic in the nesting (P-521's x86
multiplication: 18 rows, each with 17 nested steps, 9 s). `flattenCode`
proves, without evaluating anything, that the code is equal to the same code
with each block's list written as `List.flatten [c₁, …, cₙ]` (its pieces,
nested to the right), which the kernel then evaluates in time linear in its
length (P-521's multiplication: under 1 s).

`materialize_flat_code` uses it; `materialize_code` does not. The unfolding
runs `whnf` at the meta level, slower than the kernel, at every append and
every decision: for code nested to the right, or that decides much at each
step (selections of table entries, …), it costs more than it saves. -/

theorem flat_app {α : Type} {a b : List α} {La Lb : List (List α)}
    (ha : a = La.flatten) (hb : b = Lb.flatten) : a ++ b = (La ++ Lb).flatten := by
  rw [ha, hb, List.flatten_append]

theorem flat_nil {α : Type} : ([] : List α) = ([] : List (List α)).flatten := rfl

theorem flat_leaf {α : Type} (l : List α) : l = [l].flatten := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

theorem Code.block_congr {I C : Type} {l l' : List I} (h : l = l') :
    (Code.block l : Code I C) = .block l' := h ▸ rfl
theorem Code.seq_congr {I C : Type} {a a' b b' : Code I C} (ha : a = a') (hb : b = b') :
    Code.seq a b = .seq a' b' := ha ▸ hb ▸ rfl
theorem Code.ite_congr {I C : Type} {c : C} {a a' b b' : Code I C} (ha : a = a') (hb : b = b') :
    Code.ite c a b = .ite c a' b' := ha ▸ hb ▸ rfl
theorem Code.loop_congr {I C : Type} {c : C} {a a' : Code I C} (ha : a = a') :
    Code.loop a c = .loop a' c := ha ▸ rfl
theorem Code.frame_congr {I C : Type} {p q : I} {a a' : Code I C} (ha : a = a') :
    Code.frame p a q = .frame p a' q := ha ▸ rfl

/-- `++`, which `whnfNoAppend` never unfolds. -/
meta def appendConsts : NameSet := NameSet.empty |>.insert ``HAppend.hAppend |>.insert ``Append.append
  |>.insert ``List.append |>.insert ``instHAppendOfAppend |>.insert ``List.instAppend

/-- `whnf`, but never through `++`: a list built with `++` is left an append. -/
meta def whnfNoAppend (e : Expr) : MetaM Expr :=
  withCanUnfoldPred (fun cfg ci => do
    if appendConsts.contains ci.name then return false else canUnfoldDefault cfg ci) (whnf e)

/-- `whnfNoAppend`, or `none` where it fails (a number past the threshold of
`Nat.pow`'s evaluation, …): such a term is left for the kernel. Its messages
(that threshold's warning) are dropped: it only looks ahead. -/
meta def whnfNoAppend? (e : Expr) : MetaM (Option Expr) := do
  let msgs := (← getThe Core.State).messages
  let r ← tryCatchRuntimeEx (some <$> whnfNoAppend e) fun _ => pure none
  modifyThe Core.State fun s => { s with messages := msgs }
  return r

/-- The elements of the cons prefix of `l`, and its tail. -/
meta def consPrefix (l : Expr) : Array Expr × Expr := Id.run do
  let mut xs := #[]
  let mut t := l
  while t.isAppOfArity ``List.cons 3 do
    xs := xs.push (t.getArg! 1)
    t := t.appArg!
  return (xs, t)

/-- What `flatList` and `flattenCode` have done so far: the calls of `whnf`
(within a budget, past which they give up), and the deepest nesting of `++`
to the left that they have undone. -/
meta structure FlatState where
  whnfs : Nat := 0
  leftDepth : Nat := 0
  /-- Whether a definition may build a list with `++` (memoized). -/
  appends : NameMap Bool := {}

meta abbrev FlatM := StateT FlatState MetaM

/-- The calls of `whnf` `flattenCode` may make, a bound on its time. -/
meta def flatBudget : Nat := 100000

/-- The functions that build lists with `++`. -/
meta def appendBuilders : NameSet := appendConsts |>.insert ``List.flatten |>.insert ``List.flatMap

/-- Whether the definition `c` may build a list with `++`, directly or through
the definitions it uses: a list whose term uses none is left to the kernel
whole, without unfolding it at the meta level. -/
meta partial def mayAppend (c : Name) : FlatM Bool := do
  if appendBuilders.contains c then return true
  if let some b := (← get).appends.find? c then return b
  modify fun s => { s with appends := s.appends.insert c false }
  let some (.defnInfo d) := (← getEnv).find? c | return false
  let mut r := false
  for v in d.value.getUsedConstants do
    if ← mayAppend v then r := true; break
  modify fun s => { s with appends := s.appends.insert c r }
  return r

/-- `whnfNoAppend?`, counted against the budget (an exception past it). -/
meta def flatWhnf (e : Expr) : FlatM (Option Expr) := do
  let s ← get
  if s.whnfs ≥ flatBudget then throwError "flattenCode: over budget"
  set { s with whnfs := s.whnfs + 1 }
  whnfNoAppend? e

/-- For a list `l : List α`, pieces `L`, a proof of `l = L.flatten` (by
`flat_app`, `flat_leaf` and unfolding, which the kernel checks without
evaluating the pieces), and the depth of `++` nested to the left in `l`.
Below `depth` nested appends (a long chain nested to the right, which the
kernel evaluates in linear time anyway), the list is one piece: the proof
stays shallow enough for the kernel. -/
meta partial def flatList (α : Expr) (l : Expr) (depth : Nat := 64) :
    FlatM (Array Expr × Expr × Nat) := do
  let lα := mkApp (mkConst ``List [0]) α
  let toL (cs : Array Expr) : Expr :=
    cs.foldr (fun c acc => mkApp3 (mkConst ``List.cons [0]) lα c acc)
      (mkApp (mkConst ``List.nil [0]) lα)
  let leaf (x : Expr) : Array Expr × Expr × Nat := (#[x], mkApp2 (mkConst ``flat_leaf) α x, 0)
  if depth == 0 then return leaf l
  let app (a b : Expr) : FlatM (Array Expr × Expr × Nat) := do
    let (ca, pa, da) ← flatList α a (depth - 1)
    let (cb, pb, db) ← flatList α b (depth - 1)
    let d := max (da + 1) db
    modify fun s => { s with leftDepth := max s.leftDepth d }
    return (ca ++ cb, mkAppN (mkConst ``flat_app) #[α, a, b, toL ca, toL cb, pa, pb], d)
  if (consPrefix l).2.isAppOfArity ``List.nil 1 then return leaf l
  unless ← l.getUsedConstants.anyM mayAppend do return leaf l
  let some w ← flatWhnf l | return leaf l
  if w.isAppOfArity ``HAppend.hAppend 6 then return ← app (w.getArg! 4) (w.getArg! 5)
  if w.isAppOfArity ``List.append 3 then return ← app (w.getArg! 1) (w.getArg! 2)
  if w.isAppOfArity ``List.nil 1 then return (#[], mkApp (mkConst ``flat_nil) α, 0)
  if w.isAppOfArity ``List.cons 3 then
    let (xs, t) := consPrefix w
    if t.isAppOfArity ``List.nil 1 then return leaf w
    -- `x₁ :: … :: xₖ :: t` is `[x₁, …, xₖ] ++ t` (the kernel appends `k` elements).
    let pre := xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) α x acc)
      (mkApp (mkConst ``List.nil [0]) α)
    return ← app pre t
  return leaf w

/-- For code `c : Code I C`, the same code with each block's list flattened
(`flatList`), and a proof of `c = c'`; the bodies of calls are left as they
are (the literals of their callees, or code the kernel compares as it is).
Code nested deeper than `depth` is left as it is, as `flatList` leaves lists. -/
meta partial def flattenCode (I C : Expr) (c : Expr) (depth : Nat := 64) : FlatM (Expr × Expr) := do
  let codeTy := mkApp2 (mkConst ``Code) I C
  let refl (x : Expr) := (x, mkApp2 (mkConst ``Eq.refl [1]) codeTy x)
  if depth == 0 then return refl c
  let some w ← flatWhnf c | return refl c
  match w.getAppFn.constName?, w.getAppNumArgs with
  | some ``Code.block, 3 =>
    let (cs, p, _) ← flatList I (w.getArg! 2)
    let lI := mkApp (mkConst ``List [0]) I
    let L := cs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [0]) lI x acc)
      (mkApp (mkConst ``List.nil [0]) lI)
    let l' := mkApp2 (mkConst ``List.flatten [0]) I L
    return (mkApp3 (mkConst ``Code.block) I C l',
      mkAppN (mkConst ``Code.block_congr) #[I, C, w.getArg! 2, l', p])
  | some ``Code.seq, 4 =>
    let (a, pa) ← flattenCode I C (w.getArg! 2) (depth - 1)
    let (b, pb) ← flattenCode I C (w.getArg! 3) (depth - 1)
    return (mkApp4 (mkConst ``Code.seq) I C a b,
      mkAppN (mkConst ``Code.seq_congr) #[I, C, w.getArg! 2, a, w.getArg! 3, b, pa, pb])
  | some ``Code.ite, 5 =>
    let (a, pa) ← flattenCode I C (w.getArg! 3) (depth - 1)
    let (b, pb) ← flattenCode I C (w.getArg! 4) (depth - 1)
    return (mkApp5 (mkConst ``Code.ite) I C (w.getArg! 2) a b,
      mkAppN (mkConst ``Code.ite_congr) #[I, C, w.getArg! 2, w.getArg! 3, a, w.getArg! 4, b, pa, pb])
  | some ``Code.loop, 4 =>
    let (a, pa) ← flattenCode I C (w.getArg! 2) (depth - 1)
    return (mkApp4 (mkConst ``Code.loop) I C a (w.getArg! 3),
      mkAppN (mkConst ``Code.loop_congr) #[I, C, w.getArg! 3, w.getArg! 2, a, pa])
  | some ``Code.frame, 5 =>
    let (a, pa) ← flattenCode I C (w.getArg! 3) (depth - 1)
    return (mkApp5 (mkConst ``Code.frame) I C (w.getArg! 2) a (w.getArg! 4),
      mkAppN (mkConst ``Code.frame_congr) #[I, C, w.getArg! 2, w.getArg! 4, w.getArg! 3, a, pa])
  | _, _ => return refl c

/-- The depth of `++` nested to the left from which flattening pays: below
it, the kernel's evaluation of the code as it is costs little more than its
evaluation flattened, and the unfolding is extra work. -/
meta def flatMinDepth : Nat := 4

/-- `flattenCode`, if it pays (`flatMinDepth`) and stays within its budget. -/
meta def flattenCode? (I C c : Expr) : MetaM (Option (Expr × Expr)) := do
  let r ← tryCatch (some <$> (flattenCode I C c).run {}) fun _ => pure none
  let some ((c', prf), s) := r | return none
  if s.leftDepth < flatMinDepth then return none
  return some (c', prf)

/-- Defines `N.lit`, the value of the closed code term `code` as a literal
(calling the literals of the code materialized so far), and
`N.lit_eq : code = N.lit`. -/
meta def materialize (N : Name) (code : Expr) (flat : Bool := false) : MetaM Unit := do
  let ty ← inferType code
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do
    throwError "materialize_code: {code} is not code: {ty}"
  let codeTy := mkApp2 (mkConst ``Code) (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!)
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) codeTy)
  let eval (e : Expr) : MetaM Expr := unsafe evalExpr Expr (mkConst ``Expr)
    (mkApp3 (mkConst ``ToExpr.toExpr [0]) codeTy inst e)
  let v ← eval code
  -- The code materialized so far, written out in full.
  let mut lits : Array (Name × Expr) := #[]
  let mut expanded : Std.HashMap Name Expr := {}
  for g in litNames (← getEnv) do
    let lhs ← lhsOf g
    if (← isDefEq (← inferType lhs) ty) then
      let (e, m) ← (expandLit g).run expanded
      expanded := m
      lits := lits.push (g, e)
  let (abs, gs) ← (abstractCalls lits v).run #[]
  let lhss ← gs.mapM lhsOf
  -- `abs` with the `i`-th callee (marked `.bvar (1000000 + i)`) replaced by `f i`.
  let inst (f : Nat → Expr) : Expr :=
    abs.replace fun e => match e with
      | .bvar k => if 1000000 ≤ k then some (f (k - 1000000)) else none
      | _ => none
  let litV := ShareCommon.shareCommon' (inst fun i => mkConst (gs[i]! ++ `lit))
  addDecl (forceExpose := true) <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := litV
    hints := .abbrev, safety := .safe }
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [1]) ty code rhs
  -- If the code reaches literals: `code = e'` by unfolding (`unfoldToLits`),
  -- and `e' = N.lit` by evaluation.
  let I := codeTy.appFn!.appArg!
  let C := codeTy.appArg!
  if let some (e, prf) ← unfoldToLits N code then
    -- `code = e` by unfolding, `e = e'` by flattening its blocks, and `e' = N.lit`
    -- by evaluation.
    let prf := match ← (if flat then flattenCode? I C e else pure none) with
      | some (e', q) => mkApp6 (mkConst ``Eq.trans [1]) ty code e e' prf q
      | none => prf
    addDecl <| .thmDecl {
      name := N ++ `lit_eq, levelParams := [], type := eqTy (mkConst (N ++ `lit)),
      value := ShareCommon.shareCommon' prf }
    return
  -- `code = code'` by flattening its blocks, `code' = abs[callees]` by evaluation,
  -- then each callee rewritten to its literal.
  let mut prf := match ← (if flat then flattenCode? I C code else pure none) with
    | some (code', q) => mkApp6 (mkConst ``Eq.trans [1]) ty code code' (inst fun i => lhss[i]!) q
        (mkApp2 (mkConst ``Eq.refl [1]) ty code')
    | none => mkApp2 (mkConst ``Eq.refl [1]) ty code
  for i in [0:gs.size] do
    -- The code with the literals of the first `i` callees, and `x` for the `i`-th.
    let motive := Expr.lam `x ty
      (eqTy ((inst fun j => if j < i then mkConst (gs[j]! ++ `lit)
        else if j == i then .bvar 0 else lhss[j]!))) .default
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive lhss[i]!) (mkApp motive (mkConst (gs[i]! ++ `lit)))
      (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) lhss[i]!
        (mkConst (gs[i]! ++ `lit)) motive (mkConst (gs[i]! ++ `lit_eq))) prf
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := eqTy (mkConst (N ++ `lit)),
    value := ShareCommon.shareCommon' prf }

end Lit

/-- A function on `Nat` is the table of its first values, falling back to
itself beyond them. -/
theorem Lit.table_eq {α : Type} (f : Nat → α) (n : Nat) (l : List α)
    (h : (List.range n).map f = l) : f = fun i => l.getD i (f i) := by
  funext i
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi]; rfl
  · rw [List.getElem?_eq_none (l := List.range n) (by simpa using hi)]; rfl

/-- A function of two `Nat`s is the table of its first values, falling back
to itself beyond them. -/
theorem Lit.table2_eq {α : Type} (f : Nat → Nat → α) (n m : Nat) (l : List (List α))
    (h : (List.range n).map (fun i => (List.range m).map (f i)) = l) :
    f = fun i j => (l.getD i []).getD j (f i j) := by
  funext i j
  subst h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi, Option.map_some, Option.getD_some, List.getElem?_map]
    by_cases hj : j < m
    · rw [List.getElem?_range hj]; rfl
    · rw [List.getElem?_eq_none (by simpa using hj)]; rfl
  · rw [List.getElem?_eq_none (l := List.range n) (by simpa using hi)]; rfl

/-- A function to `Nat` is its first values packed in `w`-bit fields of one
number `N` (`M = 2 ^ w`), falling back to itself beyond them: the kernel
reads a value with two arithmetic operations, which it runs natively,
rather than walking a list. -/
theorem Lit.packed_eq (f : Nat → Nat) (n w M N : Nat)
    (h : (List.range n).all (fun i => Nat.beq (N >>> (w * i) % M) (f i)) = true) :
    f = fun i => cond (Nat.blt i n) (N >>> (w * i) % M) (f i) := by
  funext i
  cases hi : Nat.blt i n
  · rfl
  · have hi : i < n := Nat.blt_eq.mp hi
    exact (Nat.eq_of_beq_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))).symm

/-- `Lit.packed_eq` for a function of two `Nat`s, its values at `i < n`,
`j < m` in field `m i + j`. -/
theorem Lit.packed2_eq (f : Nat → Nat → Nat) (n m w M N : Nat)
    (h : (List.range n).all (fun i => (List.range m).all fun j =>
      Nat.beq (N >>> (w * (m * i + j)) % M) (f i j)) = true) :
    f = fun i j => cond (Nat.blt i n && Nat.blt j m) (N >>> (w * (m * i + j)) % M) (f i j) := by
  funext i j
  cases hi : Nat.blt i n <;> cases hj : Nat.blt j m
  · rfl
  · rfl
  · rfl
  · have hi : i < n := Nat.blt_eq.mp hi
    have hj : j < m := Nat.blt_eq.mp hj
    exact (Nat.eq_of_beq_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_range.mpr hi)) j
      (List.mem_range.mpr hj))).symm

open Lit in
/-- `materialize_table f n`, for a closed `f : Nat → α`, defines `f.lit`, the
table of the values `f 0`, …, `f (n - 1)` as literals (and `f i` beyond
them), and `f.lit_eq : f = f.lit`, which the kernel checks by evaluating
those `n` values once. The literals of code that calls `f` then read the
table (`materialize_code`). `materialize_table f n m`, for a closed
`f : Nat → Nat → α`, does the same with the table of the values `f i j`,
`i < n`, `j < m`. A table of `Nat`s is one number (`Lit.packed_eq`), which
the kernel reads in constant time; others are lists. -/
elab "materialize_table " id:ident n:num m:(num)? : command => liftTermElabM do
  let f ← realizeGlobalConstNoOverloadWithInfo id
  let fty ← whnfD (← inferType (mkConst f))
  let .forallE _ (.const ``Nat []) α _ := fty
    | throwError "materialize_table: {f} is not a function on `Nat`: {fty}"
  if α.hasLooseBVars then throwError "materialize_table: {f} is dependent"
  let nat := mkConst ``Nat
  let range (k : Nat) := mkApp (mkConst ``List.range) (mkNatLit k)
  -- The values of the table (the type of its rows, and the values of `g`), and
  -- the value of `g` at `i` (and `j`) from the table `l`, else `d`.
  let (β, rowTy, valsOf, lookup) ← match m with
    | none => pure (α, α,
        fun (g : Expr) => mkApp4 (mkConst ``List.map [0, 0]) nat α g (range n.getNat),
        fun (l i _ d : Expr) => mkApp4 (mkConst ``List.getD [0]) α l i d)
    | some m =>
      let .forallE _ (.const ``Nat []) β _ ← whnfD α
        | throwError "materialize_table: {f} is not a function of two `Nat`s: {fty}"
      if β.hasLooseBVars then throwError "materialize_table: {f} is dependent"
      let rowTy := mkApp (mkConst ``List [0]) β
      pure (β, rowTy,
        fun (g : Expr) => mkApp4 (mkConst ``List.map [0, 0]) nat rowTy
          (.lam `i nat (mkApp4 (mkConst ``List.map [0, 0]) nat β (mkApp g (.bvar 0)) (range m.getNat)) .default)
          (range n.getNat),
        fun (l i j d : Expr) => mkApp4 (mkConst ``List.getD [0]) β
          (mkApp4 (mkConst ``List.getD [0]) rowTy l i (mkApp (mkConst ``List.nil [0]) β)) j d)
  let listTy := mkApp (mkConst ``List [0]) rowTy
  -- A table of `Nat`s is packed in one number (`Lit.packed_eq`).
  if β == nat then
    let vals : List Nat ← match m with
      | none => unsafe evalExpr (List Nat) (mkApp (mkConst ``List [0]) nat) (valsOf (mkConst f))
      | some _ => do
        let rows ← unsafe evalExpr (List (List Nat)) listTy (valsOf (mkConst f))
        pure rows.flatten
    let w := max 1 (vals.foldl (fun w v => max w v.log2.succ) 0)
    let N := vals.foldr (fun v acc => v ||| (acc <<< w)) 0
    let lemma (g : Expr) : Expr := match m with
      | none => mkApp5 (mkConst ``Lit.packed_eq) g (mkNatLit n.getNat) (mkNatLit w) (mkNatLit (2 ^ w))
          (mkNatLit N)
      | some m => mkApp6 (mkConst ``Lit.packed2_eq) g (mkNatLit n.getNat) (mkNatLit m.getNat) (mkNatLit w)
          (mkNatLit (2 ^ w)) (mkNatLit N)
    -- The hypothesis of the lemma, for `g`: its values are the table's.
    let hTyOf (g : Expr) : MetaM Expr := do return (← whnfR (← inferType (lemma g))).bindingDomain!
    let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    -- By evaluation, of `f` with the literals it reaches (`unfoldToLits`) if any.
    let h ← match ← unfoldToLits f (mkConst f) with
      | none => pure refl
      | some (f', prfF) =>
        let motive ← withLocalDeclD `g fty fun g => do mkLambdaFVars #[g] (← hTyOf g)
        pure <| mkApp4 (mkConst ``Eq.mpr [0]) (← hTyOf (mkConst f)) (← hTyOf f')
          (mkApp6 (mkConst ``congrArg [1, 1]) fty (mkSort 0) (mkConst f) f' motive prfF) refl
    let prf := mkApp (lemma (mkConst f)) h
    let some (_, _, litV) := (← inferType prf).eq?
      | throwError "materialize_table: unexpected {← inferType prf}"
    addDecl (forceExpose := true) <| .defnDecl {
      name := f ++ `lit, levelParams := [], type := fty, value := litV
      hints := .abbrev, safety := .safe }
    addDecl <| .thmDecl {
      name := f ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) fty (mkConst f) (mkConst (f ++ `lit))
      value := prf }
    return
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) listTy)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) listTy inst
    (valsOf (mkConst f)))
  let l := ShareCommon.shareCommon' l
  -- `valsOf f = l`: by evaluation, of `f` with the literals it reaches
  -- (`unfoldToLits`) if any, so that a table built from tables reads them.
  let refl := mkApp2 (mkConst ``Eq.refl [1]) listTy l
  let hvals ← match ← unfoldToLits f (mkConst f) with
    | none => pure refl
    | some (f', prfF) =>
      let motive ← withLocalDeclD `g fty fun g => mkLambdaFVars #[g] (valsOf g)
      pure <| mkApp6 (mkConst ``Eq.trans [1]) listTy (valsOf (mkConst f)) (valsOf f') l
        (mkApp6 (mkConst ``congrArg [1, 1]) fty listTy (mkConst f) f' motive prfF) refl
  let litV ← match m with
    | none => withLocalDeclD `i nat fun i =>
        mkLambdaFVars #[i] (lookup l i i (mkApp (mkConst f) i))
    | some _ => withLocalDeclD `i nat fun i => withLocalDeclD `j nat fun j =>
        mkLambdaFVars #[i, j] (lookup l i j (mkApp2 (mkConst f) i j))
  let prf := match m with
    | none => mkApp5 (mkConst ``Lit.table_eq) β (mkConst f) (mkNatLit n.getNat) l hvals
    | some m => mkApp6 (mkConst ``Lit.table2_eq) β (mkConst f) (mkNatLit n.getNat) (mkNatLit m.getNat) l hvals
  addDecl (forceExpose := true) <| .defnDecl {
    name := f ++ `lit, levelParams := [], type := fty, value := litV
    hints := .abbrev, safety := .safe }
  addDecl <| .thmDecl {
    name := f ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) fty (mkConst f) (mkConst (f ++ `lit))
    value := ShareCommon.shareCommon' prf }

namespace Lit

/-- Defines `N.lit`, the value of the closed term `v` (of a type with a
`ToExpr` instance) as a literal, and `N.lit_eq : v = N.lit`, by evaluation
(reading the literals `v` reaches). -/
meta def materializeValue (N : Name) (v : Expr) : MetaM Unit := do
  let ty ← instantiateMVars (← inferType v)
  if ty.hasLevelParam || ty.hasMVar then throwError "materialize_value: {v} is universe polymorphic"
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) ty)
  let l ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) ty inst v)
  addDecl (forceExpose := true) <| .defnDecl {
    name := N ++ `lit, levelParams := [], type := ty, value := ShareCommon.shareCommon' l
    hints := .abbrev, safety := .safe }
  -- By evaluation, of `v` with the literals it reaches (`unfoldToLits`) if any.
  let prf ← match ← unfoldToLits N v with
    | some (_, prf) => pure prf
    | none => pure (mkApp2 (mkConst ``Eq.refl [1]) ty v)
  addDecl <| .thmDecl {
    name := N ++ `lit_eq, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) ty v (mkConst (N ++ `lit))
    value := ShareCommon.shareCommon' prf }

end Lit

open Lit in
/-- `materialize_value c`, for a closed constant `c` whose type has a `ToExpr`
instance (e.g. a list of instructions that several programs contain),
defines `c.lit`, its value as a literal, and `c.lit_eq : c = c.lit`, which the
kernel checks once, by evaluation; `materialize_value N := t` does the same for
the closed term `t`, as `N.lit` and `N.lit_eq`. The literals of code that
contains it then read it (`materialize_code`), as for `materialize_table`. -/
syntax "materialize_value " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_value $id:ident) => liftTermElabM do
    let c ← realizeGlobalConstNoOverloadWithInfo id
    unless (← getConstInfo c).levelParams.isEmpty do
      throwError "materialize_value: {c} is universe polymorphic"
    materializeValue c (mkConst c)
  | `(materialize_value $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_value: {e} is not closed"
    materializeValue ((← getCurrNamespace) ++ id.getId) e

open Lit in
/-- `materialize_code foo` defines `foo.lit`, the value of the code `foo` as a
literal (calling the literals of the code materialized before), and
`foo.lit_eq : foo = foo.lit`; `materialize_code N := t` does the same for the
closed code term `t`, as `N.lit` and `N.lit_eq`. -/
syntax "materialize_code " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_code $id:ident) => liftTermElabM do
    let foo ← realizeGlobalConstNoOverloadWithInfo id
    materialize foo (mkConst foo)
  | `(materialize_code $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_code: {e} is not closed"
    materialize ((← getCurrNamespace) ++ id.getId) e

open Lit in
/-- `materialize_flat_code` is `materialize_code` for code whose blocks are
built with `++` nested to the left (rows appended one by one, …), which the
kernel's evaluation would rebuild once for every `++` above them: `N.lit_eq`
goes through the code with each block flattened (`flattenCode`), which the
kernel evaluates in time linear in its length. Elsewhere it costs more to
unfold than it saves: the generators that decide much at each step, or
nest their appends to the right. It can cost far more: 3DES's x86-64
literals took 0.6 s with `materialize_code` and 40 s with it. Use it only
where measuring the file shows it faster. -/
syntax "materialize_flat_code " ident (" := " term)? : command

open Lit in
elab_rules : command
  | `(materialize_flat_code $id:ident) => liftTermElabM do
    let foo ← realizeGlobalConstNoOverloadWithInfo id
    materialize foo (mkConst foo) (flat := true)
  | `(materialize_flat_code $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    if e.hasMVar || e.hasFVar then throwError "materialize_flat_code: {e} is not closed"
    materialize ((← getCurrNamespace) ++ id.getId) e (flat := true)

open Lit in
/-- `materialize_template N := f x₁ … xₖ`, for code that is a function of
offsets (`Nat → … → Nat → α`): `N.lit`, that function as a literal with the
offsets free, and `N.lit_eq : f x₁ … xₖ = N.lit`, which the literals of code
calling `f x₁ … xₖ` then read rather than evaluating `f` at each call (see
"Templates" in `Lit.lean`). -/
syntax "materialize_template " ident " := " term : command

open Lit in
elab_rules : command
  | `(materialize_template $id:ident := $t) => liftTermElabM do
    let e ← instantiateMVars (← Term.elabTermAndSynthesize t none)
    materializeTemplate ((← getCurrNamespace) ++ id.getId) e

namespace Lit

/-- The value `v` of a constant with a literal, and the code it unfolds to, a
few definitions deep (each with its head unfolded, while that is a definition
of this project's code): a goal can name any of them for the constant, as a
generic proof's `exchangeWith c mq` for `exchangeP256 := Cfg.exchangeJA p256 …`,
which unfolds to it. -/
meta def unfoldChain (env : Environment) (mods : Array Name) (v : Expr) (depth : Nat := 4) :
    Array Expr := Id.run do
  let ok (e : Expr) := e.isApp && e.getAppFn.isConst && !e.hasLooseBVars
  unless ok v do return #[]
  let mut out := #[v]
  let mut cur := v
  for _ in [0:depth] do
    let .const g ls := cur.getAppFn | break
    unless codeModule env mods g do break
    let some (.defnInfo d) := env.find? g | break
    let next := ((d.value.instantiateLevelParams d.levelParams ls).betaRev cur.getAppRevArgs).headBeta
    unless ok next do break
    out := out.push next
    cur := next
  return out

/-- The closed subterms of `tgt` that are `v` up to its arguments: the same
head and number of arguments, each argument the same, or (an argument that is
not code, whose comparison could build it) definitionally equal by the
kernel's check (a configuration written another way). -/
meta def unfoldedOccurrences (tgt v : Expr) : MetaM (Array Expr) := do
  let f := v.getAppFn
  let n := v.getAppNumArgs
  let found ← IO.mkRef (#[] : Array Expr)
  tgt.forEach fun t => do
    if t.getAppFn == f && t.getAppNumArgs == n && !t.hasLooseBVars && !t.hasMVar then
      found.modify fun a => if a.contains t then a else a.push t
  let env ← getEnv
  let mut out := #[]
  for t in ← found.get do
    let mut same := true
    for i in [0:n] do
      let a := t.getArg! i
      let b := v.getArg! i
      if a == b then continue
      let ty ← whnfR (← inferType a)
      if ty.isAppOf ``Code || ty.isAppOf ``List || a.hasFVar ||
          !Kernel.isDefEqGuarded env {} a b then
        same := false
        break
    if same then out := out.push t
  return out

/-- With `VG_RW_LIT_REPORT` set to a file, a line there for each code that
`rw_lit` found unfolded (`unfoldChain`) rather than named: where a proof
names the code by its generator. -/
meta def reportUnfolded (N : Name) (v : Expr) : MetaM Unit := do
  let some path ← IO.getEnv "VG_RW_LIT_REPORT" | return
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn s!"{← getMainModule} {N} {v.getAppFn.constName!}"

end Lit

open Elab Tactic Lit in
/-- Rewrites each code of the goal that has a literal (`materialize_code`) to it. -/
elab "rw_lit" : tactic => withMainContext do
  -- Only code whose head constant the goal mentions can occur in it.
  let used := (← instantiateMVars (← getMainTarget)).getUsedConstantsAsSet
  let env ← getEnv
  let mods := env.header.moduleNames
  -- (`litNames` scans every constant of the project's modules: once a call.)
  let names := litNames env
  for N in names do
    let lhs ← lhsOf N
    -- A constant's code as the goal may have it unfolded: a generic proof's
    -- `Cfg.verify p384` for `verifyP384 := Cfg.verify p384`. Rewritten as a whole
    -- (`N.lit_eq` at `value = N.lit`, which the kernel checks by delta), rather than
    -- unfolded below, where the kernel would build the code again from the
    -- functions it is made of (e.g. 30 s rather than 2 s for P-384's verification).
    if let .const c [] := lhs then
      if let some (.defnInfo d) := env.find? c then
        if d.levelParams.isEmpty then
          for v in unfoldChain env mods d.value do
            unless used.contains v.getAppFn.constName! do continue
            let tgt ← instantiateMVars (← getMainTarget)
            for t in ← unfoldedOccurrences tgt v do
              let tgt ← instantiateMVars (← getMainTarget)
              let ty ← inferType lhs
              let u ← getLevel ty
              -- `N.lit_eq` at `t = N.lit`, which the kernel checks by delta.
              let prf ← mkExpectedTypeHint (mkConst (N ++ `lit_eq))
                (mkApp3 (mkConst ``Eq [u]) ty t (mkConst (N ++ `lit)))
              let motive ← withLocalDeclD `y ty fun y =>
                mkLambdaFVars #[y] (tgt.replace fun x => if x == t then some y else none)
              let g ← getMainGoal
              let tgt' := tgt.replace fun x => if x == t then some (mkConst (N ++ `lit)) else none
              replaceMainGoal [← g.replaceTargetEq tgt'
                (mkApp6 (mkConst ``congrArg [u, 1]) ty (mkSort 0) t (mkConst (N ++ `lit)) motive prf)]
              reportUnfolded N v
    unless lhs.getAppFn.isConst && used.contains lhs.getAppFn.constName! do continue
    let tgt ← instantiateMVars (← getMainTarget)
    if (tgt.find? (· == lhs)).isNone then continue
    let g ← getMainGoal
    let r ← g.rewrite tgt (mkConst (N ++ `lit_eq))
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)
  -- The definitions of the goal that lead to constants with a literal
  -- (`materialize_table`, code used other than as a call), unfolded, and
  -- those constants rewritten to their literals.
  -- Each is rewritten on its own, and then in the goal with one `congrArg`:
  -- the goal can be large (a hint of `taint_decide`), and the kernel
  -- instantiates the motive of each rewrite of it.
  let tgt ← instantiateMVars (← getMainTarget)
  for s in ← reachingSubterms names tgt do
    let some (s', prf) ← unfoldToLits .anonymous s (some names) | continue
    let g ← getMainGoal
    let tgt ← instantiateMVars (← g.getType)
    let ty ← inferType s
    let motive ← withLocalDeclD `y ty fun y =>
      mkLambdaFVars #[y] (tgt.replace fun t => if t == s then some y else none)
    let eqPrf := mkApp6 (mkConst ``congrArg [← getLevel ty, 1]) ty (mkSort 0) s s' motive prf
    replaceMainGoal [← g.replaceTargetEq (tgt.replace fun t => if t == s then some s' else none) eqPrf]

/-- `decide +kernel`, after rewriting the code constants of the goal to their
literals (`rw_lit`). -/
macro "lit_decide" : tactic => `(tactic| (rw_lit; decide +kernel))

end VG
