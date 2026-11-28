module

public meta import Lean.Meta.Tactic.Simp.Simproc
public meta import Lean.Meta.WHNF
public meta import Lean.Meta.Match.MatcherInfo

/-!
# Unfolding a definition on constructors without its equation lemmas

`simp only [f]` rewrites with `f`'s equation lemmas, which it realizes in the
module that runs it. Those of `f`'s `match` (and its `splitter`) are realized
under a private name, so no importer can reuse them: every module that unfolds
an ISA's `exec` this way carried its own copy, up to megabytes each.

`unfoldStep?` instead unfolds `f a₁ … aₙ` by definitional reduction: it
unfolds `f` and reduces the `match` it starts with, which needs the arguments
it matches on to be constructors. The result is definitionally equal, so a
`dsimproc` built on it (`X86_64.reduceExec`, …) needs no proof term and
realizes nothing. Pass the `dsimproc` to `simp` in place of the definition.
-/

public meta section

namespace VG

open Lean Meta

/-- `e`, a definition applied to arguments, unfolded once and its outer
`match` reduced, if the arguments it matches on are constructors; `none`
otherwise (the `match` would be stuck). As an equation lemma would, this
leaves the chosen case's right-hand side as it is, inner `match`es included. -/
def unfoldStep? (e : Expr) : MetaM (Option Expr) := do
  let some e' ← withTransparency .all <| unfoldDefinition? e | return none
  match ← withTransparency .all <| reduceMatcher? e'.headBeta with
  | ReduceMatcherResult.reduced e'' => return some e''.headBeta
  | _ => return none

end VG
