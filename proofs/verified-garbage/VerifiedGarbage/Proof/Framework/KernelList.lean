module


/-!
# List functions for the kernel

The kernel evaluates the taint analyses (`VG.Taint`), and is slow at the
library's list functions: they are structurally recursive, which compiles to
`brecOn`, and `==` and `≤` on `Nat` go through `Decidable` instances. The
functions here are the same functions written with `List.rec` and
`Nat.beq`/`Nat.ble` (which the kernel evaluates natively), each proven equal
to the library's, so that an analysis can be evaluated in these terms and
reasoned about in the library's.

Lean's compiler does not compile recursors, and the analyses' hints are
computed in compiled code (`Taint.hint`), so each function here is
`@[implemented_by]` the library's function it equals (`…_eq`). That changes
what compiled code runs, not what the kernel checks: the kernel checks every
hint, and the emitter's audit (`#assert_no_compiler_overrides`) rejects any
of these in the code it runs.
-/

@[expose] public section

namespace VG.KList

variable {α β : Type}

/-- The library's functions, which compiled code runs for those below (Lean's
compiler does not compile `List.rec` or `Nat.rec`). -/
def takeC {α : Type} (n : Nat) (xs : List α) : List α := xs.take n
def dropC {α : Type} (n : Nat) (xs : List α) : List α := xs.drop n
def anyC (l : List α) (p : α → Bool) : Bool := l.any p
def allC (l : List α) (p : α → Bool) : Bool := l.all p
def filterC (p : α → Bool) (l : List α) : List α := l.filter p
def findC (p : α → Bool) (l : List α) : Option α := l.find? p
def mapC (f : α → β) (l : List α) : List β := l.map f
def appendC (xs ys : List α) : List α := xs ++ ys

/-- List prefixes and suffixes evaluated through a direct natural-number recursor. -/
@[implemented_by takeC] def take {α : Type} (n : Nat) (xs : List α) : List α :=
  Nat.rec (fun _ => []) (fun _ ih xs => match xs with
    | [] => []
    | x :: xs => x :: ih xs) n xs
@[implemented_by dropC] def drop {α : Type} (n : Nat) (xs : List α) : List α :=
  Nat.rec (fun xs => xs) (fun _ ih xs => match xs with
    | [] => []
    | _ :: xs => ih xs) n xs
theorem take_eq {α : Type} (n : Nat) (xs : List α) : take n xs = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => exact congrArg (List.cons x) (ih xs)
theorem drop_eq {α : Type} (n : Nat) (xs : List α) : drop n xs = xs.drop n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => rfl
    | cons x xs => exact ih xs

@[implemented_by anyC] def any (l : List α) (p : α → Bool) : Bool := List.rec false (fun a _ ih => p a || ih) l

@[implemented_by allC] def all (l : List α) (p : α → Bool) : Bool := List.rec true (fun a _ ih => p a && ih) l

@[implemented_by filterC] def filter (p : α → Bool) (l : List α) : List α :=
  List.rec [] (fun a _ ih => bif p a then a :: ih else ih) l

@[implemented_by findC] def find? (p : α → Bool) (l : List α) : Option α :=
  List.rec none (fun a _ ih => bif p a then some a else ih) l

@[implemented_by mapC] def map (f : α → β) (l : List α) : List β := List.rec [] (fun a _ ih => f a :: ih) l

@[implemented_by appendC] def append (xs ys : List α) : List α := List.rec ys (fun a _ ih => a :: ih) xs

theorem any_eq (l : List α) (p : α → Bool) : any l p = l.any p := by
  induction l <;> simp_all [any]

theorem all_eq (l : List α) (p : α → Bool) : all l p = l.all p := by
  induction l <;> simp_all [all]

theorem filter_eq (p : α → Bool) (l : List α) : filter p l = l.filter p := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp_all [filter]

theorem find?_eq (p : α → Bool) (l : List α) : find? p l = l.find? p := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp_all [find?]

theorem map_eq (f : α → β) (l : List α) : map f l = l.map f := by
  induction l <;> simp_all [map]

theorem append_eq (xs ys : List α) : append xs ys = xs ++ ys := by
  induction xs <;> simp_all [append]

theorem beq_eq (a b : Nat) : Nat.beq a b = (a == b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

end VG.KList
