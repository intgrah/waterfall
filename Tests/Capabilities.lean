import Waterfall
import Waterfall.Committed

open Lean Meta Elab Tactic Waterfall

namespace CapabilityTest

-- The representation is nonrecursive, but its registered view has an IH.
-- Test the operation itself so induction on the Nat index cannot mask a miss.
inductive Stamp : Nat → Prop where
  | mk (n : Nat) : Stamp n

@[induction_eliminator] def Stamp.induct
    {motive : (n : Nat) → Stamp n → Prop}
    (zero : motive 0 (.mk 0))
    (succ : ∀ n, motive n (.mk n) → motive (n + 1) (.mk (n + 1)))
    {n} (h : Stamp n) : motive n h := by
  cases h
  induction n with
  | zero => exact zero
  | succ n ih => exact succ n ih

@[cases_eliminator] def Stamp.view
    {motive : (n : Nat) → Stamp n → Prop}
    (zero : motive 0 (.mk 0))
    (succ : ∀ n, motive (n + 1) (.mk (n + 1)))
    {n} (h : Stamp n) : motive n h := by
  cases h
  cases n with
  | zero => exact zero
  | succ n => exact succ n

elab "choose_operation " label:str : tactic => withMainContext do
  let saved ← Tactic.saveState
  let moves ← operations (← getMainGoal) #[]
  saved.restore true
  let some move := moves.find? (·.label == label.getString)
    | throwError "missing operation {label.getString}"
  move.run

example (P : Nat → Prop) (zero : P 0) (step : ∀ n, P n → P (n+1))
    (n : Nat) (h : Stamp n) : P n := by
  choose_operation "induction h"
  · exact zero
  · rename_i n ih
    exact step n ih

example (P : Nat → Prop) (zero : P 0) (step : ∀ n, P (n+1))
    (n : Nat) (h : Stamp n) : P n := by
  choose_operation "cases hypothesis registered"
  · exact zero
  · exact step _

-- Registered cases must not remove raw cases; the raw move still has one goal.
example (n : Nat) (h : Stamp n) : True := by
  choose_operation "cases hypothesis"
  trivial

set_option tactic.customEliminators false in
example (n : Nat) (h : Stamp n) : True := by
  fail_if_success choose_operation "cases hypothesis registered"
  fail_if_success choose_operation "induction h"
  trivial

-- A local dependent function can return data rather than a proposition.
example (P : Nat → Type) (h : ∀ n, P n) (n : Nat) : P n := by
  waterfall (effort := 100)

example (P : Nat → Type) (h : ∀ n, P n) (n : Nat) : P n := by
  waterfall (mode := .committed) (effort := 100)

-- The conclusion cannot reduce until an implicit data argument is chosen.
inductive Cover where
  | keep
  | bump
  | add (amount : Nat)
  | unused (value : Nat)

def render : Cover → Nat → Nat
  | .keep, n => n
  | .bump, n => n + 1
  | .add k, n => n + k
  | .unused _, n => n

inductive Wrapped (P : Nat → Prop) : Nat → Prop where
  | pack {cover : Cover} {n : Nat} : P n → Wrapped P (render cover n)

example (P : Nat → Prop) (n : Nat) (h : P n) : Wrapped P n := by
  fail_if_success choose_operation "constructor CapabilityTest.Wrapped.pack"
  choose_operation "constructor CapabilityTest.Wrapped.pack witness 1 CapabilityTest.Cover.keep"
  exact h

example (P : Nat → Prop) (n : Nat) (h : P n) : Wrapped P n := by
  waterfall (effort := 1000)

example (P : Nat → Prop) (n : Nat) (h : P n) : Wrapped P n := by
  waterfall (mode := .committed) (effort := 1000)

-- Constructor fields inferred from the target need no explicit term enumerator.
example (P : Nat → Prop) (n k : Nat) (h : P n) : Wrapped P (n + k) := by
  choose_operation "constructor CapabilityTest.Wrapped.pack witness 1 CapabilityTest.Cover.add"
  exact h

-- A field absent from the conclusion is still an obligation. Losing it would
-- leave an unassigned metavariable hidden inside the final proof term.
example (P : Nat → Prop) (n : Nat) (h : P n) : Wrapped P n := by
  choose_operation "constructor CapabilityTest.Wrapped.pack witness 1 CapabilityTest.Cover.unused"
  run_tac
    unless (← getUnsolvedGoals).length == 2 do throwError "lost a constructor field"
  all_goals first | exact h | exact 0

example : True := by
  fail_if_success have : Wrapped (fun _ => False) 0 := by waterfall (effort := 50)
  trivial

end CapabilityTest
