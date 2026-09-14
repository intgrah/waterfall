import Tests.Capabilities
import waterfall.Observe

open Lean Meta Elab Tactic waterfall waterfall.Observe

elab "compare_modes" : tactic => do
  let saved ← Tactic.saveState
  for committed in [false, true] do
    saved.restore true
    let report ← capture {effort := 3000} #[] "readability" false true {}
      (if committed then Committed.hooks else {})
    let some plan := report.plan | throwError "reference proof failed: {report.error}"
    IO.println s!"REFERENCE committed={committed} plan={(toJson plan).compress}"
  checkComplete (← getGoals)

set_option maxHeartbeats 0
set_option maxRecDepth 4096

example (P : Nat → Type) (h : ∀ n, P n) (n : Nat) : P n := by compare_modes
example (P : Nat → Prop) (n : Nat) (h : P n) : CapabilityTest.Wrapped P n := by compare_modes
example : ∃ n : Nat, n = 1 ∧ n ≠ 0 := by compare_modes

def concat : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: concat xs ys

example (xs : List Nat) : concat xs [] = xs := by compare_modes
example (P : Nat → Prop) (zero : P 0) (step : ∀ n, P n → P (n+1))
    (n : Nat) (h : CapabilityTest.Stamp n) : P n := by compare_modes
