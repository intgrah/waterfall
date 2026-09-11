import Waterfall

open Waterfall Lean Elab Tactic

example (P : Prop) (h : P) : P := by waterfall
example (P : Prop) (h : P) : P := by waterfall (mode := .search)
example (P : Prop) (h : P) : P := by waterfall (mode := .committed)
example (P : Prop) (h : P) : P := by
  waterfall (effort := 1) (lazy := false) (deferChecks := true)
example (P : Prop) (h : P) : P := by
  waterfall (config := {effort := 1, mode := .committed})
example (P : Prop) (h : P) : P := by
  fail_if_success waterfall (effort := 0)
  waterfall (attemptHeartbeats := 20000000)

-- General callback configuration uses the same mode hooks and engine API.
example (P : Prop) (h : P) : P := by
  fail_if_success run_tac
    discard <| Waterfall.run {} #[] { Mode.search.hooks with
      policy := ⟨Unit, (), fun _ _ => pure false⟩ }
  run_tac discard <| Waterfall.run {} #[] { Mode.search.hooks with
    trials := diagonalTrials 1 }

example (P : Prop) (h : P) : P := by
  fail_if_success run_tac
    discard <| Waterfall.run {} #[] { Mode.search.hooks with
      trials := fun _ => #[(0, 0)] }
  waterfall
