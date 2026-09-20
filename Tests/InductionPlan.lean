import waterfall
import waterfall.InductionPlan

open Lean Elab Tactic waterfall

namespace waterfallInductionPlanTest

private meta def fixture (coverage generalized cases ordinal : Nat) : InductionPlan.Plan :=
  { move := {
      label := "induction fixture"
      induction := .data
      motive := if generalized == 0 then .direct else .localGeneralization
      run := pure () }
    summary := {
      coveredCalls := coverage
      generalized
      expectedCases := cases }
    ordinal }

private meta def candidate (index coverage generalized : Nat) (positions : Array Nat)
    (motive : InductionMotive) : Candidate :=
  { action := { group := .induction, index }
    move := {
      label := s!"candidate {index}"
      induction := .data
      inductionSummary := some {
        coveredCalls := coverage
        changingArguments := positions
        generalized }
      motive
      run := pure () } }

-- Coverage dominates optional motive strengthening, while exact duplicate
-- schemes alone may be removed. Lower-quality alternatives remain reachable.
example : True := by
  run_tac
    let broad := fixture 3 0 2 2
    let narrow := fixture 1 0 2 0
    let generalized := fixture 3 2 2 1
    let duplicate := { broad with ordinal := 9 }
    let plans := InductionPlan.ordered #[narrow, generalized, duplicate, broad]
    unless plans.size == 3 && plans[0]?.map (·.ordinal) == some 9 &&
        plans[1]?.map (·.ordinal) == some 1 &&
        plans[2]?.map (·.ordinal) == some 0 do
      throwError "induction-plan dominance or conservative deduplication changed"
  trivial

-- Goal analysis attaches a summary to each actual induction operation.
elab "check_induction_metadata" : tactic => do
  let moves ← waterfall.movesFor (← getMainGoal) #[] 1 2 .induction
  let inductions := moves.filter (fun move : Move => move.induction != .none)
  unless !inductions.isEmpty && inductions.all (·.inductionSummary.isSome) do
    throwError "an induction operation lacks typed plan metadata"
  evalTactic (← `(tactic| simp))

example (xs : List Nat) : xs.length = xs.length := by check_induction_metadata

-- Incomparable schemes retain generator order, including generalized motives.
-- A strict coverage superset may lead, with its direct motive first.
example : True := by
  run_tac
    let nGen := candidate 0 4 1 #[0, 1] .localGeneralization
    let nDirect := candidate 1 4 0 #[0, 1] .direct
    let mGen := candidate 2 3 1 #[1, 2] .localGeneralization
    let mDirect := candidate 3 3 0 #[1, 2] .direct
    let mindGen := candidate 4 9 3 #[0, 1, 2] .localGeneralization
    let mindDirect := candidate 5 9 0 #[0, 1, 2] .direct
    let hooks := InductionPlan.hooks
    let span : Span := { phase := .enumerate, group := some .induction }
    let some incomparable ← hooks.order (← getMainGoal) span #[nGen, nDirect, mGen, mDirect]
      | throwError "induction planner returned no permutation"
    unless incomparable == #[nGen.action, nDirect.action, mGen.action, mDirect.action] do
      throwError "incomparable induction schemes lost stable generator order"
    let some dominant ← hooks.order (← getMainGoal) span
        #[nGen, nDirect, mindGen, mindDirect]
      | throwError "induction planner returned no dominance permutation"
    unless dominant == #[mindDirect.action, mindGen.action, nGen.action, nDirect.action] do
      throwError "strict induction dominance was not selected"
  trivial

end waterfallInductionPlanTest
