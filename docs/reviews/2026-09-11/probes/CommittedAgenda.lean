import Waterfall
import Waterfall.Observe

open Lean Meta Elab Tactic Waterfall Waterfall.Observe
set_option Elab.async false

-- Mirror the existing deferred-sibling regression: the necessary induction is
-- now on the FIRST sibling, and the LAST sibling must wait for its witness.
-- The policy should try earlier agenda entries after the last has no candidate.
example : ∃ n : Nat, n = 1 ∧ n = 1 := by
  run_tac
    evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))
    let [witness, left, right] ← getGoals | throwError "unexpected sibling agenda"
    setGoals [left, right]
    let saved ← Tactic.saveState
    let hooks : Hooks := { Committed.hooks with
      trials := fun _ => #[(1, 1)]
      cost := fun _ _ c => pure (if c.move.label == "dependent closer" then c.move.cost else 1000)
      extraMoves := fun g _ _ _ group => do
        let isInduction := g == left
        if group != (if isInduction then .induction else .basic) then return #[]
        if g == right && !(← witness.isAssigned) then return #[]
        if g != left && g != right then return #[]
        return #[{
          label := "dependent closer"
          role := `prepare
          induction := if isInduction then .data else .none
          run := do
            if g == left then witness.assign (mkNatLit 1)
            g.withContext g.refl
            setGoals [] }] }
    let report ← capture { effort := 2 } #[] "earlier-induction" false true {} hooks
    IO.println s!"forward agenda success={report.success} error={report.error}"
    -- Confirm the same exact actions can close the proof merely by exchanging
    -- siblings. This probe reports the bug, then leaves a kernel-checked proof.
    saved.restore true
    setGoals [right, left]
    let reordered ← capture { effort := 2 } #[] "last-induction" false true {} hooks
    IO.println s!"reversed agenda success={reordered.success} error={reordered.error}"
    unless reordered.success do throwError "control failed: {reordered.error}"
