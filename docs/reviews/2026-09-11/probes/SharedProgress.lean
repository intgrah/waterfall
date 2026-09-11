import Waterfall
import Waterfall.Observe

open Lean Meta Elab Tactic Waterfall Waterfall.Observe
set_option Elab.async false

-- A positive-cost operation advances a shared witness while leaving the
-- selected proposition unchanged. Local shape equality is not state equality.
example : ∃ n : Nat, True ∧ n = 1 := by
  run_tac
    evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))
    let [witness, left, right] ← getGoals | throwError "unexpected agenda"
    setGoals [left, right]
    let saved ← Tactic.saveState
    let chooseWitness : TacticM Unit := do witness.assign (mkNatLit 1)
    let hooks : Hooks := {
      trials := fun _ => #[(1, 1)]
      cost := fun _ _ c => pure (if c.move.role == `fixture then c.move.cost else 1000)
      extraMoves := fun g _ _ _ group => do
        if group == .basic && g == left then
          return #[{ label := "choose shared witness", role := `fixture, run := chooseWitness }]
        if group == .close && (← witness.isAssigned) then
          return #[{ cost := 0, label := "close after witness", role := `fixture, run := do
            if g == left then g.assign (mkConst ``True.intro) else g.withContext g.refl
            setGoals [] }]
        return #[] }
    let report ← capture {effort := 3} #[] "shared-progress" false true {} hooks
    IO.println s!"shared witness search success={report.success} error={report.error}"
    saved.restore true
    -- Control: dispatching exactly that first operation manually allows the
    -- engine to complete the remaining route without any new capability.
    chooseWitness
    let control ← capture {effort := 2} #[] "after-shared-progress" false true {} hooks
    IO.println s!"after same witness action success={control.success} error={control.error}"
    unless control.success do throwError "control failed: {control.error}"
