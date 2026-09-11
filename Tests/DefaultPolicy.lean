import Waterfall
import Waterfall.Observe

open Lean Meta Elab Tactic Waterfall Waterfall.Observe

namespace DefaultPolicyFixture

-- This nonrecursive proposition needs its constructor; no premise remains
-- after its natural-number argument is inferred from the target. The default
-- admission cost must postpone this closing move until a depth-one trial.
inductive Tag : Nat → Prop where
  | tag (n : Nat) : Tag n

elab "check_public_default" : tactic => do
  let saved ← Tactic.saveState
  let report ← capture {effort := 100} #[] "actual-default" false true
  let some plan := report.plan | throwError "default fixture failed: {report.error}"
  unless plan.steps.size == 1 do throwError "default fixture took an unexpected route"
  let some step := plan.steps[0]? | throwError "missing default proof step"
  unless step.action.group == .close && step.cost == 1 &&
      step.remaining == 1 && step.strength == 1 && step.children == 0 do
    throwError "public default did not enforce constructor admission"
  saved.restore true
  -- No adapter and no supplied Hooks: exact replay sees the actual default too.
  replay plan #[] "actual-default"

example : Tag 37 := by check_public_default

end DefaultPolicyFixture

-- General callbacks change policy over the current graph, not its operations.
-- These examples do not reconstruct a historical engine revision.
namespace PublicPolicyExamples

elab "wf_diagonal" : tactic => do
  discard <| Waterfall.run {effort := 1000} #[] {
    trials := Waterfall.diagonalTrials 1 }

elab "wf_free_closers" : tactic => do
  discard <| Waterfall.run {effort := 1000} #[] {
    cost := fun _ _ c => pure (if c.action.group == .close then 0 else c.move.cost) }

example (n : Nat) : n = n := by wf_diagonal
example : True := by wf_free_closers

end PublicPolicyExamples
