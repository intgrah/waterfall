import Waterfall
import Waterfall.Observe

open Lean Meta Elab Tactic Waterfall Waterfall.Observe
namespace ExhaustedBatchFixture

-- Three five-action root trials precede the depth-one trial on False. Action16
-- exhausts the global allowance there. Neither ordinary generator middleware nor
-- the additive provider may be consulted for any subsequent structural batch.
private def checkExhaustedGenerators (lazy : Bool) : TacticM Unit := do
  let outer ← Tactic.saveState
  let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
  setGoals [root.mvarId!]
  let dispatched ← IO.mkRef 0
  let lateEnumeration ← IO.mkRef 0
  let lateProvider ← IO.mkRef 0
  let accepted ← IO.mkRef 0
  let hooks : Hooks := {
    around := fun span _ body => do
      if span.phase == .action then dispatched.modify (· + 1)
      if span.phase == .enumerate && (← dispatched.get) >= 16 then
        lateEnumeration.modify (· + 1)
      body
    extraMoves := fun _ _ _ _ _ => do
      if (← dispatched.get) >= 16 then lateProvider.modify (· + 1)
      return #[]
    accepted := fun _ _ => accepted.modify (· + 1) }
  let closed ← tryCatchRuntimeEx (do
    discard <| run {effort := 16, lazy} #[] hooks
    pure true) fun _ => pure false
  let assigned ← root.mvarId!.isAssigned
  outer.restore true
  unless !closed && !assigned && (← dispatched.get) == 16 do
    throwError "exhaustion fixture did not reach its intended frontier"
  unless (← lateEnumeration.get) == 0 && (← lateProvider.get) == 0 do
    throwError "generated a batch after the last permitted action"
  unless (← accepted.get) == 0 do throwError "failed search published an accepted step"

example : True := by
  run_tac checkExhaustedGenerators true
  trivial
example : True := by
  run_tac checkExhaustedGenerators false
  trivial

-- Both sibling goals need their own action. The second action is the last one
-- allowed, yet complete continuation unwinding and accepted callbacks must run.
-- The unchanged exact-plan interpreter must replay the resulting two steps.
elab "check_last_action" : tactic => do
  let root ← getMainGoal
  let sibling ← mkFreshExprSyntheticOpaqueMVar (← root.getType)
  setGoals [root, sibling.mvarId!]
  let saved ← Tactic.saveState
  let accepted ← IO.mkRef 0
  let hooks : Hooks := {accepted := fun _ _ => accepted.modify (· + 1)}
  let report ← capture {effort := 2} #[] "last-permitted-action" true true {} hooks
  let some plan := report.plan | throwError "final-action proof did not produce a plan"
  unless report.success && plan.steps.size == 2 && (← accepted.get) == 2 do
    throwError "last permitted action lost a sibling or accepted callback"
  checkComplete [root, sibling.mvarId!]
  let .ok roundtrip := fromJson? (α := Plan) (toJson plan)
    | throwError "recorded plan did not round-trip"
  saved.restore true
  replay roundtrip #[] "last-permitted-action" hooks
  checkComplete [root, sibling.mvarId!]

example : (0 : Nat) = 0 := by check_last_action

-- Closing the first root at the limit must not admit an unproved sibling or
-- publish its callback. The caller's complete goal state must be restored.
elab "check_unclosed_sibling" : tactic => do
  let outer ← Tactic.saveState
  let root ← mkFreshExprSyntheticOpaqueMVar (← Term.elabTerm (← `((0 : Nat) = 0)) none)
  let sibling ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
  setGoals [root.mvarId!, sibling.mvarId!]
  let accepted ← IO.mkRef 0
  let hooks : Hooks := {accepted := fun _ _ => accepted.modify (· + 1)}
  let report ← capture {effort := 1} #[] "unclosed-sibling" true true {} hooks
  let assigned ← root.mvarId!.isAssigned
  let siblingAssigned ← sibling.mvarId!.isAssigned
  outer.restore true
  unless !report.success && report.plan.isNone && !assigned && !siblingAssigned &&
      (← accepted.get) == 0 do
    throwError "exhaustion accepted an incomplete continuation"

example : True := by check_unclosed_sibling; trivial
end ExhaustedBatchFixture
