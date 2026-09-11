import Waterfall
import Waterfall.Observe

open Lean Meta Elab Tactic Waterfall Waterfall.Observe

namespace ContextPolicyFixture

-- Force a failing choice before each successful sibling. Both policy callbacks
-- assign the goal and an unrelated witness temporarily. Those assignments must
-- disappear, whereas IO counters deliberately survive snapshot restoration.
elab "check_context_callbacks" : tactic => do
  let root ← getMainGoal
  let sibling ← root.withContext <| mkFreshExprSyntheticOpaqueMVar (← root.getType)
  let sentinel ← root.withContext <| mkFreshExprSyntheticOpaqueMVar (mkConst ``True)
  setGoals [root, sibling.mvarId!]
  let saved ← Tactic.saveState
  let failed ← IO.mkRef 0
  let orders ← IO.mkRef 0
  let costs ← IO.mkRef 0
  let inspect (g : MVarId) (span : Span) : TacticM Unit := do
    unless span.phase == .node && span.depth == 1 && span.strength == 2 &&
        span.group.isNone && span.action.isNone do
      throwError "policy received a different span from search or replay"
    unless (← getMainGoal) == g && !(← g.isAssigned) &&
        !(← sentinel.mvarId!.isAssigned) && (← g.getType).isConstOf ``True do
      throwError "policy received a stale or mutated input snapshot"
    unless (← getLCtx).any (fun d => !d.isImplementationDetail && d.type.isConstOf ``Nat) do
      throwError "policy was called outside the goal's local context"
    g.assign (mkConst ``True.intro)
    sentinel.mvarId!.assign (mkConst ``True.intro)
    setGoals []
  let hooks : Hooks := {
    trials := fun _ => #[(1, 2)]
    cost := fun g span _ => do
      inspect g span
      costs.modify (· + 1)
      pure 1
    order := fun g span candidates => do
      inspect g span
      orders.modify (· + 1)
      -- The appended choices are first; no original selector is removed.
      let n := candidates.size - 2
      pure <| some ((candidates.extract n candidates.size ++ candidates.take n).map (·.action))
    extraMoves := fun g _ _ _ group => pure <|
      if group != .close then #[] else #[
        { label := "fixture failed assignment", run := do
            failed.modify (· + 1)
            g.assign (mkConst ``True.intro)
            setGoals []
            throwError "deliberate failed action" },
        { label := "fixture successful sibling", run := do
            unless !(← g.isAssigned) && !(← sentinel.mvarId!.isAssigned) do
              throwError "temporary policy or failed-action assignment escaped"
            g.assign (mkConst ``True.intro)
            setGoals [] }] }
  let report ← capture {effort := 4} #[] "context-callbacks" false true {} hooks
  let some plan := report.plan | throwError "context fixture failed: {report.error}"
  unless report.success && plan.steps.size == 2 && (← failed.get) == 2 &&
      (← orders.get) == 2 && (← costs.get) == 4 && !(← sentinel.mvarId!.isAssigned) do
    throwError "context fixture did not exercise both failed choices and siblings"
  checkComplete [root, sibling.mvarId!]
  saved.restore true
  replay plan #[] "context-callbacks" hooks
  unless (← failed.get) == 2 && (← orders.get) == 2 && (← costs.get) == 6 &&
      !(← sentinel.mvarId!.isAssigned) do
    throwError "exact replay searched alternatives or changed policy inputs"
  checkComplete [root, sibling.mvarId!]

example (n : Nat) : True := by check_context_callbacks

-- A policy error must also unwind the entire caller state. This tests callback
-- exceptions separately from an ordinary failed proof action.
example : True := by
  run_tac
    let before ← Canonical.snapshot (← getUnsolvedGoals)
    let corrupt (g : MVarId) : TacticM Unit := do
      g.assign (mkConst ``True.intro)
      setGoals []
      throwError "deliberate policy error"
    for orderFailure in [true, false] do
      let hooks : Hooks := {
        order := fun g _ _ => do
          if orderFailure then corrupt g
          pure none
        cost := fun g _ _ => do
          corrupt g
          pure 0 }
      let error ← tryCatchRuntimeEx (do
        discard <| run {effort := 5} #[] hooks
        pure none) fun ex => return some (← ex.toMessageData.toString)
      unless error == some "deliberate policy error" &&
          (← Canonical.snapshot (← getUnsolvedGoals)) == before do
        throwError "policy exception damaged the caller or was silently ignored"
  trivial

end ContextPolicyFixture
