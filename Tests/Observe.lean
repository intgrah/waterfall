import waterfall
import waterfall.Observe

open Lean Meta Elab Tactic waterfall waterfall.Observe

namespace waterfallObserveTest

private def checkCosts (rows : Array Row) : TacticM Unit := do
  unless rows.any (·.span.phase == .run) do throwError "missing root span"
  for row in rows do
    let children := rows.filter (·.parent == some row.id)
    let nanos := children.foldl (fun n child => n + child.inclusive.nanos) 0
    let beats := children.foldl (fun n child => n + child.inclusive.heartbeats) 0
    unless row.inclusive.nanos == row.exclusive.nanos + nanos &&
        row.inclusive.heartbeats == row.exclusive.heartbeats + beats do
      throwError "inclusive/exclusive cost mismatch"
    if let some parent := row.parent then
      unless rows.any (·.id == parent) do throwError "orphaned cost span"

-- Replay follows failed-work name allocation. It cannot depend on diagnostic
-- user names, raw FVar/MVar IDs, or the search's discarded branches.
elab "record_and_replay" : tactic => do
  let saved ← Tactic.saveState
  let report ← capture { effort := 4000 } #[] "fixture-source-and-theory"
  unless report.success do throwError "recorded search failed: {report.error}"
  checkCosts report.rows
  let some plan := report.plan | throwError "missing accepted plan"
  let .ok roundtrip := fromJson? (α := Plan) (toJson plan)
    | throwError "plan JSON did not roundtrip"
  saved.restore true
  for _ in [:20] do discard <| mkFreshUserName `deliberate_unused_name
  replay roundtrip #[] "fixture-source-and-theory"

example (P : Prop) (h : P) : P := by record_and_replay

inductive Mark : Nat → Prop where
  | zero : Mark 0
  | one : Mark 1

inductive Allowed : Nat → Prop where
  | one : Allowed 1

-- The wrong first witness must be rejected by its sibling. Recording only
-- local successes would produce an invalid plan for this true proposition.
example : ∃ n, Mark n ∧ Allowed n := by record_and_replay

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

example (xs : List Nat) : append xs [] = xs := by record_and_replay

elab "check_stale_plans" : tactic => do
  let saved ← Tactic.saveState
  let report ← capture {} #[] "source" false true
  let some plan := report.plan | throwError "missing plan"
  saved.restore true
  let initial ← Canonical.snapshot (← getUnsolvedGoals)
  let rejected (bad : Plan) (key : String) : TacticM Unit := do
    let failed ← tryCatchRuntimeEx (do replay bad #[] key; pure false) fun _ => pure true
    unless failed do throwError "tampered plan accepted"
    unless (← Canonical.snapshot (← getUnsolvedGoals)) == initial do
      throwError "replay failure changed caller state"
  rejected plan "wrong source"
  rejected { plan with input := "wrong root" } "source"
  rejected { plan with steps := #[] } "source"
  let some first := plan.steps[0]? | throwError "expected nonempty plan"
  rejected { plan with steps := plan.steps.set! 0 { first with children := first.children + 1 } } "source"
  replay plan #[] "source"

example : True := by check_stale_plans

-- Deadlines are cooperative, not hard thread timers. Both kinds of middleware
-- failure must preserve the caller's goal and expose an explicit failed report.
elab "check_observer_limits" : tactic => do
  let original ← Canonical.snapshot (← getUnsolvedGoals)
  let report ← capture {} #[] "limits" true false { deadlineNanos := some 0 }
  if report.success then throwError "expired deadline accepted"
  unless report.error.isSome do throwError "missing deadline failure"
  unless (← Canonical.snapshot (← getUnsolvedGoals)) == original do
    throwError "deadline changed proof state"
  checkCosts report.rows
  let hooks : Hooks := {
    around := fun span outcome body =>
      Control.around { slice := fun _ => pure (some 0) } span outcome body }
  let failed ← tryCatchRuntimeEx (do discard <| waterfall.run {} #[] hooks; pure false) fun _ => pure true
  unless failed do throwError "zero resource allowance accepted"
  unless (← Canonical.snapshot (← getUnsolvedGoals)) == original do
    throwError "resource middleware changed proof state"
  evalTactic (← `(tactic| trivial))

example : True := by check_observer_limits

-- Assertions run outside the failed proof: their own failure cannot masquerade
-- as successful rejection of False, as it could under fail_if_success.
example : True := by
  run_tac
    let saved ← Tactic.saveState
    let impossible ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [impossible.mvarId!]
    let report ← capture { effort := 12 } #[] "false"
    if report.success || report.plan.isSome then throwError "false search accepted"
    unless report.rows.any (·.outcome.success == some false) do
      throwError "ordinary failed actions were not recorded"
    checkCosts report.rows
    saved.restore true
  trivial

-- Importing observation code does not force it into an ordinary probe run.
example (P : Prop) (h : P) : P := by waterfall? (effort := 20)

end waterfallObserveTest
