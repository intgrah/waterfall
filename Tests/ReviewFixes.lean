import waterfall
import waterfall.Observe

open Lean Meta Elab Tactic waterfall waterfall.Observe
set_option Elab.async false
set_option maxHeartbeats 0

namespace ReviewFixes

-- The last sibling cannot close until induction on an earlier sibling supplies
-- their witness. An empty induction expansion must continue the agenda scan.
example : ∃ n : Nat, n = 1 ∧ n = 1 := by
  run_tac
    evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))
    let [witness, left, right] ← getGoals | throwError "unexpected sibling agenda"
    setGoals [left, right]
    let saved ← Tactic.saveState
    let hooks : Hooks := { Committed.hooks with
      trials := fun _ => #[(1, 1)]
      cost := fun _ _ c => pure (if c.move.role == `fixture then c.move.cost else 1000)
      extraMoves := fun g _ _ _ group => do
        let isInduction := g == left
        if group != (if isInduction then .induction else .basic) then return #[]
        if g == right && !(← witness.isAssigned) then return #[]
        if g != left && g != right then return #[]
        return #[{
          label := "dependent closer", role := `fixture
          induction := if isInduction then .data else .none
          run := do
            if g == left then witness.assign (mkNatLit 1)
            g.withContext g.refl
            setGoals [] }] }
    let report ← capture {effort := 2} #[] "earlier-induction" true true {} hooks
    let some plan := report.plan | throwError "earlier sibling skipped: {report.error}"
    unless report.success && plan.steps.size == 2 &&
        plan.steps[0]!.focus == 0 && plan.steps[0]!.induction == .data &&
        (report.rows.filter (·.span.phase == .action)).size == 2 do
      throwError "induction scan changed scheduling or attempt accounting"
    saved.restore true
    replay plan #[] "earlier-induction" hooks

-- Continuing past an empty expansion must NOT resume the tail after a yielded
-- induction's continuation fails. Commitment still discards the right witness.
example : True := by
  run_tac
    let saved ← Tactic.saveState
    let goal ← mkFreshExprSyntheticOpaqueMVar (← Term.elabType (← `(term| ∃ n : Nat, n = 1)))
    let root := goal.mvarId!
    setGoals [root]
    let tail ← IO.mkRef false
    let progressed ← IO.mkRef false
    let hooks : Hooks := { Committed.hooks with
      trials := fun _ => #[(1, 1)]
      cost := fun _ _ c => pure (if c.move.role == `fixture then 1 else 1000)
      extraMoves := fun g _ _ _ group => do
        if g != root || group != .induction then return #[]
        return #[
          {label := "wrong witness", role := `fixture, induction := .data,
           run := do
            evalTactic (← `(tactic| refine ⟨0, ?_⟩))
            progressed.set true},
          {label := "right witness", role := `fixture, induction := .data, run := do
            tail.set true
            evalTactic (← `(tactic| exact ⟨1, rfl⟩))}] }
    let report ← capture {effort := 2} #[] "induction-commitment" false false {} hooks
    unless !report.success && (← progressed.get) && !(← tail.get) do
      throwError "committed induction backtracked after local progress"
    saved.restore true
  trivial

-- A provider can advance a witness visible only in another pending goal. Test
-- both policies and enumeration modes, including retained-plan replay.
private def sharedProgress (committed lazy : Bool) : TacticM Unit := do
  evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))
  let [witness, left, right] ← getGoals | throwError "unexpected agenda"
  setGoals [left, right]
  let saved ← Tactic.saveState
  let hooks : Hooks := { (if committed then Committed.hooks else {}) with
    trials := fun _ => #[(1, 1)]
    cost := fun _ _ c => pure (if c.move.role == `fixture then c.move.cost else 1000)
    extraMoves := fun g _ _ _ group => do
      if group == .basic && g == left then
        return #[{
          label := "choose shared witness", role := `fixture
          run := witness.assign (mkNatLit 1)}]
      if group == .close && (← witness.isAssigned) then
        return #[{cost := 0, label := "close after witness", role := `fixture, run := do
          if g == left then g.assign (mkConst ``True.intro) else g.withContext g.refl
          setGoals []}]
      return #[] }
  let report ← capture {effort := 3, lazy} #[] "shared-progress" true true {} hooks
  let some plan := report.plan | throwError "global progress rejected: {report.error}"
  unless plan.steps.size == 3 && plan.steps[0]!.label == "choose shared witness" &&
      plan.steps[0]!.children == 1 && plan.steps[0]!.cost == 1 do
    throwError "shared witness step or its positive cost was lost"
  saved.restore true
  replay plan #[] "shared-progress" hooks

example : ∃ n : Nat, True ∧ n = 1 := by run_tac sharedProgress false true
example : ∃ n : Nat, True ∧ n = 1 := by run_tac sharedProgress false false
example : ∃ n : Nat, True ∧ n = 1 := by run_tac sharedProgress true true
example : ∃ n : Nat, True ∧ n = 1 := by run_tac sharedProgress true false

-- Unchanged extension steps remain bounded by positive depth. Providers may
-- explicitly opt into the same local stutter pruning as built-in operations.
example : True := by
  run_tac
    let saved ← Tactic.saveState
    for checkLocalChange in [false, true] do
      let actions ← IO.mkRef 0
      let hooks : Hooks := {
        trials := fun round => if round == 0 then #[(2, 1)] else #[]
        policy := ⟨Unit, (), fun space => space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)⟩
        around := fun span _ body => do
          if span.phase == .action then actions.modify (· + 1)
          body
        extraMoves := fun _ _ _ _ _ => pure #[{
          label := "stutter", role := `fixture, checkLocalChange, run := pure ()}] }
      let report ← capture {effort := 5} #[] "bounded-stutter" false false {} hooks
      unless !report.success && (← actions.get) == (if checkLocalChange then 1 else 2) do
        throwError "stutter pruning or positive-depth bound broke"
      saved.restore true
  trivial

-- Keep built-in normalization's old pruning: otherwise a no-op simp can spend
-- the entire depth allowance before another operation is considered.
example : True := by
  run_tac
    let saved ← Tactic.saveState
    let actions ← IO.mkRef 0
    let hooks : Hooks := {
      trials := fun round => if round == 0 then #[(5, 1)] else #[]
      policy := ⟨Unit, (), fun space => space.expand 0 #[#[.basic]] (fun c => c.move.label == "normalize")⟩
      around := fun span _ body => do
        if span.phase == .action then actions.modify (· + 1)
        body }
    let root ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False)
    setGoals [root.mvarId!]
    let report ← capture {effort := 5} #[] "builtin-stutter" false false {} hooks
    unless !report.success && (← actions.get) == 1 do
      throwError "built-in no-op normalization was no longer pruned"
    saved.restore true
  trivial

-- Charge a known sentinel, then cancel that worker. Injecting the count avoids
-- expensive allocation work. The parent must include the debt even though the
-- cancelled worker cannot return a Result; a smaller ambient cap must reject
-- the competitor's otherwise valid proof and restore the original root.
private def cancelledWork (bounded : Bool) : TacticM Bool := do
  let started ← Std.Mutex.new false
  let cancelled ← Std.Mutex.new false
  let sentinel := 100000000
  let root ← getMainGoal
  let before ← IO.getNumHeartbeats
  let succeeded ← tryCatchRuntimeEx (do
    withTheReader Core.Context (fun c => {c with
        initHeartbeats := before
        maxHeartbeats := if bounded then sentinel / 2 else 0}) do
      discard <| Parallel.run 2 {effort := 20, attemptHeartbeats := 2 * sentinel} #[] (fun use => use {
        trials := fun round => if round < 2 then #[(1, round + 1)] else #[]
        policy := ⟨Unit, (), fun space => space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)⟩
        extraMoves := fun _ _ strength _ group => do
          if group != .basic then return #[]
          return #[{label := "cancelled cost", role := `fixture, run := do
            if strength == 1 then
              IO.addHeartbeats sentinel
              started.atomically <| set true
              try
                repeat
                  Core.checkInterrupted
                  IO.sleep 1
              finally
                cancelled.atomically <| set true
            else
              repeat
                if ← started.atomically get then break
                IO.sleep 1
              evalTactic (← `(tactic| exact True.intro))}] })
    pure true) fun _ => pure false
  let spent := (← IO.getNumHeartbeats) - before
  unless (← cancelled.atomically get) && spent >= sentinel do
    throwError "cancelled-worker cleanup or accounting lost: {spent} < {sentinel}"
  if bounded then
    if succeeded || (← root.isAssigned) then throwError "aggregate heartbeat cap bypassed"
  else
    unless succeeded do throwError "unlimited cancellation fixture failed"
    checkComplete [root]
  return succeeded

example : True := by run_tac discard <| cancelledWork false
example : True := by
  run_tac discard <| cancelledWork true
  trivial

end ReviewFixes
