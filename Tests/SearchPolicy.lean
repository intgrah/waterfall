import waterfall
import waterfall.Committed
import waterfall.Observe

open Lean Meta Elab Tactic waterfall waterfall.Observe

namespace waterfallSearchPolicyTest

-- The selection combinator must stop after the first yielded transition even
-- when the downstream visitor fails. Producing the tail would defeat commitment.
elab "check_choice_laziness" : tactic => do
  let seen ← IO.mkRef ([] : List Nat)
  let choices : Choices Nat := fun visit => do
    for n in [1:4] do
      seen.modify (n :: ·)
      if ← visit n then return true
    return false
  if ← Choices.first choices (fun _ => pure false) then throwError "false visitor became success"
  unless (← seen.get) == [1] do throwError "committed producer evaluated its tail"
  seen.set []
  unless ← choices (fun n => pure (n == 3)) do throwError "ordinary selection lost its tail"
  unless (← seen.get) == [3, 2, 1] do throwError "ordinary order changed"
  evalTactic (← `(tactic| trivial))

example : True := by check_choice_laziness

private def fixture (label : String) (body : TacticM Unit) : Move :=
  { label, role := `fixture, run := body }

-- A failing proposed operation precedes the first locally successful one. The
-- final proposed operation must not run, even though its generator is present.
elab "check_first_applicable" : tactic => do
  let tail ← IO.mkRef false
  let hooks : Hooks := {
    trials := fun _ => #[(1, 1)]
    extraMoves := fun _ _ _ _ group => do
      if group != .basic then return #[]
      return #[fixture "miss" (throwError "local miss"),
      fixture "hit" (evalTactic (← `(tactic| exact True.intro))),
      fixture "unused" (tail.set true)]
    policy := ⟨Unit, (), fun space => Choices.first <|
      space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)⟩ }
  let stats ← waterfall.run { effort := 2 } #[] hooks
  unless stats.attempts == 2 && !(← tail.get) do throwError "first applicable was not lazy"

example : True := by check_first_applicable

private def witnessHooks (commit : Bool) : Hooks := {
  trials := fun _ => #[(2, 1)]
  extraMoves := fun _ _ _ _ group => do
    if group != .basic then return #[]
    return #[fixture "wrong witness" (evalTactic (← `(tactic| refine ⟨0, ?_⟩))),
      fixture "right witness" (evalTactic (← `(tactic| exact ⟨1, rfl⟩)))]
  policy := ⟨Unit, (), fun space =>
    let choices := space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)
    if commit then Choices.first choices else choices⟩ }

-- Failure downstream must revisit the witness only in the noncommitted policy.
example : ∃ n : Nat, n = 1 := by
  fail_if_success run_tac discard <| waterfall.run { effort := 8 } #[] (witnessHooks true)
  run_tac discard <| waterfall.run { effort := 8 } #[] (witnessHooks false)

-- A different policy explicitly collects alternatives, scores successor states,
-- and retains one. This tests the abstraction beyond the two production policies:
-- the saved winning state must survive evaluation of other alternatives.
example : ∃ n : Nat, n = 1 := by
  run_tac
    let hooks := witnessHooks false
    let policy : SearchPolicy := ⟨Unit, (), fun space visit => do
      let choices ← Choices.collect (space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture))
      let ranked := choices.qsort (fun a b => a.jobs.length < b.jobs.length)
      match ranked[0]? with
      | some node => visit node
      | none => pure false⟩
    discard <| waterfall.run { effort := 8 } #[] { hooks with policy }

-- A FIFO frontier spans multiple expansion calls, not just siblings of one
-- node. Its entries carry their own proof states. This uses exactly the same
-- engine interface as the recursive policy and the committed policy.
private def fifoPolicy : SearchPolicy := ⟨List (Node Unit), [], fun space visit => do
  let children ← Choices.collect (space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture))
  let queue := space.current.state ++ children.toList.map (Node.mapState (fun _ => ()))
  match queue with
  | next :: rest => visit (next.mapState (fun _ => rest))
  | [] => pure false⟩

example : ∃ n : Nat, n = 1 := by
  run_tac
    discard <| waterfall.run { effort := 8 } #[] { (witnessHooks false) with policy := fifoPolicy }

-- Both root alternatives are already funded when the frontier selects the dead
-- branch. Draining its queue must still find the completed proof at the exact
-- attempt limit, without generating or executing another operation. Only the
-- successful branch belongs to the replayable plan, in either enumeration mode.
example : ∃ n : Nat, n = 1 := by
  run_tac
    let saved ← Tactic.saveState
    for lazy in [true, false] do
      saved.restore true
      let actions ← IO.mkRef 0
      let lateEnumeration ← IO.mkRef 0
      let base := { (witnessHooks false) with policy := fifoPolicy }
      let hooks := { base with around := fun span _ body => do
        if span.phase == .action then actions.modify (· + 1)
        if span.phase == .enumerate && (← actions.get) >= 2 then
          lateEnumeration.modify (· + 1)
        body }
      let report ← capture { effort := 2, lazy } #[] "frontier-boundary" true true {} hooks
      unless report.success do throwError "funded frontier proof lost: {report.error}"
      unless (← actions.get) == 2 && (← lateEnumeration.get) == 0 do
        throwError "frontier draining dispatched or generated new work"
      let some plan := report.plan | throwError "frontier plan missing"
      unless plan.steps.size == 1 && plan.steps[0]!.label == "right witness" do
        throwError "frontier plan retained an abandoned branch"
      saved.restore true
      replay plan #[] "frontier-boundary" base

-- A sibling can supply a shared witness through ordinary work or an induction
-- transition. In both cases the earlier ordinary miss must be reconsidered.
-- The small provider isolates scheduling from the built-in solvers.
private def checkDeferredSibling (rightInduction : Bool) : TacticM Unit := do
  evalTactic (← `(tactic| refine ⟨?_, ?_, ?_⟩))
  let [witness, left, right] ← getGoals | throwError "unexpected sibling agenda"
  setGoals [left, right]
  let saved ← Tactic.saveState
  let hooks : Hooks := { Committed.hooks with
    trials := fun _ => #[(1, 1)]
    cost := fun _ _ c => pure (if c.move.label == "dependent closer" then c.move.cost else 1000)
    extraMoves := fun g _ _ _ group => do
      let isInduction := rightInduction && g == right
      if group != (if isInduction then .induction else .basic) then return #[]
      if g == left && !(← witness.isAssigned) then return #[]
      if g != left && g != right then return #[]
      return #[{
        label := "dependent closer"
        role := `prepare
        induction := if isInduction then .data else .none
        run := do
          if g == right then witness.assign (mkNatLit 1)
          g.withContext g.refl
          setGoals [] }] }
  let report ← capture { effort := 2 } #[] "sibling-progress" true true {} hooks
  unless report.success do throwError "ordinary miss survived sibling progress: {report.error}"
  let some plan := report.plan | throwError "sibling plan missing"
  unless plan.steps.size == 2 && plan.steps[0]!.focus == 1 && plan.steps[1]!.focus == 0 &&
      (report.rows.filter (·.span.phase == .action)).size == 2 do
    throwError "sibling scheduling lost its goal order or attempt bound"
  saved.restore true
  replay plan #[] "sibling-progress" hooks

example : ∃ n : Nat, n = 1 ∧ n = 1 := by run_tac checkDeferredSibling false
example : ∃ n : Nat, n = 1 ∧ n = 1 := by run_tac checkDeferredSibling true

-- Agenda selection must be recorded and replayed. Both goals remain obligations
-- throughout, including when the selected goal is not the displayed head.
elab "check_nonhead_replay" : tactic => do
  let saved ← Tactic.saveState
  let hooks : Hooks := { policy := ⟨Unit, (), fun space =>
    space.expand (space.current.jobs.length - 1) #[] (fun _ => true)⟩ }
  let report ← capture { effort := 20 } #[] "nonhead" true true {} hooks
  unless report.success do throwError "non-head search failed: {report.error}"
  let some plan := report.plan | throwError "no recorded plan"
  unless plan.steps.any (·.focus == 1) do throwError "non-head selection was not recorded"
  saved.restore true
  replay plan #[] "nonhead" hooks

example : True ∧ True := by
  constructor
  check_nonhead_replay

-- The abandoned branch proves True only under an impossible False premise.
-- Restart restores the original obligation. Neither that assignment nor its
-- recorded action may survive into the final plan; resource spend must survive.
elab "check_checkpoint_replay" : tactic => do
  let saved ← Tactic.saveState
  let hooks : Hooks := {
    trials := fun _ => #[(1, 1)]
    extraMoves := fun _ _ _ _ group => do
      if group != .basic then return #[]
      return #[fixture "abandoned" (evalTactic (← `(tactic| apply (fun (_ : False) => True.intro)))),
        fixture "retained" (evalTactic (← `(tactic| exact True.intro)))]
    policy := ⟨Nat, 0, fun space =>
      if space.current.state == 1 then space.restart space.root 2
      else Choices.map (fun next => { next with state := 1 }) <|
        space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture &&
          c.move.label == (if space.current.state == 0 then "abandoned" else "retained"))⟩ }
  let attempts ← IO.mkRef 0
  let observed := { hooks with around := fun span _ body => do
    if span.phase == .action then attempts.modify (· + 1)
    body }
  -- A restart is metered work, even though draining a saved frontier is not.
  for effort in [1, 2] do
    let blocked ← capture { effort } #[] "checkpoint-budget" false true {} hooks
    unless !blocked.success && blocked.plan.isNone do throwError "restart exceeded its allowance"
    saved.restore true
  let report ← capture { effort := 3 } #[] "checkpoint" true true {} observed
  unless report.success do throwError "checkpoint search failed: {report.error}"
  let some plan := report.plan | throwError "checkpoint has no plan"
  unless plan.steps.size == 1 && plan.steps[0]!.label == "retained" && (← attempts.get) == 2 do
    throwError "checkpoint retained abandoned work or refunded attempts"
  saved.restore true
  replay plan #[] "checkpoint" hooks

example : True := by check_checkpoint_replay

-- A step on the first sibling must not become ancestry of the second sibling.
-- Both children inherit the splitting step, and only their own descendants
-- inherit subsequent steps. This is what ancestry-based scheduling observes.
example : True ∧ True := by
  run_tac
    let hooks : Hooks := {
      trials := fun _ => #[(2, 1)]
      extraMoves := fun _ _ _ _ group => do
        if group != .basic then return #[]
        return #[fixture "branch" (evalTactic (← `(tactic| constructor))),
          fixture "leaf" (evalTactic (← `(tactic| exact True.intro)))]
      policy := ⟨Nat, 0, fun space visit => do
        let phase := space.current.state
        if phase == 1 then
          unless space.current.jobs.length == 2 &&
              space.current.jobs.all (fun j => j.ancestors.length == 1) do
            throwError "children did not inherit their parent's ancestry"
        if phase == 2 then
          unless space.current.jobs.length == 1 &&
              space.current.jobs.head!.ancestors.map (·.move.label) == ["branch"] do
            throwError "a sibling inherited another sibling's proof steps"
        space.expand 0 #[#[.basic]]
          (fun c => c.move.role == `fixture && c.move.label == (if phase == 0 then "branch" else "leaf"))
          (fun next => visit { next with state := phase + 1 })⟩ }
    discard <| waterfall.run { effort := 3 } #[] hooks

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

example (xs : List Nat) : append xs [] = xs := by waterfall (mode := .committed)
example (xs ys zs : List Nat) : append (append xs ys) zs = append xs (append ys zs) := by
  waterfall (mode := .committed) (effort := 4000)

inductive Twice : Nat → Nat → Prop where
  | zero : Twice 0 0
  | step : Twice n m → Twice (n + 1) (m + 2)

-- Recursive evidence needs an IH. Repeatedly committing to cases on the
-- evidence only exposes another recursive premise and exhausts the pass.
-- The ordinary cascade must leave that inversion for the induction boundary.
example (n m : Nat) (h : Twice n m) : m = 2 * n := by
  run_tac
    let induced ← IO.mkRef false
    let earlyInversion ← IO.mkRef false
    let hooks := { Committed.hooks with around := fun span _ body => do
      if span.phase == .action then
        if span.induction != .none then induced.set true
        if span.label == "cases hypothesis" && !(← induced.get) then earlyInversion.set true
      body }
    discard <| waterfall.run { effort := 1000 } #[] hooks
    unless (← induced.get) && !(← earlyInversion.get) do
      throwError "ordinary work consumed recursive evidence before induction"

-- An incomplete policy can fail but cannot create a proof of a false root.
example : True := by
  fail_if_success have : False := by waterfall (mode := .committed) (effort := 10)
  trivial

end waterfallSearchPolicyTest
