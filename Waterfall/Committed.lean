import Waterfall.Core
import Waterfall.Choices

/-!
An ACL2-like policy over the shared search interface. This module contains no
proof operations, resource accounting, proof-state rollback or recursive search.
Its policy state travels with each search node; siblings share pending work but
inherit only their own proof ancestry. Restrictions are deliberately opt-in.
-/

open Lean Meta Elab Tactic
namespace Waterfall.Committed

structure State where
  shaped : Bool := false
  induced : Bool := false
  reverted : Bool := false
  direct : Bool := false

-- All rankings inspect typed generator metadata and the selected goal. None
-- depends on diagnostic labels, theorem names or benchmark namespaces.
private def rank (g : MVarId) (candidate : Candidate) : MetaM Nat := do
  let move := candidate.move
  if move.role == `inversion then return 4
  if move.induction == .evidence then
    if let some id := move.major then
      let type ← whnf (← inferType (mkFVar id))
      if let .const n _ := type.getAppFn then
        if (← g.getType).getUsedConstants.contains n then return 0
    return 1
  return if move.induction == .data then 2 else 3

/-- Try ordinary work across the current agenda before selecting an induction.
A miss belongs only to this scan: any accepted sibling step can assign shared
metavariables and make an earlier goal solvable. The next scan starts fresh.
`first` wraps this entire sequence, not each generator batch separately. -/
def choose (space : Space State) : Choices (Node State) := Choices.first fun visit => do
  let node := space.current
  let state := node.state
  for focus in [:node.jobs.length] do
    let job := node.jobs[focus]!
    if ← job.goal.isAssigned then continue
    let admit := fun (candidate : Candidate) =>
      candidate.move.induction == .none && candidate.move.role != `inversion &&
      (!state.direct || candidate.action.group == .close || candidate.move.role == `prepare)
    let ordinary := space.expand focus
      #[#[.close], #[.basic], #[.hypotheses], #[.functions], #[.induction],
        #[.rules], #[.forward], #[.library]] admit
    let ordinary := Choices.filter (fun (next : Node State) =>
      match next.plan with
      | (step, _) :: _ => step.action.group != .library || step.children == 0
      | [] => false) ordinary
    if ← ordinary (fun next => do
      let shaped := !state.induced && next.plan.head?.any (fun (step, _) =>
        step.action.group != .close && step.role != `prepare)
      visit { next with state := { state with shaped := state.shaped || shaped } }) then return true
  -- A checkpoint is a whole compatible proof state. Changing the immutable
  -- policy state makes this restart enter a different phase rather than loop.
  if state.shaped && !state.induced && !state.reverted then
    return ← space.restart space.root { reverted := true, direct := true } visit
  -- All ordinary proposals missed in this scan. Consider induction in reverse
  -- agenda order, without retaining misses across subsequent proof steps.
  -- An empty expansion has made no commitment: keep scanning earlier siblings.
  -- Choices.first stops this whole producer only after a transition is yielded,
  -- even when that transition's continuation fails.
  for focus in (List.range node.jobs.length).reverse do
    let job := node.jobs[focus]!
    if ← job.goal.isAssigned then continue
    let candidates := space.expand focus #[#[.hypotheses, .functions, .induction]] fun c =>
      c.move.induction != .none || c.move.role == `inversion
    if ← candidates (fun next => do
      let induced := next.plan.head?.any (fun (step, _) => step.induction != .none)
      visit { next with state := { state with
        induced := state.induced || induced, direct := false } }) then return true
  return false

/-- The same inference adapters and attempt slices as the default. The linear
trial schedule is a committed heuristic, not a fair enumeration of proof paths.
Weighted costs retain the current engine's library floor; this is not a byte-for-
byte reproduction of the earlier standalone experiment's transformation count. -/
def hooks : Hooks := {
  policy := ⟨State, {}, choose⟩
  trials := fun round => #[(4 * (round + 1) + 4, round + 1)]
  cost := fun _ _ candidate => pure candidate.move.cost
  order := fun g _ candidates => do
    let ranked ← candidates.mapIdxM fun i c => return ((← rank g c, i), c.action)
    return some ((ranked.qsort (fun a b => a.1.1 < b.1.1 ||
      (a.1.1 == b.1.1 && a.1.2 < b.1.2))).map (·.2)) }

end Waterfall.Committed
