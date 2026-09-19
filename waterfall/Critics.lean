module
public import waterfall.Core

meta section

/-!
Small ACL2-style proof critics implemented through the public engine hooks.
They add proposals and ordering information, but own no traversal, rollback,
resource accounting or proof validation.
-/

open Lean Meta Elab Tactic
namespace waterfall.Critics

/-- Split a proposition that is the sole missing premise of an otherwise
applicable local rule. Inference retains no temporary elaboration metavariables;
the actual split is reconstructed inside the rollback-protected action. -/
public def blockedPremises (g : MVarId) : TacticM (Array Move) := g.withContext do
  let mut out : Array Move := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || !(← isProp d.type) then continue
    let blocker? ← withoutModifyingState do
      try
        let premises ← g.apply (mkFVar d.fvarId)
        let mut known := 0
        let mut unknown : Array Expr := #[]
        for premise in premises do
          let type ← instantiateMVars (← premise.getType)
          if type.hasMVar then return none
          if (← findLocalDeclWithType? type).isSome then known := known + 1
          else unknown := unknown.push type
        if known == 0 || unknown.size != 1 then return none
        let type := unknown[0]!
        let blocker := if type.isAppOfArity ``Not 1 then type.getAppArgs[0]! else type
        if blocker.hasMVar || !(← isProp blocker) then return none
        if (← findLocalDeclWithType? blocker).isSome ||
            (← findLocalDeclWithType? (mkNot blocker)).isSome then return none
        return some blocker
      catch _ => return none
    let some blocker := blocker? | continue
    unless out.any (fun move => move.subject == some blocker) do
      out := out.push {
        cost := 1, label := "split blocked rule premise", role := `critic,
        major := some d.fvarId, subject := some blocker,
        run := g.withContext do
          let (positive, negative) ← g.byCases blocker `wf_blocker
          setGoals [positive.mvarId, negative.mvarId] }
  return out

/-- Exposing root binders can reveal a critic hidden by a quantified target.
The temporary locals and candidate proposals are discarded after this probe. -/
public def prelude (goals : List MVarId) : TacticM (Array PreludeTrial) := do
  for g in goals do
    let found ← withoutModifyingState do
      try
        g.withContext do
          let (introduced, child) ← g.intros
          if introduced.isEmpty then return false
          return !(← blockedPremises child).isEmpty
      catch _ => return false
    if found then return #[{ depth := 5 }]
  return #[]

/-- Add critic proposals to an arbitrary policy. `early` enables the bounded
goal-directed prelude used by ordinary backtracking search. -/
public def hooks (inner : Hooks := {}) (early := false) : Hooks := { inner with
  extraMoves := fun g rules strength remaining group => do
    let original ← inner.extraMoves g rules strength remaining group
    if group == .hypotheses then return original ++ (← blockedPremises g)
    return original
  prelude := fun goals => do
    let original ← inner.prelude goals
    if early then return (← prelude goals) ++ original
    return original
  order := fun g span candidates => do
    let requested ← inner.order g span candidates
    let ordered ← match requested with
      | none => pure candidates
      | some actions => actions.mapM fun action => do
          let some candidate := candidates.find? (·.action == action)
            | throwError "critic received an unknown ordered action"
          return candidate
    return some ((ordered.filter (·.move.role == `critic) ++
      ordered.filter (·.move.role != `critic)).map (·.action)) }

end waterfall.Critics
