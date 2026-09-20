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

public def exposesBlockedPremise (g : MVarId) : TacticM Bool := withoutModifyingState do
  try
    g.withContext do
      let (introduced, child) ← g.intros
      if introduced.isEmpty then return false
      return !(← blockedPremises child).isEmpty
  catch _ => return false

/-- Exposing root binders can reveal a critic hidden by a quantified target. -/
public def prelude (goals : List MVarId) : TacticM (Array PreludeTrial) := do
  for g in goals do
    if ← exposesBlockedPremise g then return #[{ depth := 5 }]
  return #[]

public def needsPrelude (goals : List MVarId) : TacticM Bool := do
  for g in goals do
    if ← exposesBlockedPremise g then return true
  return false

/-- Add critic proposals to an arbitrary policy. `early` prioritizes goal
shaping that exposes a critic; `speculate` also requests the legacy bounded
depth trial. They are separate so a general scheduler need not use a magic
depth. -/
public def hooks (inner : Hooks := {}) (early := false) (speculate := early) : Hooks := { inner with
  extraMoves := fun g rules strength remaining group => do
    let original ← inner.extraMoves g rules strength remaining group
    if group == .hypotheses then return original ++ (← blockedPremises g)
    return original
  prelude := fun cfg goals => do
    let original ← inner.prelude cfg goals
    if speculate then return (← prelude goals) ++ original
    return original
  order := fun g span candidates => do
    let requested ← inner.order g span candidates
    let ordered ← match requested with
      | none => pure candidates
      | some actions => actions.mapM fun action => do
          let some candidate := candidates.find? (·.action == action)
            | throwError "critic received an unknown ordered action"
          return candidate
    let critics := ordered.filter (·.move.role == `critic)
    let others := ordered.filter (·.move.role != `critic)
    let expose ← if early && others.any (·.move.preparation == .allBinders) then
      exposesBlockedPremise g else pure false
    let others := if expose then
      others.filter (·.move.preparation == .allBinders) ++
        others.filter (·.move.preparation != .allBinders)
      else others
    return some ((critics ++ others).map (·.action)) }

end waterfall.Critics
