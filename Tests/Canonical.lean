import Waterfall
import Waterfall.Canonical

open Lean Meta Elab Tactic Waterfall

namespace WaterfallCanonicalTest

private def equal (label left right : String) : TacticM Unit :=
  unless left == right do throwError "canonical guard changed under {label}"

private def different (label left right : String) : TacticM Unit :=
  if left == right then throwError "canonical guard erased {label}" else pure ()

-- Construct the same dependent context and quantified proposition with entirely
-- fresh IDs and different display names. No proof is admitted: scratch holes
-- are removed by the caller's snapshot bracket before closing its True goal.
private def alpha (aName xName binder : Name) : TacticM (String × Array Name) := do
  let u ← mkFreshLevelMVar
  withLocalDeclD aName (mkSort u) fun a =>
    withLocalDeclD xName a fun x => do
      let eq := mkApp3 (mkConst ``Eq [u]) a (.bvar 0) x
      let target := Expr.forallE binder a eq .default
      let g ← mkFreshExprMVar target .syntheticOpaque binder
      let .mvar uid := u | throwError "fixture did not allocate universe hole"
      return (← Canonical.snapshot [g.mvarId!],
        #[a.fvarId!.name, x.fvarId!.name, g.mvarId!.name, uid.name])

elab "check_canonical_alpha" : tactic => withMainContext do
  let (first, ids) ← withoutModifyingState <| alpha `A `x `argument
  -- Model discarded search work: both fresh names and absolute mvar allocation
  -- counters may advance before the retained continuation is replayed.
  let (second, otherIds) ← withoutModifyingState do
    for _ in [:17] do
      discard <| mkFreshUserName `discarded
      discard <| mkFreshExprMVar (mkConst ``Nat)
      discard <| mkFreshLevelMVar
    alpha `RenamedType `renamedLocal `renamedBinder
  if ids == otherIds then throwError "alpha fixture reused allocation IDs"
  equal "fresh IDs, allocation counters and display names" first second
  evalTactic (← `(tactic| trivial))

example : True := by check_canonical_alpha

private def withValue (value : Nat) : TacticM String :=
  withLetDecl `sameName (mkConst ``Nat) (mkNatLit value) fun entry => do
    let target ← mkEq entry entry
    let g ← mkFreshExprMVar target
    Canonical.snapshot [g.mvarId!]

elab "check_canonical_lets" : tactic => withMainContext do
  let first ← withoutModifyingState <| withValue 0
  let second ← withoutModifyingState <| withValue 1
  different "different local let values behind the same printed target" first second
  evalTactic (← `(tactic| trivial))

example : True := by check_canonical_lets

private def siblingHoles (shared : Bool) : TacticM String := do
  let witness ← mkFreshExprMVar (mkConst ``Nat)
  let other ← if shared then pure witness else mkFreshExprMVar (mkConst ``Nat)
  let left ← mkFreshExprMVar (← mkEq witness (mkNatLit 0))
  let right ← mkFreshExprMVar (← mkEq other (mkNatLit 1))
  Canonical.snapshot [left.mvarId!, right.mvarId!]

elab "check_canonical_sharing" : tactic => withMainContext do
  let shared ← withoutModifyingState <| siblingHoles true
  let separate ← withoutModifyingState <| siblingHoles false
  different "shared versus independent sibling witnesses" shared separate
  evalTactic (← `(tactic| trivial))

example : True := by check_canonical_sharing

private def atUniverse (sortLevel : Level) : TacticM String := do
  let g ← mkFreshExprMVar (mkSort sortLevel)
  Canonical.snapshot [g.mvarId!]

elab "check_canonical_universes" : tactic => withMainContext do
  withoutModifyingState do
    different "Prop versus Type" (← atUniverse .zero) (← atUniverse (.succ .zero))
    let .mvar u ← mkFreshLevelMVar | throwError "fixture expected a universe hole"
    let g ← mkFreshExprMVar (mkSort (.mvar u))
    let openGuard ← Canonical.snapshot [g.mvarId!]
    assignLevelMVar u .zero
    let zeroGuard ← Canonical.snapshot [g.mvarId!]
    different "unassigned versus assigned universe" openGuard zeroGuard
    assignLevelMVar u (.succ .zero)
    different "different universe assignments" zeroGuard (← Canonical.snapshot [g.mvarId!])
    -- A postponed equation can constrain a goal without changing its target.
    let before ← Canonical.snapshot [g.mvarId!]
    modifyThe Meta.State fun s => { s with postponed := s.postponed.push {
      ref := Syntax.missing, lhs := .mvar u, rhs := .zero, ctx? := none } }
    different "postponed universe equation" before (← Canonical.snapshot [g.mvarId!])
  evalTactic (← `(tactic| trivial))

example : True := by check_canonical_universes

-- Snapshot must not normalize away assignments, solve holes, allocate fresh
-- names, or change the caller's agenda. Check those observable effects directly,
-- independently of comparing the snapshot with a second snapshot of itself.
elab "check_canonical_read_only" : tactic => withMainContext do
  withoutModifyingState do
    let .mvar u ← mkFreshLevelMVar | throwError "fixture expected a universe hole"
    let value ← mkFreshExprMVar (mkConst ``Nat)
    let g ← mkFreshExprMVar (← mkEq value (mkNatLit 3))
    let universeGoal ← mkFreshExprMVar (mkSort (.mvar u))
    value.mvarId!.assign (mkNatLit 3)
    assignLevelMVar u (.succ .zero)
    let goals ← getGoals
    let ctx ← getMCtx
    let core ← getThe Core.State
    let first ← Canonical.snapshot [g.mvarId!, universeGoal.mvarId!]
    let after ← getMCtx
    let coreAfter ← getThe Core.State
    unless (← getGoals) == goals && !(← g.mvarId!.isAssigned) &&
        !(← universeGoal.mvarId!.isAssigned) do throwError "snapshot changed goals"
    unless (← getExprMVarAssignment? value.mvarId!) == some (mkNatLit 3) &&
        (← getLevelMVarAssignment? u) == some (.succ .zero) do
      throwError "snapshot changed existing assignments"
    unless after.mvarCounter == ctx.mvarCounter && after.depth == ctx.depth &&
        after.levelAssignDepth == ctx.levelAssignDepth do
      throwError "snapshot changed allocation or assignment restrictions"
    unless core.ngen.idx == coreAfter.ngen.idx &&
        core.ngen.namePrefix == coreAfter.ngen.namePrefix &&
        core.auxDeclNGen.idx == coreAfter.auxDeclNGen.idx &&
        core.nextMacroScope == coreAfter.nextMacroScope do
      throwError "snapshot consumed fresh names or macro scopes"
    equal "repeated read-only snapshot" first
      (← Canonical.snapshot [g.mvarId!, universeGoal.mvarId!])
  evalTactic (← `(tactic| trivial))

example : True := by check_canonical_read_only

end WaterfallCanonicalTest
