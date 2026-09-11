import Lean

/-!
Read-only, structural guards for the optional search/replay laboratory. This is
not definitional equality or a complete equivalence test for Lean states. The
caller separately pins the theory, rules, options and operation vocabulary.

One numbering covers the entire ordered agenda and its reachable metavariable
graph, so shared holes stay shared. Binder/display names and fresh variable IDs
are omitted; types, values, universe structure and assignment restrictions are
retained. Global names and opaque expression metadata remain exact: a benign
change there can conservatively make replay unsupported rather than authorize a
different action. No normalization, elaboration, assignment or fresh name is
performed while taking a snapshot.
-/

open Lean Meta Elab Tactic

namespace Waterfall.Canonical

private def node (tag : String) (fields : Array Json := #[]) : Json :=
  .arr (#[.str tag] ++ fields)

-- Preserve Name structure; concatenated display strings need not be injective.
private def nameJson : Name → Json
  | .anonymous => node "anonymous"
  | .str parent value => node "str" #[nameJson parent, .str value]
  | .num parent value => node "num" #[nameJson parent, toJson value]

private structure State where
  context : MetavarContext
  fvars : Array FVarId := #[]
  declared : Array FVarId := #[]
  mvars : Array MVarId := #[]
  levels : Array LMVarId := #[]

private abbrev Encode := StateT State CoreM

-- StateT does not lift MonadRecDepth; bracket the underlying CoreM call so
-- recursive traversal obeys Lean's enclosing recursion limit as well as ticks.
private def withDepth (body : Encode α) : Encode α :=
  fun state => withIncRecDepth (body.run state)

private def fvar (id : FVarId) : Encode Json := do
  if let some index := (← get).fvars.findIdx? (· == id) then
    return node "fvar" #[toJson index]
  let index := (← get).fvars.size
  modify fun s => { s with fvars := s.fvars.push id }
  return node "fvar" #[toJson index]

private def mvar (id : MVarId) : Encode Json := do
  if let some index := (← get).mvars.findIdx? (· == id) then
    return node "mvar" #[toJson index]
  let index := (← get).mvars.size
  modify fun s => { s with mvars := s.mvars.push id }
  return node "mvar" #[toJson index]

private partial def level (value : Level) : Encode Json := withDepth do
  Core.checkSystem "waterfall canonical level"
  match value with
  | .zero => return node "zero"
  | .succ value => return node "succ" #[← level value]
  | .max left right => return node "max" #[← level left, ← level right]
  | .imax left right => return node "imax" #[← level left, ← level right]
  | .param name => return node "param" #[nameJson name]
  | .mvar id => do
    if let some index := (← get).levels.findIdx? (· == id) then
      return node "level-mvar" #[toJson index]
    let index := (← get).levels.size
    modify fun s => { s with levels := s.levels.push id }
    return node "level-mvar" #[toJson index]

private partial def expr (value : Expr) : Encode Json := withDepth do
  Core.checkSystem "waterfall canonical expression"
  match value with
  | .bvar index => return node "bvar" #[toJson index]
  | .fvar id => fvar id
  | .mvar id => mvar id
  | .sort value => return node "sort" #[← level value]
  | .const name levels => return node "const" #[nameJson name, .arr (← levels.toArray.mapM level)]
  | .app fn arg => return node "app" #[← expr fn, ← expr arg]
  | .lam _ type body info => return node "lambda" #[.str (reprStr info), ← expr type, ← expr body]
  | .forallE _ type body info => return node "forall" #[.str (reprStr info), ← expr type, ← expr body]
  | .letE _ type value body nondep =>
    return node "let" #[toJson nondep, ← expr type, ← expr value, ← expr body]
  | .lit value => return node "literal" #[.str (reprStr value)]
  -- Metadata can affect tactic enumeration. Do not erase unknown annotations
  -- merely because the kernel ignores them; exact metadata is conservative.
  | .mdata data body => return node "metadata" #[.str (reprStr data.entries), ← expr body]
  | .proj name index body => return node "projection" #[nameJson name, toJson index, ← expr body]

private def localContext (context : LocalContext) : Encode Json := do
  let mut declarations := #[]
  for declaration in context do
    discard <| fvar declaration.fvarId
    modify fun s => { s with declared := s.declared.push declaration.fvarId }
  for declaration in context do
    let id ← fvar declaration.fvarId
    declarations := declarations.push (← match declaration with
      | .cdecl _ _ _ type info kind => do
        return node "local" #[id, .str (reprStr info), .str (reprStr kind), ← expr type]
      | .ldecl _ _ _ type value nondep kind => do
        return node "local-value" #[id, toJson nondep, .str (reprStr kind), ← expr type, ← expr value])
  return .arr declarations

private def instances (values : LocalInstances) : Encode Json := do
  return .arr (← values.mapM fun value => do
    return node "instance" #[nameJson value.className, ← expr value.fvar])

private def declaration (id : MVarId) : Encode Json := do
  Core.checkSystem "waterfall canonical declaration"
  let context := (← get).context
  let some decl := context.decls.find? id | throwError "waterfall replay guard unsupported: unknown expression metavariable"
  let locals ← localContext decl.lctx
  let type ← expr decl.type
  let localInstances ← instances decl.localInstances
  let assignment ← match context.eAssignment.find? id with
    | none => pure Json.null
    | some value => expr value
  let delayed ← match context.dAssignment.find? id with
    | none => pure Json.null
    | some value => do
      return node "delayed" #[.arr (← value.fvars.mapM expr), ← mvar value.mvarIdPending]
  return node "declaration" #[locals, type, localInstances, .str (reprStr decl.kind),
    toJson decl.depth, toJson decl.numScopeArgs, assignment, delayed]

private def encode (goals : List MVarId) (postponed : Array PostponedEntry) : Encode Json := do
  let roots ← goals.toArray.mapM mvar
  -- Postponed universe equations constrain the current elaboration. Keep their
  -- order and level sharing; source locations and diagnostic contexts are not
  -- part of the equations. Other unreachable metavariables/caches are omitted.
  let constraints ← postponed.mapM fun constraint => do
    return node "universe-equation" #[← level constraint.lhs, ← level constraint.rhs]
  let mut declarations := #[]
  while declarations.size < (← get).mvars.size do
    let id := (← get).mvars[declarations.size]!
    declarations := declarations.push (← declaration id)
  let mut universes := #[]
  while universes.size < (← get).levels.size do
    let id := (← get).levels[universes.size]!
    let context := (← get).context
    let some depth := context.lDepth.find? id | throwError "waterfall replay guard unsupported: unknown universe metavariable"
    let assignment ← match context.lAssignment.find? id with
      | none => pure Json.null
      | some value => level value
    universes := universes.push <| node "universe-declaration" #[toJson depth, assignment]
  let s ← get
  unless s.fvars.all s.declared.contains do throwError "waterfall replay guard unsupported: free variable outside the recorded contexts"
  -- Unification can depend on which hole is older. Preserve relative age among
  -- reachable holes, not the absolute allocation counter of discarded work.
  let ages ← s.mvars.mapM fun id => do
    let some decl := s.context.decls.find? id | throwError "waterfall replay guard unsupported: unknown expression metavariable"
    return decl.index
  let ranks := ages.map fun age => toJson ((ages.filter (· < age)).size)
  return node "wf-core-canonical-v1" #[.arr roots, .arr declarations, .arr ranks,
    .arr universes, .arr constraints, toJson s.context.depth, toJson s.context.levelAssignDepth]

/-- A structural guard over the entire ordered pending agenda. Alpha-renaming
fresh expression/universe metavariable IDs, local IDs, and binder/display names
does not change it. Sharing, types, local values, universe equations and the
restrictions on metavariable assignment do. Unsupported/stale references fail
closed; environment/rules/options must be checked by the plan interpreter too.
-/
def snapshot (goals : List MVarId) : TacticM String := do
  let context ← getMCtx
  let postponed := (← getThe Meta.State).postponed.toArray
  let (value, _) ← (encode goals postponed).run { context }
  let text := value.compress
  Core.checkSystem "waterfall canonical snapshot"
  return text

end Waterfall.Canonical
