import Waterfall.Protocol

/-!
Optional combinators for the same lazy choice interface used by the engine.
A producer calls its visitor in order and stops when the visitor returns true.
The visitor may perform a recursive search, collect frontier entries, or simply
inspect transitions. These combinators introduce no proof or scheduling rules.
-/

namespace Waterfall.Choices

/-- Commit to the first locally successful transition, even when its entire
continuation fails. An inapplicable proposal is never yielded by the engine.
The private result distinguishes stopping enumeration from finding a proof. -/
def first (choices : Choices α) : Choices α := fun visit => do
  let result ← IO.mkRef false
  discard <| choices fun value => do
    result.set (← visit value)
    return true
  result.get

def filter (predicate : α → Bool) (choices : Choices α) : Choices α :=
  fun visit => choices fun value => if predicate value then visit value else pure false

def map (f : α → β) (choices : Choices α) : Choices β :=
  fun visit => choices (visit ∘ f)

/-- The right producer is called only after every left continuation fails. -/
def append (left right : Choices α) : Choices α := fun visit => do
  if ← left visit then return true
  right visit

/-- Materialization is explicit. Useful for beam or state-based scoring
experiments; unlike `first`, it intentionally pays for every offered transition. -/
def collect (choices : Choices α) : Lean.Elab.Tactic.TacticM (Array α) := do
  let values ← IO.mkRef #[]
  discard <| choices fun value => do values.modify (·.push value); return false
  values.get

end Waterfall.Choices

namespace Waterfall.Node

/-- Replace traversal bookkeeping while retaining the complete proof checkpoint.
For example, a FIFO frontier can store `Node Unit` and attach its updated queue
only when the traversal selects that entry. -/
def mapState (f : α → β) (node : Node α) : Node β :=
  { saved := node.saved, jobs := node.jobs, state := f node.state, plan := node.plan }

end Waterfall.Node
