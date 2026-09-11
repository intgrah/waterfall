import Waterfall
import Waterfall.Observe

open Lean Meta Elab Tactic Waterfall
set_option Elab.async false
namespace ParallelFixture

example (P : Prop) (h : P) : P := by waterfall (cpus := 2)
example (P : Prop) (h : P) : P := by waterfall (cpus := 2) (mode := .committed)
example (xs : List Nat) : xs ++ [] = xs := by waterfall (cpus := 2)
example : True := by
  fail_if_success waterfall (cpus := 0)
  fail_if_success waterfall (cpus := 2) (effort := 0)
  waterfall (cpus := 1)

-- Restarts are work too. Both workers share exactly seven admitted transitions,
-- and failure must restore the original root rather than publish a partial state.
example : True := by
  run_tac
    let charged ← Std.Mutex.new 0
    let root ← getMainGoal
    let succeeded ← tryCatchRuntimeEx (do
      discard <| Parallel.run 2 {effort := 7} #[] (fun use => use {
        charge := charged.atomically <| modify (· + 1)
        policy := ⟨Unit, (), fun space => space.restart space.current ()⟩ })
      pure true) fun _ => pure false
    unless !succeeded && !(← root.isAssigned) && (← charged.atomically get) == 7 do
      throwError "shared restart accounting or failure rollback broke"
  trivial

-- Sibling goals share an unknown. Solving separate leaves in separate workers
-- would be unsound; every worker must instead solve the entire compatible agenda.
example : True := by
  run_tac
    let saved ← Tactic.saveState
    let witness ← mkFreshExprMVar (mkConst ``Nat)
    let left ← mkFreshExprMVar (← mkEq witness (mkNatLit 0))
    let right ← mkFreshExprMVar (← mkEq witness (mkNatLit 1))
    setGoals [left.mvarId!, right.mvarId!]
    let closed ← tryCatchRuntimeEx (do
      discard <| Parallel.run 2 {effort := 20}
      pure true) fun _ => pure false
    unless !closed && !(← left.mvarId!.isAssigned) && !(← right.mvarId!.isAssigned) do
      throwError "parallel search accepted or leaked incompatible sibling states"
    saved.restore true
  trivial

-- Every invocation creates its own mutable observer. Child allocations must be
-- debited to the parent even though Lean's raw heartbeat counter is thread-local.
example : True := by
  run_tac
    let recorded ← Std.Mutex.new 0
    let before ← IO.getNumHeartbeats
    discard <| Parallel.run 2 {effort := 30} #[] fun use => do
      let recorder ← Observe.Recorder.create
      let hooks := recorder.hooks
      use { hooks with around := fun span outcome body => do
        let result ← hooks.around span outcome body
        if span.phase == .run then
          let rows ← recorder.rows.get
          let spent := rows.foldl (fun n r => n + r.exclusive.heartbeats) 0
          recorded.atomically <| modify (· + spent)
        pure result }
    let spent := (← IO.getNumHeartbeats) - before
    unless (← recorded.atomically get) > 0 && spent >= (← recorded.atomically get) do
      throwError "worker heartbeats were not debited to parent"

-- Round zero deliberately damages its private proof state and fails; round one
-- supplies a different witness. Only the complete winning checkpoint is adopted.
example : ∃ n : Nat, n = 1 := by
  run_tac
    discard <| Parallel.run 2 {effort := 20} #[] (fun use => use {
      trials := fun round => if round < 2 then #[(1, round + 1)] else #[]
      policy := ⟨Unit, (), fun space => space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)⟩
      extraMoves := fun _ _ strength _ group => do
        if group != .basic then return #[]
        return #[{ label := "witness", role := `fixture, run := do
          if strength == 1 then
            evalTactic (← `(tactic| refine ⟨0, ?_⟩))
            throwError "abandon wrong witness"
          evalTactic (← `(tactic| exact ⟨1, rfl⟩)) }] })

-- No work can escape its enclosing heartbeat allowance, including when a worker
-- constructs a valid proof but its total measured allocations overrun the share.
example : True := by
  run_tac
    let root ← getMainGoal
    let closed ← tryCatchRuntimeEx (do
      let start ← IO.getNumHeartbeats
      withTheReader Core.Context (fun c => {c with initHeartbeats := start, maxHeartbeats := 1}) do
        discard <| Parallel.run 2 {effort := 10}
      pure true) fun _ => pure false
    unless !closed && !(← root.isAssigned) do throwError "parallel ambient cap bypassed"
  trivial

-- A completed worker cancels its competitor. Even a competitor inside an
-- uninterruptible IO operation must finish cleanup before the caller returns.
example : True := by
  run_tac
    let active ← Std.Mutex.new 0
    discard <| Parallel.run 2 {effort := 20} #[] (fun use => use {
      trials := fun round => if round < 2 then #[(1, round + 1)] else #[]
      policy := ⟨Unit, (), fun space => space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)⟩
      extraMoves := fun _ _ strength _ group => do
        if group != .basic then return #[]
        return #[{ label := "cancellation", role := `fixture, run := do
          active.atomically <| modify (· + 1)
          try
            IO.sleep (if strength == 1 then 40 else 5)
            if strength == 1 then throwError "slow unsuccessful worker"
            evalTactic (← `(tactic| exact True.intro))
          finally
            active.atomically <| modify (· - 1) }] })
    unless (← active.atomically get) == 0 do
      throwError "parallel search returned before worker cleanup"

end ParallelFixture
