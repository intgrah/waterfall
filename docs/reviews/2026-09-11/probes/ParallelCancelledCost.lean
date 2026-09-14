import waterfall

open Lean Meta Elab Tactic waterfall
set_option Elab.async false
set_option maxHeartbeats 0

-- Both lanes start an admitted action. Lane zero has measured allocation work
-- to debit, then waits until the winning lane causes cooperative cancellation.
-- tryCatchRuntimeEx never catches an interrupt, so its Result may be skipped.
example : True := by
  run_tac
    let started ← Std.Mutex.new false
    let cancelled ← Std.Mutex.new false
    let sentinel := 100000000
    let before ← IO.getNumHeartbeats
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
            evalTactic (← `(tactic| exact True.intro)) }] })
    let spent := (← IO.getNumHeartbeats) - before
    logInfo m!"cancelled worker cleaned up={← cancelled.atomically get}; parent charged={spent}; minimum debt={sentinel}"
    unless ← cancelled.atomically get do throwError "control did not cancel the slow worker"
    -- Reporting rather than asserting the bug leaves a kernel-checked proof.
