import waterfall

open Lean Elab Tactic waterfall
-- Exercise calls made from Lean's own asynchronous elaboration workers. With a
-- one-thread task pool, a polling coordinator must not starve its proof tasks.
set_option Elab.async true
elab "parallel_from_pool" : tactic => do
  discard <| Parallel.run 2 {effort := 10} #[] (fun use => use {
    trials := fun r => if r < 2 then #[(1, 1)] else #[]
    policy := ⟨Unit, (), fun space => space.expand 0 #[#[.basic]] (fun c => c.move.role == `fixture)⟩
    extraMoves := fun _ _ _ _ group => do
      if group != .basic then return #[]
      return #[{ label := "delayed closure", role := `fixture, run := do
        -- Real Lean operations can themselves await queued tasks. Dedicated
        -- proof threads alone do not help if their caller occupies the pool.
        let nested ← BaseIO.asTask (pure ())
        discard <| IO.wait nested
        IO.sleep 10
        evalTactic (← `(tactic| exact True.intro)) }] })

example : True := by parallel_from_pool
example : True := by parallel_from_pool
example : True := by parallel_from_pool
