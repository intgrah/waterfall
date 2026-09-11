# Using Waterfall

Start with `import Waterfall` and `waterfall`. It closes the complete displayed
proof state or fails, restoring the input. It works well as the last tactic in
a branch, as well as an attempt at an entire theorem.

Supply definitions and lemmas as `waterfall [append, append_assoc]`. The list is
shared by the available proof operations. Waterfall automatically uses local
hypotheses and relevant definitions from the current module. It does not unfold
all imported definitions. Add the imported definition when an otherwise simple
recursive goal gets stuck.

Both modes respect Lean's registered induction and case eliminators, including
views of nonrecursive representations. Raw case analysis remains an alternative.
The Lean option `tactic.customEliminators` controls these registered views.
Local functions returning data can also discharge data-valued goals, including
Type-valued induction hypotheses.

## Search or commitment

The default `(mode := .search)` uses depth-first continuation search inside
iterative deepening over depth and solver strength. Every alternative includes
all pending sibling obligations, so a later failure can undo an earlier witness
choice. Increasing effort extends the same deterministic schedule, subject to
Lean's ambient resource limits and any custom callbacks.

`(mode := .committed)` uses the same engine with an ACL2-inspired policy. It
commits to the first locally progressing transition, scans ordinary work before
induction, ranks induction candidates, limits repeated forward steps by ancestry,
and permits one return to the original conjecture per trial. It retries ordinary
work after sibling progress. This deliberately prunes alternatives and uses a
different trial schedule and costs; it is not simply a speed switch.

## Resources and diagnostics

`(effort := 3000)` increases the global operation allowance. An attempt is a
dispatched operation, including an unsuccessful one; checkpoint restarts also
cost an attempt. Enumerating and ranking candidates consume time and heartbeats
without being separate attempts. More budget can find a stronger early solver,
but is not a guarantee of lower wall-clock time.

`attemptHeartbeats` is a base slice in **raw heartbeats**; it grows with trial
strength and is capped by the enclosing remaining allowance. Lean's
`set_option maxHeartbeats` uses thousands of raw heartbeats. The default base
slice is 20,000,000 raw heartbeats. This does not grant an unlimited parent budget.
Use an enclosing `set_option maxHeartbeats ... in` when a proof genuinely needs
more total work. `maxRecDepth` may separately limit a long search.

`waterfall?` and `(report := true)` print attempts, visited nodes, successful
trial depth/strength, raw heartbeat use and retained operation labels. Those
labels are diagnostics, not a script. For internal wall-clock measurements and
replayable plans, import `Waterfall.Observe` and use its `capture` and `replay`
interfaces.

## Enumeration and custom policies

`(lazy := false)` eagerly enumerates phase batches. `(deferChecks := true)`
delays applicability checks until a candidate is reached. They preserve offered
operations, but change their resource costs and finite-budget behavior. Neither
makes committed search complete.

`Waterfall.run config rules { Mode.search.hooks with ... }` adapts a mode using
ordinary Lean functions from `run_tac` or a compiled tactic. Use `trials` for depth/strength scheduling, `order` for a
permutation within an operation batch, `cost` for goal-aware structural costs,
and `policy.choose` for a different traversal or deliberate pruning. The engine
checks ordering permutations and structural cost floors. Custom callbacks can
still make search unfair or fail to terminate; they are trusted metaprograms.

The [compiled tutorial](../Docs/Guide.lean) demonstrates these options. The
[API reference](API.md) explains checkpoint ownership, middleware and replay.
