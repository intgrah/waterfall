# Using waterfall

Start with `import waterfall` and `waterfall`. It closes the complete displayed
proof state or fails, restoring the input. It works well as the last tactic in
a branch, as well as an attempt at an entire theorem.

Supply definitions and lemmas as `waterfall [append, append_assoc]`. The list is
shared by the available proof operations. waterfall automatically uses local
hypotheses and relevant definitions from the current module. It does not unfold
all imported definitions. Add the imported definition when an otherwise simple
recursive goal gets stuck.

Both modes respect Lean's registered induction and case eliminators, including
views of nonrecursive representations. Raw case analysis remains an alternative.
The Lean option `tactic.customEliminators` controls these registered views.
Local functions returning data can also discharge data-valued goals, including
Type-valued induction hypotheses.

Backward constructor application also tries an outer constructor for one implicit
data argument when ordinary unification needs a witness. The argument must have
a visible inductive type in the constructor signature; a bare polymorphic type
parameter is outside this fallback. Fields are inferred or left as proof
obligations. This finite enumeration does not synthesize arbitrary nested terms,
guess multiple implicit arguments simultaneously, or guess witnesses for general
lemma applications.

## Search or commitment

The default `(mode := .search)` uses depth-first continuation search inside
iterative deepening over depth and solver strength. Every alternative includes
all pending sibling obligations, so a later failure can undo an earlier witness
choice. Increasing effort extends the same deterministic schedule, subject to
Lean's ambient resource limits and any custom callbacks.

`(mode := .committed)` uses the same engine with an ACL2-inspired policy. It
commits to the first locally progressing transition, scans ordinary work before
induction, ranks induction candidates, and permits one return to the original conjecture per trial. It retries ordinary
work after sibling progress. Distinct forward instances may be chained, subject
to the same depth and attempt budgets as other operations. This deliberately prunes alternatives and uses a
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

`waterfall?` offers a “Try this” hint and editor code action. Applying it replaces
the complete invocation, including its options and rule list, with ordinary
Lean proof commands. It works with both modes and with `cpus`. The replacement
contains no call to waterfall or its plan interpreter.

The frontend reconstructs the retained path and checks the printed text from the
original goal. Operations it cannot render as tactics fall back to an explicit
proof term, which can be longer. Reconstruction and checking consume additional
time and ambient heartbeats; ordinary `waterfall` does neither.

`(report := true)` prints attempts, visited nodes, successful trial depth/strength,
raw heartbeat use and retained operation labels. For internal wall-clock
measurements and replayable plans, import `waterfall.Observe` and use its
`capture` and `replay` interfaces. `trace.waterfall.suggestions` explains when
command reconstruction falls back to a proof term.

## Enumeration and custom policies

`(lazy := false)` eagerly enumerates phase batches. `(deferChecks := true)`
delays applicability checks until a candidate is reached. They preserve offered
operations, but change their resource costs and finite-budget behavior. Neither
makes committed search complete.

`waterfall.run config rules { Mode.search.hooks with ... }` adapts a mode using
ordinary Lean functions from `run_tac` or a compiled tactic. Use `trials` for depth/strength scheduling, `order` for a
permutation within an operation batch, `cost` for goal-aware structural costs,
and `policy.choose` for a different traversal or deliberate pruning. The engine
checks ordering permutations and structural cost floors. Custom callbacks can
still make search unfair or fail to terminate; they are trusted metaprograms.

The [compiled tutorial](../Tutorial/Guide.lean) demonstrates these options. The
[API reference](API.md) explains checkpoint ownership, middleware and replay.

## Multiple CPUs

`waterfall (cpus := 4)` runs different trials of the selected policy concurrently.
The tactic uses dedicated worker threads; CPU affinity may further limit concurrency. Attempts and
heartbeats remain total budgets; more CPUs do not multiply either allowance.
Each worker keeps a complete proof state, including dependent siblings. The first
complete proof wins, then all other workers are cancelled and joined.

At a fixed budget this changes which trials receive work, so it can gain or lose
proofs and does not guarantee a speedup. A difficult single trial is still
sequential. One CPU is the default and preserves sequential execution.
