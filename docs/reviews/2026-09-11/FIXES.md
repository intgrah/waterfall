# Fixes for the independent review

All three findings are corrected in a behavior change separate from the
readability refactor. The public tactic syntax, inference order, stable action
identifiers, and default effort settings are unchanged.

## Cancelled-worker heartbeat accounting

`Parallel.Worker` pairs the task with a cost cell. The worker fills that cell in
a `finally` block, including when Lean propagates an interrupt instead of
returning a `Result`. The parent cancels and joins every registered worker,
charges every cost, and restores its input state in its own `finally` block.
Only then can it adopt a complete winning proof and check the aggregate limit.
Cancellation is still propagated; it is not converted into an ordinary failed
proof operation. No shared mutable proof state was introduced.

The regression injects 100,000,000 raw heartbeats into a worker that waits for
cancellation. With an unlimited parent, the competitor's proof succeeds and the
parent must include the injected debt. With a 50,000,000-heartbeat parent, that
otherwise valid proof must be rejected and the original goal remain unassigned.
Both cases also require the cancelled worker's cleanup to have completed.

## Committed induction's sibling scan

An induction expansion that yields no transition now continues to the next
earlier sibling. `Choices.first` still wraps the whole scan, so the first
progressing transition commits even if its continuation later fails. No second
policy, fallback search, or additional induction heuristic was added.

One regression finds the earlier sibling's induction in exactly two operations
and replays its retained plan. A negative control verifies that a wrong witness
chosen by induction still prevents trying the next alternative.

## Progress through shared proof state

Local conjecture equality is now an opt-in pruning heuristic on `Move`, via
`checkLocalChange`. Built-in generators enable it, preserving their old pruning.
Extensions default to disabling it: target/assumption-type equality cannot tell
whether they advanced a shared witness, another goal, or local values. Providers
can opt in or perform their own checks in their operation's `run` function.
Every structural step still costs at least one unit of depth; the attempt and
heartbeat limits and complete-proof check are unchanged.

The shared-witness regression now succeeds and replays in both search and
committed modes, with eager and lazy enumeration. Further tests check that an
unchanged extension step is bounded by depth, opting into the local guard works,
and unchanged built-in normalization is still pruned immediately.

## Validation

[Tests/ReviewFixes.lean](../../../Tests/ReviewFixes.lean) is included in `lake test`.
The focused file passed with one Lean scheduler thread and with two cluster
CPUs. Full build/tests, compiled documentation, the static site, and the
independent consumer's build and kernel check all passed on the cluster.
Both agenda orders and the shared-witness probe now succeed. The cancellation
probe charges 100,013,111 raw heartbeats against its 100,000,000 sentinel debt
(the original charged only 6,096). These injected costs are a resource-accounting
check, not a performance benchmark. All ten existing reference proof plans
remain byte-identical.

Exact sources and logs are recorded in `fix-validation.json`. No new full-corpus
performance or coverage claim is made for these targeted correctness repairs.

The core is still 499 noncomment lines. Core plus the full protocol is 620;
the complete default import is 845, including the 114-line parallel scheduler.
