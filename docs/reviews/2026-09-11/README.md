# Independent adversarial review of Waterfall

Reviewed 2026-09-11. Target: `/home/samth/work/Waterfall`, baseline `75e0ecf`
plus the readability refactor in `Core.lean` and `Protocol.lean`, finalized as
`b859160c2580d4f1109aeb8b5d966851b24b8d7c`.
This review concerns the extracted package, not the legacy waterfall driver.
No source changes, local Lean builds, or corpus runs were performed by this
reviewer. Three bounded probes were supplied for the parent's reserved cluster
CPU. The parent executed all three in development attempt 144: one CPU, a
30-second process cap per probe, all exit codes zero. All three reproduced their
reported failures and their checked controls.

## Findings, ordered by priority

### P1 — Cancelled workers lose their measured heartbeat debt

**Pre-existing; source-confirmed and reproduced.**
`Waterfall/Parallel.lean:35-40` catches the worker's body with
`tryCatchRuntimeEx`, then stores its measured heartbeats in `Result`.
`Parallel.lean:120-121` debits only tasks returning an outer `.ok Result`.

Lean 4.30.0's `Lean/CoreM.lean:794-800` explicitly rethrows interrupt
exceptions from `tryCatchRuntimeEx`. Ordinary cooperative cancellation therefore
skips the worker's measurement/result construction, returns an outer `.error`,
and contributes no heartbeat debit at all. Attempts remain correctly charged
through the independent mutex; heartbeat accounting does not. This contradicts
the promise in `Parallel.lean:51-55` and `docs/API.md` that cancelled work is
charged to the parent. It can underreport cost and permit successful results
whose actual aggregate work exceeded the parent's limit.

Probe: [probes/ParallelCancelledCost.lean](probes/ParallelCancelledCost.lean). One worker explicitly charges
100,000,000 raw heartbeats, then waits for `Core.checkInterrupted` to cancel it.
The other waits for that charge and proves `True`. Both have unlimited ambient
allowance in the probe so the measured debt, not incidental timeouts, is isolated.
The cancelled worker's `finally` confirms cleanup. The parent must report at
least the sentinel's debt. Observed: cancelled-worker cleanup was `true`, but
the parent charged **6,096** heartbeats against a minimum explicit debt of
**100,000,000**. These are artificial resource-debit sentinel values, not a
proof-performance benchmark.

Small repair: publish measured worker work from `try ... finally` into an
external per-worker cell or synchronized ledger; account it after joining even
when the task's result is an exception. Do not catch cancellation as ordinary
proof failure. `MonadFinally` runs across interrupts; `tryCatchRuntimeEx` does
not. Keep the final aggregate budget check after all child work is accounted.

Related hardening, **not a confirmed reachable defect in the current parent**:
`Parallel.lean:75-121` places cancel/join after a `tryCatchRuntimeEx` block.
An interrupt *raised in that block* would bypass cleanup. The current parent
spawn/wait path has no evident `Core.checkInterrupted`/`Core.checkSystem` call;
callback initialization happens inside workers. The monitor's parent-token
polling returns `none` and reaches cleanup. I have not identified or reproduced
a present path that raises an interrupt before the join. Defensive cleanup could
use a `finally` bracket, including partially completed spawning. Preserve/rethrow
parent cancellation after cleanup. Failure snapshot restoration should likewise
not depend on a catch combinator that excludes interrupts.

### P2 — Committed induction stops before scanning an earlier eligible sibling

**Pre-existing; source-confirmed and reproduced.**
`Waterfall/Committed.lean:63-71` loops over reverse agenda order but immediately
returns the result of `candidates` for the first unassigned goal. If that goal
has no applicable induction/inversion, no earlier unassigned goal is examined.
This is not commitment after the first progressing induction: no transition has
been selected. It contradicts the surrounding scan description and loses routes
where an earlier sibling must instantiate a shared witness before the last
sibling can close.

Probe: [probes/CommittedAgenda.lean](probes/CommittedAgenda.lean), a mirror of the existing deferred-sibling
test. The only necessary induction transition belongs to the first sibling;
the second must wait for its witness. Reversing the same two pending goals is a
control requiring exactly the same proof operations. Observed: the original
agenda failed with `waterfall exhausted 0 attempts at depth 1`; merely reversing
the two goals succeeded. No progressing induction had been attempted before
the failure.

Small repair: continue the reverse-agenda scan when `candidates` returns false.
The outer `Choices.first` already stops after the first yielded transition,
including when its complete continuation later fails; no additional policy or
backtracking behavior is needed. If committing to a goal before any applicable
induction were deliberate, document it as a separate incomplete heuristic. It
is not the presently documented first-progress commitment.

### P2 — Local shape equality can veto real progress on the shared proof state

**Pre-existing; source-confirmed and reproduced extension limitation.**
`Waterfall/Core.lean:449-453,564-566` compares only the selected goal's target
and local declaration types. Equality rejects every single-child structural
transition, including arbitrary `Hooks.extraMoves`. It omits local let values,
other pending goals, and metavariables reachable only from those goals. An
operation that assigns a shared witness outside the selected proposition can
therefore make useful global progress and still be rejected as a no-op.

Probe: [probes/SharedProgress.lean](probes/SharedProgress.lean). A positive-cost operation instantiates the
witness of `∃ n, True ∧ n = 1` while the selected `True` proposition stays
unchanged. Both remaining leaves close after that assignment. The probe compares
search with manually dispatching exactly the same first operation. Observed:
search exhausted three attempts; manually dispatching that identical witness
assignment let the engine close both remaining leaves.

This is a limit on the general extension abstraction, not a demonstrated loss
in the built-in corpus and not a kernel soundness defect. A bounded structural
operation already consumes positive depth, so global-state-changing extensions
can safely be allowed without unbounded zero-cost cycles. Avoid expanding the
readability change into an unmeasured performance change: record the limitation
and test it, then decide whether the no-op check should be narrower or account
for complete state progress.

## Assessment of the readability change

No introduced behavioral regression found by source comparison. The eight
generators retain the previous statements, ordering, costs, labels, and delayed
elaboration boundaries. `MotivePlan` replaces positional generalization/Boolean
arguments with named proof choices. The common simplifier builder preserves
both normalizing and terminal uses. Moving `Config` and `Stats` preserves their
public qualified names and makes the protocol easier to read.

The result is substantially easier to navigate: `movesFor` is a concise map of
the proof vocabulary, while `expand`, `proveAll`, and `run` distinguish a local
inference, its complete continuation, and iterative deepening. The operations
remain proposed alternatives, rather than being misleadingly described as a
mandatory sequential pipeline. `docs/IMPLEMENTATION.md` makes that distinction
and reports the full helper/protocol cost honestly.

The main remaining complexity is concentrated at genuine trust boundaries:
compatible Lean snapshots, retained proof plans, cancellation, and resource
accounting. The cancelled-work defect illustrates why naming a success/failure
container is insufficient unless exceptional exits are represented explicitly.
No case-study-specific logic, unsafe code, or new inference family was introduced
by the readability work.

The parent reports ten representative before/after proof plans (five goals in
both modes) are byte-identical. Full build, tests, compiled documentation, site
generation, and the independent consumer's build/kernel check passed in cluster
development attempt 143. This is parent-executed verification, not a second
reviewer build. The adversarial probes were separately run in attempt 144.

These findings should become separate behavior-fix follow-ups. None was
introduced by the readability refactor, so I would not fold their corrections
silently into that change or infer an unmeasured corpus-coverage impact.

## Limits of this review

This is source review plus bounded adversarial scheduling/resource probes, not
a proof of engine correctness, exhaustive policy completeness, or a fresh corpus
evaluation. In particular, the structural progress finding has no measured
default-profile coverage impact. The user-facing tactic still relies on Lean's
kernel to check declarations; `checkComplete` checks assignment completeness and
absence of direct sorry terms, not a separate kernel recheck.

## Reproduce the findings

From the repository root after `lake test`, run each file with
`lake env lean docs/reviews/2026-09-11/probes/<Name>.lean`. Use a 30-second
process timeout for the cancellation probe. The probes print the observed
failure and a successful control, and finish with valid Lean proofs; exit zero
means the diagnostic ran, not that the reported defect is fixed. The cancellation
probe injects a known raw heartbeat count, so it does not require that much real
allocation work.

The baseline and final validation logs are retained in compressed form, with
their hashes, exact source pins, and proof-plan comparison in
[validation.json](validation.json). The full suite and all probes ran through
the existing inductive-bench cluster development runner. Default affinity was
one CPU at low priority; the explicit parallel regression used two CPUs.
No new corpus evaluation was performed. These three behavior changes remain
follow-ups, separate from the readability refactor.
