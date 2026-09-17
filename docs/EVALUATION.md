# Software Foundations evaluation

The full inductive-bench Software Foundations evaluation contains 2,190 eligible
Lean theorem/example goals. VFA contributes **509 goals across 15 chapters**.
Its catalog has 512 entries: 493 theorems, 16 examples, and three tactic-bodied
definitions excluded from proof evaluation. These are counts of the benchmark's
Lean port, not a count of every exercise in every edition of the Coq books.

| Volume | Eligible goals | Baseline | Search | Committed |
| --- | ---: | ---: | ---: | ---: |
| LF | 937 | 659 | 740 | 739 |
| PLF | 744 | 230 | 325 | 354 |
| VFA | 509 | 315 | 390 | 354 |
| Total | 2,190 | 1,204 | 1,455 | 1,447 |

The search and committed columns are the updated arms of the September 11, 2026
full-corpus capability comparison, measured at waterfall commit
[`6ff4eb9`](https://github.com/samth/waterfall/commit/6ff4eb97746a772f9ec353923343bd22c1805630).
They predate subsequent correctness fixes, parallel execution, proof hints and
the Lean 4.33.1 upgrade. The current 0.1 candidate has not been rerun on the full
corpus; these historical measurements must not be relabeled as current-revision
scores.

The run used Lean 4.30.0, effort 1,000, 200M raw search heartbeats, 1B raw
declaration heartbeats, recursion depth 2,048 and 90-second request caps. Execution
was interpreted, with one Lean thread per worker. The existing inductive-bench
dispatcher distributed work over four cluster machines. Preceding helper facts
were supplied as assumptions. The corpus was used during development and is not
held out.

Each mode had a full old-versus-new comparison on 5,960 eligible goals, including
3,770 goals from other suites. All 23,840 paired observations passed the strict
reader, with no missing or uncertain outcomes. The waterfall columns report the updated arms. The [original evaluation report](https://github.com/samth/lean-waterfall/blob/main/docs/reviews/2026-09-11/core-capabilities/README.md)
describes the comparisons and execution contract.

## Baseline

The baseline counts a goal if any of three independently budgeted profiles proves it:
`simp_all`, `grind`, or structural induction followed by simplification/grind.
Induction enumerates eligible recursive data variables and inductive proof evidence,
with either no generalization or all admissible data parameters generalized.

These baseline observations come from the completed September 6 benchmark, not the
old-core arm of the September 11 comparison. All 2,190 SF goal IDs, source hashes
and supplied-fact hashes match the later search run. The baseline profiles had an
800M raw-heartbeat search allowance, versus 200M for the reported waterfall runs;
this is a coverage comparison of the recorded configurations, not an equal-budget
speed comparison. Evaluation uncertainty contributes no baseline successes.
The [baseline summary](evaluation/sf-baselines-2026-09-06.json) records individual
profile counts and the original result source.

## Data

- [Summary and provenance](evaluation/sf-2026-09-11.json): per-volume counts,
  measured source and benchmark commits, input hashes, and the excluded VFA definitions.
- [All VFA observations](evaluation/vfa-2026-09-11.csv): 509 goals in each of
  two modes, with outcome, stopping reason and internal per-proof timing.

`successful_search_rerun_nanos` times an independent rerun of the successful
search, not replay of an already recorded plan. Failed goals have no such timer.
The CSV contains metadata and results, not vendored SF source.

The summary is derived from the strict-reader outputs
`reports/wf-single-policy-20260909/capabilities-{search,committed}-full-v2/final-analysis/`
at benchmark commit `b6a5028cc216bf73fa4ab9512105e7e01a2de865`, joined to
`catalog/tasks.tsv`. The exported counts were checked against the recorded
capability assessment; hashes in the JSON identify the exact input files.

## Separate proof-hint regression panel

The later [111-goal proof-hint check](https://github.com/samth/lean-waterfall/blob/main/docs/reviews/2026-09-16/waterfall-package-notes/docs/reviews/2026-09-11/SUGGESTIONS.md) includes
**53 selected VFA goals**, a subset used for regression testing. Search closed
43/53 and committed mode 34/53 at effort 10,000 and 800M raw heartbeats. Every
emitted replacement was independently compiled. Those counts are neither a
full-volume result nor directly comparable to the lower-budget full-corpus run.
