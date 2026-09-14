# Checked proof hints for waterfall

`waterfall?` now offers Lean's standard **Try this** hint and editor replacement.
Clicking it replaces the entire invocation, including options and supplied
rules, with ordinary Lean proof commands. Both modes and the `cpus` option work.
Use `(report := true)` separately for search statistics.

## Results on all 111 goals

| Mode | Ordinary waterfall | Successful hints | Fresh replacements accepted |
|---|---:|---:|---:|
| Search | 98/111 | 98/111 | 98/98 |
| Committed | 72/111 | 72/111 | 72/72 |

All 111 canonical goals were executed in each mode. Every proof found by the
ordinary control has a valid replacement: **170/170 emitted scripts
compiled in fresh Lean processes**, with no hint-emission or replacement
failures. The remaining goals fail during search at this budget. Every target
started its internal timer; no outcome was inferred from a missing measurement.

The scripts contain no waterfall or plan-interpreter call. They follow the
winning path, omitting abandoned search branches. They range from 3
to 91 displayed lines; 2 use the checked explicit-term fallback.
Further shortening is possible.

Median individual-proof times, in seconds, on the commonly successful goals:

| Mode | Search plus checked hint | Replacement only | Slowest replacement |
|---|---:|---:|---:|
| Search | 0.936 | 0.083 | 11.111 |
| Committed | 4.082 | 0.051 | 11.817 |

These are internal monotonic-clock measurements, excluding imports and prefix
elaboration. Hint time includes reconstruction and checking. Each cell comes
from one run; it is not evidence for small speed differences. Ordinary control
times are also retained in the data, from the preceding full v4 run.

[All per-goal results](suggestions-results.csv),
[machine-readable summary](suggestions-results.json), and
[every actual editor replacement](suggestions-hints.json) are retained here.
Raw process logs, frozen inputs, hashes and the reproducible collection scripts
are in inductive-bench's `reports/waterfall-suggestions-20260911/` directory.
They are committed at `c34e42d4373dea8d8ca970dc7396f7c9fb796877` on the
local `wf-proof-hints-20260911` branch of inductive-bench.

## What is checked

The frontend records accepted steps through the existing middleware hook.
It reparses the literal printed text, restores the original checkpoint, executes
that text with error recovery disabled and checks every original obligation.
Only then does it publish a TryThis editor action. Each parallel worker owns
its recorder; the winning worker supplies the proof and hint.

The corpus harness independently captures the actual editor edit, verifies its
span, substitutes it into the original source, and compiles the resulting file
in a new process. It uses inductive-bench's existing cluster scheduler and paired
proof runner, with at most four single-thread workers per host on cl and kj.
Expanded inputs and results stay on node-local disks; each shard returns one
archive. The only reusable runner change recognizes named Lean diagnostics such
as `error(lean.unknownIdentifier):`, covered by its process-boundary test.

Settings: Lean 4.30.0, effort 10000, one CPU per proof, maxRecDepth 2048,
800,000,000 raw target heartbeats with the original declaration origin, and the
existing 180-second process cutoff. The frozen prefixes admit preceding helper
facts: results concern these individual targets in those contexts, rather than
recertification of entire case-study libraries. Target statements and supplied
facts are unchanged. Their source hashes match between the v4 controls and v5
final hint run. The final run executes all 222 question-mark cases again.

## Implementation and validation

The inference engine remains **499 noncomment lines**. Core plus protocol is
622; the complete default import is 1051, including the separate 200-line
[hint frontend](../../../waterfall/Suggestions.lean). No inference operation,
search policy or external dependency was added. Optional metadata describes a
functional operation's subject and shares a tactic adapter's existing command.

Common steps print as `induction`, `fun_induction`, `cases`, `generalize`,
`apply`, `have`, `simp_all`, and `grind`. Fixed-index induction retains its
equations. Leaf checks use the same sibling scope as search. Forward steps
print the small derived fact from the winning assignment. Unsupported recipes
fall back to an explicit proof term with newly created auxiliary declarations
inlined; this route is checked too.

The [regression tests](../../../Tests/Suggestions.lean) cover actual editor
spans and text, both modes, parallel execution, pending siblings, later-goal
selection, stronger solver configurations, constructors, indexed induction,
rule application, forward instantiation and private auxiliary proofs.
`lake build`, `lake test`, documentation checks, site generation, and the
independent consumer's build and `leanchecker` check passed.
[Receipts and source hashes](suggestions-validation.json) and the
[full validation log](suggestions-full.log.gz) are preserved.

The full v4 investigation exposed five emission failures after successful
search: `mergesort_sorts`, `FreshFrom.step`, committed
`cons_of_small_maintains_sort`, `perm_of_count_eq`, and `Related.mono`.
Direct rendering fixed all five. Diagnostic versions and invalid setup runs
are kept separately in the benchmark report and excluded from the final counts.
The package and site remain private; no public release or deployment was made.
