# API reference

Lean doc comments provide hover documentation in the editor. `Docs/Guide.lean`
is a compiled tutorial. The library exports the following small interfaces.

| Module | Responsibility |
| --- | --- |
| `Waterfall` / `Waterfall.Tactic` | `waterfall`, `waterfall?`, `Mode`, `Options` |
| `Waterfall.Core` | `run`, engine transitions and root validation |
| `Waterfall.Protocol` | `Config`, `Stats`, `Move`, `Candidate`, `Job`, `Node`, `Space`, `SearchPolicy`, `Hooks` |
| `Waterfall.Choices` | Generic lazy selection, filtering, collection and commitment |
| `Waterfall.Parallel` | Isolated concurrent trials, shared work accounting and cancellation |
| `Waterfall.Committed` | ACL2-inspired callbacks over the shared engine |
| `Waterfall.Suggestions` | Checked standalone scripts and editor hints from retained paths |
| `Waterfall.Observe` | Optional timing, control middleware, action recording and replay |
| `Waterfall.Canonical` | Optional canonical goal encoding for replay checks |

The [proof architecture walkthrough](IMPLEMENTATION.md) maps these interfaces to
the named proof-stage generators and explains how their child obligations form
one compatible proof continuation. Generator helpers are private; extensions
use `movesFor`, `operations`, and `Hooks`.

## Tactic interface

`Options` extends engine `Config` with `mode : Mode := .search` and `cpus : Nat := 1`. Standard Lean configuration syntax accepts
individual fields or `(config := { ... })`. The adapter passes
`mode.hooks` and `Options.toConfig` to `Parallel.run`; one CPU calls `run` directly. Custom callback functions are
configured through `run`, preserving the arbitrary typed policy state interface.
It adds no proof-search algorithm.

`run (cfg : Config) (rules : Array (TSyntax term) := #[]) (hooks : Hooks := {})`
runs in `TacticM` and returns `Stats` after closing all original goals. Failure
restores Lean's original proof state. Effort and external observer effects are
not rolled back. `Stats.choices` contains retained labels in reverse proof order.

`waterfall?` installs `Suggestions.run` inside each worker. It records only
accepted steps and gives the winning proof a checked editor replacement.
`Suggestions.compile` accepts the input checkpoint, original goals, retained
path and rules; it returns `Script` (`tactic`, `text`, `usedTerm`) while restoring
the completed proof. It reparses the printed text and requires all original
obligations to close with error recovery disabled. The inference engine and its
recording interface are unchanged.

## Search and checkpoints

`Choices α = (α → TacticM Bool) → TacticM Bool` is effectful lazy enumeration.
Returning `true` from a visitor stops it. `Choices.first` commits to the first
emitted choice even if its downstream continuation fails; `filter` retains a
subsequence; `collect` eagerly materializes all emitted choices and pays their
cost.

A `Node σ` contains a saved Lean proof state, all pending `Job`s, typed policy
state and the retained plan. Each job has its own remaining structural allowance
and ancestry. Never combine jobs from one checkpoint with Lean state from another.

A `SearchPolicy` supplies its state type, initial state and
`choose : Space State → Choices (Node State)`. `Space.expand` enumerates metered
transitions for a selected goal and operation batches. `Space.restart` restores
a compatible checkpoint, installs new policy state and charges an attempt.
Already funded frontier entries remain selectable at attempt exhaustion; new
expansion and restart are refused. Ambient limits still constrain traversal.

## Hooks

- `charge`: reserve one operation before dispatch, including checkpoint restarts.
  Exceptions stop the run; reservations and external effects are not rolled back.
- `policy`: choose transitions, agenda order and traversal.
- `trials`: finite batches of depth/positive-strength pairs by round.
- `batches`: lazy structural groups; each original group must occur exactly once.
- `order`: a permutation of candidate selectors within a batch; validated.
- `cost`: effective path cost under the goal's context and rollback. Structural
  costs must respect the engine's positive intrinsic floor.
- `extraMoves`: append general operations without renumbering the originals.
- `around`: polymorphic middleware around a span and continuation.
- `accepted`: observe only the retained complete proof's selections, in reverse order.

An observer calls its continuation once and leaves proof state alone. Resource
control middleware can reduce allowances or abort spans. The engine owns proof
acceptance and rollback. Ordering and cost callbacks see temporary state;
external IO side effects remain the callback author's responsibility.

## Progress and extension operations

`Move.checkLocalChange` defaults to `false`. A structural extension may assign a
shared witness, change another obligation, or update local values while leaving
the selected target and assumption types unchanged. The engine accepts such a
transition and charges its positive structural cost. Final root validation is
unchanged; accepting a transition is not accepting a complete proof.

Built-in generators set `checkLocalChange := true` to preserve their existing
local stutter pruning. An extension can opt into this heuristic explicitly, or
implement its own progress checks in `Move.run`. The heuristic compares the
single child's target and assumption types with the input; it is deliberately
not a general test of proof-state equality. The engine's positive cost floor and
global attempt allowance still bound steps that leave a goal unchanged.

## Observation and replay

Import `Waterfall.Observe` explicitly. `capture` returns a `Report` with success,
error, optional timing rows and an optional `Plan`. Timing rows distinguish
inclusive and exclusive wall-clock nanoseconds and raw heartbeats. A `Control`
can supply smaller per-span slices and a cooperative deadline. Deadlines are
checked between spans; a process timeout belongs to the calling harness.

Plans store versioned action selectors, goal/agenda encodings, selected focus,
strength, costs and generated-child counts. Replay validates these against the
same operations and supplied rules; it does not search for another route. Pass
a stable source/theory key and retain the exact source version. Changed
operations, selector order, costs or unrecorded provider state can invalidate a
plan. Final root validation and Lean's kernel remain authoritative.

See `Tests/SearchPolicy.lean` for a FIFO frontier, scored successors, commitment,
sibling dependencies and charged checkpoint recovery; see `Tests/Observe.lean`
for timing and replay examples.

## Parallel execution

`Parallel.run cpus cfg rules withHooks` runs the same engine in isolated workers.
`withHooks` receives a continuation accepting `Hooks`; call it once. Allocate
mutable observers inside this function so each worker owns separate IO references:

```lean
import Waterfall
import Waterfall.Observe

open Lean Elab Tactic Waterfall
example (P : Prop) (h : P) : P := by
  run_tac
    discard <| Parallel.run 2 {} #[] fun use => do
      let recorder ← Observe.Recorder.create
      use (recorder.hooks {} Mode.search.hooks)
```

Round `i` of `Hooks.trials` belongs to worker `i % cpus`. No trial is duplicated,
and all callbacks otherwise describe one policy. The first observed complete
proof wins; ordering among simultaneous completions is unspecified. This
parallelizes iterative deepening, not sibling proof obligations or branches
inside a single trial. Committed mode retains its local commitment semantics.

A mutex reserves attempts across workers, including restarts. Each worker has
its own engine counters and elaboration state. The enclosing remaining heartbeat
allowance is divided equally; unused shares are currently not redistributed.
Each worker records its spent heartbeats in a `finally` block, independently
of whether it returns a proof result or an interrupt. The parent always cancels,
joins, and reads these costs before adopting the winner. Actual child
heartbeats, including failed and cancelled work, are charged to the
parent's thread counter before acceptance. Aggregate overruns reject the result.
Workers use dedicated threads so a caller running inside Lean's elaboration
pool cannot starve them. Operating-system CPU affinity can impose lower CPU
concurrency than `cpus`; zero is rejected. No process or CPU affinity is created
by the tactic itself. The limit is per invocation, not a global limit on
concurrent theorem elaboration.

Parent cancellation and a completed proof signal cancellation to workers, which
are always joined. Cancellation remains cooperative inside Lean operations.
Increasing both work and heartbeat limits keeps every trial eventually available
when the underlying schedule is fair. A fixed total budget can produce different
coverage from sequential execution: speculation competes for the same resources.
Custom callbacks must not share mutable IO references unless synchronized; use
`withHooks` for per-worker recorders and other local state. Observer callbacks in
an unsuccessful worker may already have run and are not undone by cancellation.
`Stats.attempts` and `nodes` are aggregate counts; depth, strength and choices
identify the winning worker. `Observe.capture` remains a sequential convenience
API; use the initializer above for parallel observation.
