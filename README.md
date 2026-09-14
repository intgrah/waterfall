# Waterfall

Small, configurable proof search for inductive Lean goals. Waterfall combines
simplification, theorem application, case analysis and induction in one search
engine. It depends only on Lean **4.33.1** and is licensed under Apache-2.0,
the same license as Lean.

```lean
import Waterfall

inductive Tree (V : Type) where
  | empty
  | node (left : Tree V) (key : Nat) (value : V) (right : Tree V)

def elements : Tree V → List (Nat × V)
  | .empty => []
  | .node left key value right => elements left ++ (key, value) :: elements right

def fastElements : Tree V → List (Nat × V) → List (Nat × V)
  | .empty, acc => acc
  | .node left key value right, acc =>
      fastElements left ((key, value) :: fastElements right acc)

theorem fast_elements_helper (t : Tree V) (acc : List (Nat × V)) :
    fastElements t acc = elements t ++ acc := by
  waterfall
```

This is **Waterfall 0.1** (`0.1.0` in Lake), available from
[samth/Waterfall](https://github.com/samth/Waterfall).
[Website and documentation](https://samth.github.io/Waterfall/) ·
[CI](https://github.com/samth/Waterfall/actions/workflows/ci.yml).
The website is generated from [editable Markdown files](site/README.md).
There is no tagged release or Reservoir listing yet.

The example above proves that an accumulator-based tree traversal returns the
same elements as a traversal using list append. Waterfall finds an induction
proof that covers the recursive calls with changed accumulators. It is adapted
from Software Foundations' VFA SearchTree chapter; all definitions needed to run it are included.
No explicit rule list is needed: the definitions are found in the current module,
and append associativity is already registered for simplification. The proof also
succeeds with `waterfall (mode := .committed)`.

## Software Foundations

The full inductive-bench Software Foundations corpus contains **2,190 eligible
Lean theorem/example goals**. Its VFA portion has **509 goals across 15 chapters**
(512 catalog entries, excluding three definitions).

| Volume | Goals | Search | Committed |
| --- | ---: | ---: | ---: |
| LF | 937 | 740 | 739 |
| PLF | 744 | 325 | 354 |
| VFA | 509 | 390 | 354 |
| Total | 2,190 | 1,455 | 1,447 |

These full-corpus results were measured at Waterfall **6ff4eb9** on Lean
**4.30.0**, at effort **1,000** with **200M raw search heartbeats**. Preceding helper
facts are supplied as assumptions; this is a development corpus. The run predates
subsequent correctness fixes and the Lean 4.33.1 upgrade. The current 0.1 candidate
has not been rerun on the full corpus.
[Protocol, provenance and per-goal VFA results](docs/EVALUATION.md).

The separate [111-goal proof-hint regression](docs/reviews/2026-09-11/SUGGESTIONS.md)
uses higher budgets and includes 53 selected VFA goals. It validates emitted proof
scripts; its 43/53 search and 34/53 committed results are not full-volume scores.

For small examples you can read and run, see [Docs/Examples.lean](Docs/Examples.lean):

- **LF / Imp:** prove that eliminating `0 + e` preserves expression evaluation.
- **VFA / Sort:** prove insertion preserves an inductive sortedness predicate;
  combine Waterfall proofs with a short explicit permutation argument to verify
  insertion sort.
- **VFA / SearchTree:** prove accumulator-based tree traversal equivalent to
  the simple implementation, as shown above.

These standalone examples prove their own helper lemmas and import only
Waterfall. They run in `lake test`; [the walkthrough](docs/EXAMPLES.md) explains
the proof structure and supplied lemmas.

## Install with Lake

A `lakefile.toml` dependency can use the public Git repository:

```toml
[[require]]
name = "waterfall"
git = "https://github.com/samth/Waterfall.git"
rev = "main"
```

The project needs a matching `lean-toolchain`; `lake update` resolves the dependency,
and `import Waterfall` exports the tactics. Lake records the chosen commit in
`lake-manifest.json`. A local checkout can use `path = "../Waterfall"` in place of
`git` and `rev`.

Waterfall targets Lean 4.33.1; CI also checks compatibility with Lean 4.30.0.
[Release preparation](docs/RELEASE.md) records the remaining tagging and registry work.

## Use and configure

```lean
import Waterfall

namespace WaterfallReadme

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

example (xs : List Nat) : append xs [] = xs := by
  waterfall [append]

example (xs : List Nat) : append xs [] = xs := by
  waterfall (mode := .committed) (effort := 3000) [append]

example (P : Prop) (h : P) : P := by
  waterfall (config := {mode := .search, effort := 1000, lazy := true})

end WaterfallReadme
```

The default `.search` mode backtracks over whole proof continuations, including
pending sibling goals. `.committed` uses an ACL2-inspired policy that commits
after local progress, tries ordinary work before induction, and can return to
the original conjecture once per trial. It can miss proofs that backtracking
finds. Both use the same inference operations.

`effort` is the main knob: more effort permits more attempts, deeper plans and
stronger operations. Lean's enclosing resource limits still apply. Use
`waterfall?` for a checked “Try this” editor hint that replaces the invocation
with ordinary Lean proof commands. Use `(report := true)` for search statistics.
Local hypotheses, registered `simp` and `grind` rules, and definitions from the
current module are used automatically. Waterfall also retrieves library theorems
for backward application. Imported definitions and additional rewrite or
instantiation rules can be supplied in brackets.

| Option | Default | Meaning |
| --- | --- | --- |
| `mode` | `.search` | Backtracking search or `.committed` |
| `cpus` | `1` | Maximum concurrent workers; total budgets remain shared |
| `effort` | `1000` | Global attempted-operation allowance |
| `attemptHeartbeats` | `20000000` | Base raw heartbeat slice per operation; strength scales it |
| `lazy` | `true` | Enumerate batches only when reached |
| `deferChecks` | `false` | Delay candidate applicability probes |
| `report` | `false` | Print search statistics |

See the [compiled Lean tutorial](Docs/Guide.lean), [user guide](docs/GUIDE.md),
and [API reference](docs/API.md). For a guided source review, read the
[proof architecture](docs/IMPLEMENTATION.md). The website includes usage examples and an option reference.

Use `waterfall (cpus := 4)` to explore different depth/strength trials of the
same policy concurrently on at most four dedicated worker threads. The first completed proof wins; timings,
retained plans and finite-budget coverage can vary. Workers share the attempt
allowance and divide the remaining heartbeat allowance. Operating-system CPU affinity can further limit concurrency. Cancellation is
cooperative, and all workers are joined before returning. The default of one
CPU uses the existing sequential path. See [parallel execution](docs/API.md#parallel-execution).

## Extend it

`Waterfall.run` accepts `Config`, supplied rules and `Hooks`. A `SearchPolicy`
selects a lazy sequence of compatible proof checkpoints; its typed state can
hold a frontier. Goal-aware callbacks configure ordering and costs. The engine
owns metering, rollback, sibling obligations and complete-proof validation.

Import `Waterfall.Observe` explicitly for internal timing, cost traces,
action recording, cooperative deadlines and exact-plan replay. Observation is
outside the default import closure. Auxiliary lemma synthesis and the earlier
large Waterfall implementation are not part of this package.

## Build and check

```sh
lake build
lake test
lake -d docbuild build
lake -d docbuild test
lake -d docbuild exe site check-docs
```

The inference engine has 499 noncomment lines. Including its protocol gives
622; the complete default import, including both configured modes and the tactic
interface, parallel scheduler and proof hints, is 1,051. Optional observation adds 317 lines. These counts include
local helpers; the package does not claim a sub-500-line complete import.

[Proof-hint validation on all 111 goals](docs/reviews/2026-09-11/SUGGESTIONS.md)
includes every emitted replacement and its individual proof timing.

The [independent adversarial review](docs/reviews/2026-09-11/README.md)
records three reproduced issues: cancelled-worker heartbeat accounting,
committed induction's sibling scan, and progress detection for general extensions.
All three now have [fixes and regression tests](docs/reviews/2026-09-11/FIXES.md).

The tests include backtracking, shared witnesses, exhaustion, commitment,
configuration, checkpoint recovery and recorded-plan replay. Proofs are checked
by Lean; successful return requires all original obligations to be complete.

Waterfall is strongest on inductive data with usable recursive definitions and
helper lemmas. It remains bounded automation: missing lemmas, difficult mutual
induction, and unsuitable operation ordering can prevent closure. It is inspired
by ACL2 and proof-planning research; it is not an implementation of all ACL2
reasoning machinery. [SOURCE.json](SOURCE.json) records the extraction origin.
