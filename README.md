# Waterfall

Small, configurable proof search for inductive Lean goals. Waterfall combines
simplification, theorem application, case analysis and induction in one search
engine. It depends only on Lean **4.30.0** and is licensed under Apache-2.0,
the same license as Lean.

```lean
import Waterfall

example (xs : List Nat) : xs ++ [] = xs := by
  waterfall
```

This is a **private, unreleased candidate**, hosted at
[samth/Waterfall](https://github.com/samth/Waterfall). It is not registered in Reservoir. The website is in [site/index.html](site/index.html).

## Install locally with Lake

Put this checkout next to your project, then add to your `lakefile.toml`:

```toml
[[require]]
name = "waterfall"
path = "../Waterfall"
```

Use the same `lean-toolchain`, run `lake update`, then `import Waterfall`.
Repository access is required to clone the private Git repository. Public
distribution and Reservoir registration remain pending. [Release preparation](docs/RELEASE.md) records the
remaining publication steps.

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
`waterfall?` for a diagnostic summary; it does not emit a standalone proof script.
Imported definitions and helpful lemmas can be supplied in brackets. Local
hypotheses are used automatically.

| Option | Default | Meaning |
| --- | --- | --- |
| `mode` | `.search` | Backtracking search or `.committed` |
| `cpus` | `1` | Maximum concurrent workers; total budgets remain shared |
| `effort` | `1000` | Global attempted-operation allowance |
| `attemptHeartbeats` | `20000000` | Base raw heartbeat slice per operation; strength scales it |
| `lazy` | `true` | Enumerate batches only when reached |
| `deferChecks` | `false` | Delay candidate applicability probes |
| `report` | `false` | Print search statistics; enabled by `waterfall?` |

See the [compiled Lean tutorial](Docs/Guide.lean), [user guide](docs/GUIDE.md),
and [API reference](docs/API.md). For a guided source review, read the
[proof architecture](docs/IMPLEMENTATION.md). The website includes an option configurator.

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
outside the default import closure. Lemma discovery and the earlier large
Waterfall implementation are not part of this package.

## Build and check

```sh
lake build
lake test
python3 scripts/check_docs.py
python3 scripts/size.py
python3 scripts/build_site.py
```

The inference engine has 499 noncomment lines. Including its protocol gives
619; the complete default import, including both configured modes and the tactic
interface and parallel scheduler, is 835. Optional observation adds 316 lines. These counts include
local helpers; the package does not claim a sub-500-line complete import.

The [independent adversarial review](docs/reviews/2026-09-11/README.md)
records three reproduced, pre-existing issues to address separately: cancelled
worker heartbeat accounting, committed induction's sibling scan, and progress
detection for general extensions. The package remains an unreleased candidate.

The tests include backtracking, shared witnesses, exhaustion, commitment,
configuration, checkpoint recovery and recorded-plan replay. Proofs are checked
by Lean; successful return requires all original obligations to be complete.

Waterfall is strongest on inductive data with usable recursive definitions and
helper lemmas. It remains bounded automation: missing lemmas, difficult mutual
induction, and unsuitable operation ordering can prevent closure. It is inspired
by ACL2 and proof-planning research; it is not an implementation of all ACL2
reasoning machinery. [SOURCE.json](SOURCE.json) records the extraction origin.
