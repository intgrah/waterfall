# Reading the proof engine

Start with `movesFor` in [Core.lean](../Waterfall/Core.lean). Its eight cases are
the proof vocabulary. Each calls a named generator that **proposes** proof steps;
it does not yet apply them. A `Move` holds the deferred inference, its intrinsic
cost, and semantic metadata for scheduling. Array order matters: recorded plans
identify a step by its group and its original ordinal.

| Generator | What it contributes to a proof |
| --- | --- |
| `closeGoal` | Assumption/reflexivity/contradiction, arithmetic, simplification, grind, and constructors that can close a leaf |
| `prepareGoal` | Introduce binders, turn function equality into pointwise equality, normalize, or split the target |
| `analyzeHypotheses` | Split expressions in assumptions and invert inductive evidence, including registered case views |
| `applyRules` | Apply an assumption or supplied theorem backward; construct the target with premises left as obligations |
| `applyLibraryTheorems` | Retrieve indexed library theorems and propose each applicable direction separately |
| `instantiateHypotheses` | Apply a quantified assumption to an existing term or bounded constructor chain, adding a derived fact |
| `followRecursion` | Perform functional induction or case analysis on a recursive call appearing in the problem |
| `inductOrAnalyzeData` | Induct on data or evidence with several motives, or try ordinary data case analysis |

Smaller proof operations have their own names too. `simplification` configures
the same strength-scaled simplifier for closure and normalization. `caseAlternatives`
offers the registered view before raw cases. `chooseImplicitWitnesses` proposes
one constructor layer for an implicit data argument; every unresolved field
remains an obligation. `MotivePlan` records which variables to generalize and
whether to abstract fixed indices with equations; `inductWithMotive` performs
that preparation, induction, and reintroduction of dependent assumptions.

## From a proposed step to a complete proof

`expand` selects one `Job` from a `Node`, prepares rules, and lazily enumerates
the requested stages. Each candidate receives its stable identifier before
applicability filtering or policy reordering. `attempt` charges the global work
allowance and runs one inference inside a bounded heartbeat slice. A closer is
accepted only if it leaves no children. Built-in steps request local stutter
pruning: a single unchanged conjecture is rejected by `conjectureShape`.
Extensions default to allowing local stutter because a step may advance a
shared witness or another obligation. `Move.checkLocalChange` makes this
heuristic explicit; every structural transition still spends positive depth.

Successful local inference is still only a proposal. The successor checkpoint
contains its new child obligations **and every pending sibling**, under the same
Lean metavariable assignments. `proveAll` passes these whole checkpoints to the
policy and follows the selected continuations. For example, choosing a witness
for an existential may make its first premise true and its second false. The
default policy can restore the entire earlier state and try another witness.
Proving siblings independently and combining their assignments would be wrong.

`run` calls `proveAtDepthAndStrength` along the configured trial schedule. Depth
limits structural proof steps; strength increases solver limits and their
heartbeat slices. Effort counts attempts across every failed branch and trial.
Only after the whole agenda closes are retained `Selection`s delivered to
observers. `checkComplete` verifies every original root has a proof without
unresolved metavariables or direct sorry terms. Lean checks the declarations.

## Where the other pieces belong

[Protocol.lean](../Waterfall/Protocol.lean) defines the shared data and callbacks:
resource `Config`, spent-work `Stats`, proof `Move`s and `Selection`s, pending
`Job`s, compatible `Node`s, and the policy's `Space`. Moving Config and Stats here
keeps these interfaces together; it does not reduce the total implementation.

The default policy follows every continuation in order. [Committed.lean](../Waterfall/Committed.lean)
uses the same operations with first-progress commitment, ordinary work before
induction, and one return to the original conjecture per trial. It deliberately
discards alternatives. [Parallel.lean](../Waterfall/Parallel.lean) distributes
depth/strength trials of either policy across isolated workers; it shares work
accounting and adopts only a whole completed proof. These modules do not add
inference rules.

[Observe.lean](../Waterfall/Observe.lean) adds optional timing, resource control,
recording, and exact-plan replay through middleware. [Tactic.lean](../Waterfall/Tactic.lean)
parses the public options. The proof engine owns rollback and acceptance; IO
counters and other external callback effects cannot be rolled back.

## Size and refactoring limits

The engine remains 499 noncomment lines after the three review fixes. Including
the complete protocol gives 620; the default import is 845. Before these fixes
the corresponding totals were 499, 619, and 835. The increase is the explicit
progress contract and interrupt-safe worker accounting, outside the proof engine.
Counts include all local helpers and are reproduced by `python3 scripts/size.py`;
moving shared data declarations is not counted as an overall reduction. No new
search policy, inference family, or dependency was introduced.
