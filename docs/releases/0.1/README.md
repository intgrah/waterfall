# Waterfall 0.1 preparation

The selected release is **0.1**, represented as `0.1.0` in Lake. The default
toolchain is Lean **4.33.1**, the latest stable release checked on 2026-09-12.
Lean **4.30.0** remains covered by the compatibility checks. The repository,
website and package remain private; no release tag or registry listing was made.

## Compatibility changes

The default proof engine, configured policies, parallel implementation and hint
frontend compile on Lean 4.33.1 without source changes. The optional canonical
serializer needed two adjustments:

- Use `MetavarContext.findLevelDepth?` instead of accessing the removed `lDepth`
  field. The accessor is also available in Lean 4.30.0.
- Bind a local-context entry explicitly and use `pure` for nested match results.
  Nested `return` has different control-flow behavior in the newer Lean
  elaborator. An initial compiling attempt returned the first local declaration
  prematurely; the existing local-let regression caught this. The delayed
  assignment branch uses the same explicit result style.

`Tests/Canonical.lean` is unchanged: its original checks for local values,
alpha-renaming, shared witnesses, universe constraints and read-only operation
all pass. No test expectation was weakened. The inference core remains 499
noncomment lines; the default import remains 1,051. Optional observation adds
317 lines, including its canonical serializer.

## Checked Software Foundations examples

[Docs/Examples.lean](../../../Docs/Examples.lean) contains eight proved theorems
in three self-contained developments:

1. LF Imp: removing `0 + e` preserves expression evaluation.
2. VFA Sort: insertion preserves sortedness and permutation, then those facts
   establish insertion-sort correctness. The short `sort_perm` composition is
   explicit; the other proof blocks use Waterfall.
3. VFA SearchTree: accumulator-based traversal agrees with append-based
   traversal, first for an arbitrary accumulator and then for `[]`.

All definitions and helper lemmas needed by these examples are included. They
import only Waterfall and contain no admitted proofs. The original chapters are
linked in the file. The README's complete tree example is separately compiled
from its literal code fence. `lake test` compiles all eight example theorems,
and `leanchecker Docs.Examples` independently checks the resulting declarations.

During preparation, `sort_perm` failed both with plain Waterfall (1,000
attempts) and with explicit induction followed by Waterfall at the ambient
resource limit. Its short direct permutation composition is retained rather
than tuning the engine for an example. These development observations are not
new benchmark coverage measurements.

## Benchmark claims in the README

The README now describes the **43/53 search** and **34/53 committed** results
on the VFA portion of the existing 111-goal panel. These are original Lean
4.30.0 observations at effort 10,000 and 800M raw heartbeats, with preceding
helper facts supplied as assumptions. The selected goals span Selection,
Merge, SearchTree, Queue, Redblack and Binom. The counts are neither whole-book
coverage nor measurements of this toolchain upgrade. The fresh example checks
above are separate from those historical observations.

The [original proof-hint report](../../reviews/2026-09-11/SUGGESTIONS.md) retains
all per-goal results and replacement scripts. The release evidence records the
exact input file hashes and full compiler logs for both toolchains.

## Validation evidence

Both toolchains passed the full checks above on the cluster. [Source pins and check inventory](validation.json), [Lean 4.33.1 receipt](lean-4.33.1.json), [Lean 4.30.0 receipt](lean-4.30.0.json), [4.33.1 log](lean-4.33.1.log.gz), and [4.30.0 log](lean-4.30.0.log.gz) are retained.
