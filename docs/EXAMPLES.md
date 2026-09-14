# Software Foundations examples

[Docs/Examples.lean](../Docs/Examples.lean) contains three self-contained Lean
adaptations of Software Foundations examples. Run `lake test`, or after
`lake build` run `lake env lean Docs/Examples.lean`. They need only this package.
Every helper theorem is proved in the file. The examples keep the source
algorithms and specifications, with Lean constructor names and standard lists;
they do not import the larger benchmark's established-theorem assumptions.

## An expression optimizer preserves meaning

The [LF Imp chapter](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)
defines arithmetic expressions and an optimization that removes `0 + e`.
`optimize_sound` states that evaluation before and after optimization agrees
for every expression. Its proof is:

```lean
waterfall
```

The difficulty is the interaction between recursive evaluation and the special
pattern `plus (num 0) b`. The original explicit proof inducts over the expression
and splits the left operand and its numeral in the addition case. The example
lets waterfall select and combine the proof operations. It retains addition,
natural subtraction, and multiplication from the source's variable-free language.

## Insertion sort preserves order and contents

The [VFA Sort chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html)
uses an inductive sortedness predicate. Its three constructors express the empty
list, a singleton, and a pair of ordered elements followed by a sorted suffix.

`insert_sorted` is the central preservation lemma:

```lean
theorem insert_sorted (x : Nat) (xs : List Nat) :
    Sorted xs → Sorted (insert x xs) := by
  waterfall (effort := 3000)
```

The proof must connect the evidence that the input is sorted with the branches
of `insert`'s comparison. Once it is proved, `sort_sorted` uses it as a supplied
lemma. `insert_perm` proves that insertion preserves the multiset of elements.

The example keeps the short induction and permutation composition in `sort_perm`
explicit. Plain waterfall and an induction followed by waterfall did not close
that step at their tested default budgets. This is an example of mixing a small
manual argument with automation, not a claim that waterfall proves every step
of sorting without guidance. `sort_correct` then combines both properties:

```lean
theorem sort_correct (xs : List Nat) :
    List.Perm xs (sort xs) ∧ Sorted (sort xs) := by
  waterfall [sort_perm, sort_sorted]
```

## An accumulator traversal matches the simple implementation

The [VFA SearchTree chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html)
compares an in-order traversal using list append with a traversal that threads an
accumulator. The latter avoids intermediate append operations. The key lemma is:

```lean
theorem fast_elements_helper (t : Tree V) (acc : List (Nat × V)) :
    fastElements t acc = elements t ++ acc := by
  waterfall
```

Induction has to keep the accumulator general: a recursive call passes a new
accumulator, rather than the one in the original goal. waterfall discovers the
definitions in this module; append associativity is already a standard `simp`
rule. The same proof succeeds with `waterfall (mode := .committed)`. The final
theorem specializes this lemma to `[]`.
The equivalence applies to every tree; it needs no search-tree ordering invariant.
The full definition and helper proof also appear in the README and are compiled
from that literal code block by `lake -d docbuild exe site check-docs`.

## Proof hints and evaluation scope

Replace a `waterfall` call with `waterfall?` to obtain an editor replacement
containing checked proof commands. Both support the same options and supplied
lemmas. A suggested script may still use `simp_all` or `grind` for its leaf goals.

These examples illustrate proof structure. The separate [full-corpus
evaluation](EVALUATION.md) covers 509 VFA theorem/example goals across 15 chapters,
with 390 search and 354 committed successes at commit `6ff4eb9`, Lean 4.30.0 and
effort 1,000. The later [proof-hint regression](reviews/2026-09-11/SUGGESTIONS.md)
contains 53 selected VFA goals within its 111-goal panel, tested at effort 10,000.
The full-corpus and selected-panel measurements use different revisions and
budgets; neither is a rerun of the current 0.1 candidate on Lean 4.33.1.
