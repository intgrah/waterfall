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
waterfall [eval, optimize]
```

The difficulty is the interaction between recursive evaluation and the special
pattern `plus (num 0) b`. The original explicit proof inducts over the expression
and splits the left operand and its numeral in the addition case. The example
lets Waterfall select and combine the proof operations. It retains addition,
natural subtraction, and multiplication from the source's variable-free language.

## Insertion sort preserves order and contents

The [VFA Sort chapter](https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html)
uses an inductive sortedness predicate. Its three constructors express the empty
list, a singleton, and a pair of ordered elements followed by a sorted suffix.

`insert_sorted` is the central preservation lemma:

```lean
theorem insert_sorted (x : Nat) (xs : List Nat) :
    Sorted xs → Sorted (insert x xs) := by
  waterfall (effort := 3000) [insert]
```

The proof must connect the evidence that the input is sorted with the branches
of `insert`'s comparison. Once it is proved, `sort_sorted` uses it as a supplied
lemma. `insert_perm` proves that insertion preserves the multiset of elements.

The example keeps the short induction and permutation composition in `sort_perm`
explicit. Plain Waterfall and an induction followed by Waterfall did not close
that step at their tested default budgets. This is an example of mixing a small
manual argument with automation, not a claim that Waterfall proves every step
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
  waterfall [elements, fastElements, List.append_assoc]
```

Induction has to keep the accumulator general: a recursive call passes a new
accumulator, rather than the one in the original goal. Append associativity
connects the implementations. The final theorem specializes this lemma to `[]`.
The equivalence applies to every tree; it needs no search-tree ordering invariant.
The full definition and helper proof also appear in the README and are compiled
from that literal code block by `scripts/check_docs.py`.

## Proof hints and evaluation scope

Replace a `waterfall` call with `waterfall?` to obtain an editor replacement
containing checked proof commands. Both support the same options and supplied
lemmas. A suggested script may still use `simp_all` or `grind` for its leaf goals.

These are readable examples, not an independently selected coverage benchmark.
The separate [53-goal VFA results](reviews/2026-09-11/SUGGESTIONS.md) were measured
on Lean 4.30.0 at effort 10,000 and 800M raw heartbeats. They report 43 search
successes and 34 committed successes in a six-chapter development panel, within
the larger 111-goal panel. They do not measure all of Software Foundations or
establish that the same counts hold after the Lean upgrade.
