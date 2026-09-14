# Examples from Software Foundations

These three adaptations are in [Docs/Examples.lean](../Docs/Examples.lean). All definitions and
helper proofs are included. The file imports only Waterfall and is checked by `lake test` on
Lean 4.33.1 and 4.30.0.

After `lake build`, the file can also be checked with `lake env lean Docs/Examples.lean`.

<nav aria-label="Examples">

[Optimization](#optimizer) · [Insertion sort](#sorting) · [Tree traversal](#traversal)

</nav>

<section id="optimizer">

*Logical Foundations / Imp*

## Expression optimization

`optimize` recursively eliminates `0 + e` in an arithmetic AST. Its semantic-preservation
statement is:

```lean
theorem optimize_sound (a : AExp) : eval (optimize a) = eval a := by
  waterfall [eval, optimize]
```

The nested pattern `plus (num 0) b` requires additional discrimination within the addition case
of structural induction. The supplied definitions expose both the optimizer’s equations and the
evaluation equations to normalization.

<details>

<summary>Complete optimizer example</summary>

```lean
import Waterfall

namespace Waterfall.Examples.Optimization

/-! An optimizer erases `0 + e` anywhere inside an arithmetic expression.
Its correctness statement relates two recursive functions, including the
optimizer's special case inside the addition constructor. -/
inductive AExp where
  | num : Nat → AExp
  | plus : AExp → AExp → AExp
  | minus : AExp → AExp → AExp
  | times : AExp → AExp → AExp

def eval : AExp → Nat
  | .num n => n
  | .plus a b => eval a + eval b
  | .minus a b => eval a - eval b
  | .times a b => eval a * eval b

def optimize : AExp → AExp
  | .num n => .num n
  | .plus (.num 0) b => optimize b
  | .plus a b => .plus (optimize a) (optimize b)
  | .minus a b => .minus (optimize a) (optimize b)
  | .times a b => .times (optimize a) (optimize b)

theorem optimize_sound (a : AExp) : eval (optimize a) = eval a := by
  waterfall [eval, optimize]

end Waterfall.Examples.Optimization
```

</details>

*Adapted from [Software Foundations:
Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html).*

</section>

<section id="sorting">

*Verified Functional Algorithms / Sort*

## Insertion sort

`Sorted` is the inductive adjacent-order predicate from VFA. Insertion preservation couples
elimination of sortedness evidence with the comparison split in `insert`:

```lean
theorem insert_sorted (x : Nat) (xs : List Nat) :
    Sorted xs → Sorted (insert x xs) := by
  waterfall (effort := 3000) [insert]
```

This invocation uses effort 3,000. Supplying the preservation lemma then discharges sortedness
of the recursive sort:

```lean
theorem sort_sorted (xs : List Nat) : Sorted (sort xs) := by
  waterfall [sort, insert_sorted]
```

The permutation argument has a separate obligation: composing `List.Perm.cons` with
`insert_perm` instantiated at `sort xs`. Waterfall proves `insert_perm`, but neither the direct
invocation nor induction followed by Waterfall closed this composition at the tested default
budgets. The example retains that step explicitly:

```lean
theorem sort_perm (xs : List Nat) : List.Perm xs (sort xs) := by
  -- Keep this short permutation composition explicit; Waterfall proves the
  -- insertion and sortedness obligations above, including the case analysis.
  induction xs with
  | nil => exact List.Perm.nil
  | cons x xs ih => exact (List.Perm.cons x ih).trans (insert_perm x (sort xs))
```

The final specification packages permutation and sortedness:

```lean
theorem sort_correct (xs : List Nat) :
    List.Perm xs (sort xs) ∧ Sorted (sort xs) := by
  waterfall [sort_perm, sort_sorted]
```

<details>

<summary>Complete insertion-sort example</summary>

```lean
import Waterfall

namespace Waterfall.Examples.Sorting

/-! Insertion sort needs both an order guarantee and a permutation guarantee:
a function that returns `[]` would meet sortedness alone. -/
def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def sort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (sort xs)

inductive Sorted : List Nat → Prop where
  | nil : Sorted []
  | single (x : Nat) : Sorted [x]
  | step (x y : Nat) (xs : List Nat) :
      x ≤ y → Sorted (y :: xs) → Sorted (x :: y :: xs)

theorem insert_sorted (x : Nat) (xs : List Nat) :
    Sorted xs → Sorted (insert x xs) := by
  waterfall (effort := 3000) [insert]

theorem sort_sorted (xs : List Nat) : Sorted (sort xs) := by
  waterfall [sort, insert_sorted]

theorem insert_perm (x : Nat) (xs : List Nat) :
    List.Perm (x :: xs) (insert x xs) := by
  waterfall [insert, List.Perm.refl, List.Perm.cons, List.Perm.swap]

theorem sort_perm (xs : List Nat) : List.Perm xs (sort xs) := by
  -- Keep this short permutation composition explicit; Waterfall proves the
  -- insertion and sortedness obligations above, including the case analysis.
  induction xs with
  | nil => exact List.Perm.nil
  | cons x xs ih => exact (List.Perm.cons x ih).trans (insert_perm x (sort xs))

theorem sort_correct (xs : List Nat) :
    List.Perm xs (sort xs) ∧ Sorted (sort xs) := by
  waterfall [sort_perm, sort_sorted]

end Waterfall.Examples.Sorting
```

</details>

*Adapted from [Software Foundations:
Sort](https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html).*

</section>

<section id="traversal">

*Verified Functional Algorithms / SearchTree*

## Tree traversal

Equivalence of the append-based and accumulator traversals requires an induction hypothesis
applicable at the accumulator arguments of the recursive calls:

```lean
theorem fast_elements_helper (t : Tree V) (acc : List (Nat × V)) :
    fastElements t acc = elements t ++ acc := by
  waterfall
```

Waterfall discovers the definitions in this module, and append associativity is already
registered for simplification. The traversal theorem is the empty-accumulator specialization:

```lean
theorem fast_elements_correct (t : Tree V) :
    fastElements t [] = elements t := by
  waterfall [fast_elements_helper]
```

No binary-search-tree invariant is required; the result is structural.

<details>

<summary>Complete tree-traversal example</summary>

```lean
import Waterfall

namespace Waterfall.Examples.TreeTraversal

/-! The simple traversal appends lists. Its accumulator version avoids those
intermediate appends. The helper quantifies over every accumulator, which must
remain general through the induction; the final correctness theorem uses `[]`.
No search-tree ordering invariant is needed for this traversal equivalence. -/
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

theorem fast_elements_correct (t : Tree V) :
    fastElements t [] = elements t := by
  waterfall [fast_elements_helper]

end Waterfall.Examples.TreeTraversal
```

</details>

*Adapted from [Software Foundations:
SearchTree](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html).*

</section>

The larger [VFA experiment](index.md#results) uses a different setup, with preceding helper
facts supplied as assumptions.
