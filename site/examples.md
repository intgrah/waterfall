# Examples from Software Foundations

These three adaptations are in [Tutorial/Examples.lean](../Tutorial/Examples.lean). All definitions and
helper proofs are included. The file imports only waterfall and is checked by `lake test` on
Lean 4.33.1 and 4.30.0.

After `lake build`, the file can also be checked with `lake env lean Tutorial/Examples.lean`.

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
  waterfall
```

The nested pattern `plus (num 0) b` requires additional discrimination within the addition case
of structural induction. Both recursive definitions are found automatically in this module.

<details>

<summary>Complete optimizer example</summary>

```lean
import waterfall

namespace waterfall.Examples.Optimization

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
  waterfall

end waterfall.Examples.Optimization
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
  waterfall (effort := 3000)
```

The definition of `insert` is found automatically; this proof uses effort 3,000. The recursive
sort needs the preservation lemma as a hint:

```lean
theorem sort_sorted (xs : List Nat) : Sorted (sort xs) := by
  waterfall [insert_sorted]
```

waterfall also proves `insert_perm` without supplied rules. For `sort_perm`, the induction
case needs that lemma instantiated at `sort xs`. Lean's inferred matching pattern selects
`x :: xs`, which misses the needed instance; `grind_pattern` registers `insert x xs` instead.
With that annotation, waterfall finds the induction and closes both cases at its default
budget:

```lean
grind_pattern insert_perm => insert x xs

theorem sort_perm (xs : List Nat) : List.Perm xs (sort xs) := by
  waterfall
```

The final specification uses both proved properties as hints:

```lean
theorem sort_correct (xs : List Nat) :
    List.Perm xs (sort xs) ∧ Sorted (sort xs) := by
  waterfall [sort_perm, sort_sorted]
```

<details>

<summary>Complete insertion-sort example</summary>

```lean
import waterfall

namespace waterfall.Examples.Sorting

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
  waterfall (effort := 3000)

theorem sort_sorted (xs : List Nat) : Sorted (sort xs) := by
  waterfall [insert_sorted]

theorem insert_perm (x : Nat) (xs : List Nat) :
    List.Perm (x :: xs) (insert x xs) := by
  waterfall

grind_pattern insert_perm => insert x xs

theorem sort_perm (xs : List Nat) : List.Perm xs (sort xs) := by
  waterfall

theorem sort_correct (xs : List Nat) :
    List.Perm xs (sort xs) ∧ Sorted (sort xs) := by
  waterfall [sort_perm, sort_sorted]

end waterfall.Examples.Sorting
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

waterfall discovers the definitions in this module, and append associativity is already
registered for simplification. The traversal theorem is the empty-accumulator specialization:

```lean
theorem fast_elements_correct (t : Tree V) :
    fastElements t [] = elements t := by
  waterfall [fast_elements_helper]
```

The specialization uses the helper as a rewrite rule. No binary-search-tree invariant is
required; the result is structural.

<details>

<summary>Complete tree-traversal example</summary>

```lean
import waterfall

namespace waterfall.Examples.TreeTraversal

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

end waterfall.Examples.TreeTraversal
```

</details>

*Adapted from [Software Foundations:
SearchTree](https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html).*

</section>
