import waterfall

/-!
# Software Foundations examples

Self-contained Lean adaptations of examples from Software Foundations by
Benjamin C. Pierce and the Software Foundations contributors:

* Logical Foundations, Imp: https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html
* Verified Functional Algorithms, Sort: https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html
* Verified Functional Algorithms, SearchTree: https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html

These examples import only waterfall. Every helper theorem is proved here;
no benchmark assumptions or earlier case-study proofs are imported.
-/

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

-- Match the insertion result in sort's recursive case, so grind instantiates
-- the helper at sort xs rather than only at the original input list.
grind_pattern insert_perm => insert x xs

theorem sort_perm (xs : List Nat) : List.Perm xs (sort xs) := by
  waterfall

theorem sort_correct (xs : List Nat) :
    List.Perm xs (sort xs) ∧ Sorted (sort xs) := by
  waterfall [sort_perm, sort_sorted]

end waterfall.Examples.Sorting

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
