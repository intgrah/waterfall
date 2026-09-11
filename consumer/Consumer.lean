import Waterfall

namespace Consumer

def append : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => x :: append xs ys

theorem search (xs : List Nat) : append xs [] = xs := by waterfall [append]
theorem committed (xs : List Nat) : append xs [] = xs := by
  waterfall (mode := .committed) [append]

#print axioms search
#print axioms committed
end Consumer

example (P : Prop) (h : P) : P := by
  waterfall (cpus := 2)
