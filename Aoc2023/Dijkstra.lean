import Mathlib.Data.Fintype.Card
import Mathlib.Data.BinaryHeap

abbrev WeightedGraph α := α → List (α × ℕ)

def dijkstraAux [BEq α] [Hashable α] 
  (f : WeightedGraph α)
  (q : BinaryHeap (ℕ × α) (·.fst > ·.fst))
  (map : Std.HashMap α ℕ)
  (n : ℕ)
: Std.HashMap α ℕ :=
  match n with 
  | 0 => map
  | (n + 1) =>
    match q.extractMax with
    | (none, _) => map
    | (some (d, a), q'') => Id.run <| do
      let mut map' := map
      let mut q' := q''
      if not (map'.contains a) then
        map' := map'.insert a d
        for (c, w) in f a do
          q' := q'.insert (d + w, c)
      return dijkstraAux f q' map' n

def dijkstra [BEq α] [Hashable α] [Fintype α] (f : WeightedGraph α) (a : α)
: Std.HashMap α ℕ :=
  dijkstraAux f (BinaryHeap.singleton _ (0, a)) {} (Fintype.card α * Fintype.card α * Fintype.card α)
-- i think the iteration bound is actually |α|² but just in case
