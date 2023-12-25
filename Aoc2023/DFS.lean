import Std.Lean.HashSet
import Mathlib.Data.Fintype.Card

def dfsAux [BEq α] [Hashable α]
  (f : α → List α)
  (a : α)
  (done : Lean.HashSet α)
  (_ : ¬done.contains a)
: ℕ → Lean.HashSet α
| 0 => done
| (n + 1) => Id.run <| do
  let mut done' := done.insert a
  for c in f a do
    if h : ¬done'.contains c then
      done' := dfsAux f c done' h n
  return done' 

def dfs [BEq α] [Hashable α] [Fintype α] (f : α → List α) (a : α)
: Lean.HashSet α :=
  if h : ¬Lean.HashSet.empty.contains a then -- this always happens 
    dfsAux f a {} h (Fintype.card α)
  else
    {}
