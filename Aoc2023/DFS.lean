import Std.Lean.HashSet
import Mathlib.Data.Fintype.Card

/-
depth first search.

This used to be implemented a bit more functionally, but there were some stack
overflow problems. So, I made it imperative. 
-/
def dfs [BEq α] [Hashable α] [Fintype α] (f : α → List α) (a : α)
: Lean.HashSet α := Id.run <| do
  let mut done : Lean.HashSet α := Lean.HashSet.ofList [a]
  let mut s : List α := [a]
  for _ in List.range (Fintype.card α) do
    match s with
    | [] => return done 
    | (a :: s') => 
      s := s'
      for c in f a do
        if ¬done.contains c then do
          done := done.insert c
          s := c :: s
  return done
  
