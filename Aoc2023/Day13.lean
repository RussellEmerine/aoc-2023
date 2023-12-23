import Mathlib.Data.List.Palindrome
import «Aoc2023».GridArray

namespace Day13

def reflectsAt (array : Array α) (i : Fin (array.size + 1)) :=
  let bound := min i ⟨array.size - i, array.size.sub_lt_succ i⟩
  let subarray := array.toSubarray (i - bound) (i + bound)
  subarray.toArray.toList.Palindrome

instance [inst : DecidableEq α] {array : Array α} {i : Fin (array.size + 1)}
: Decidable (reflectsAt array i) := by
  unfold reflectsAt
  simp
  refine @List.Palindrome.instDecidablePalindrome ?_ ?_ _
  exact inst 

def maps (s : Array String)
: Except String (List ((m : ℕ) × (n : ℕ) × GridArray m n Bool)) :=
  let groups := List.toArray <$> (s.toList.groupBy fun i j => i ≠ "" ∧ j ≠ "").filter (· ∉ [[], [""]])
  groups.mapM fun group => do
    let array := group.map (·.toList.toArray.map (· = '#'))
    let m := array.size
    if hm : m = 0 then
      Except.error "can't make map from empty array"
    else do
    let n := (array.get ⟨0, Nat.pos_of_ne_zero hm⟩).size
    if hn : ∀ {i : ℕ} (hi : i < array.size), array[i].size = n then
      return ⟨m, n, {
        array
        h₁ := rfl
        h₂ := hn  
      }⟩ 
    else do
      Except.error "can't make map from uneven array"

def verticalReflections (grid : GridArray m n Bool) : ℕ :=
  (Fin.val <$> (List.finRange n).filter fun j =>
    (List.finRange m).all fun i =>
      reflectsAt (grid.row i) j).sum

def horizontalReflections (grid : GridArray m n Bool) : ℕ :=
  verticalReflections grid.transpose

def reflectionSum (grid : GridArray m n Bool) : ℕ :=
  100 * horizontalReflections grid + verticalReflections grid

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day13/test.txt")
  let grids ← IO.ofExcept (maps lines)
  println! "Test: {((fun ⟨_, _, grid⟩ => reflectionSum grid) <$> grids).sum}"
  println! "Expected: {405}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day13/task.txt")
  let grids ← IO.ofExcept (maps lines)
  println! "Task: {((fun ⟨_, _, grid⟩ => reflectionSum grid) <$> grids).sum}"

end Task1

def main : IO Unit := do
  println! "Day 13"
  println! "Task 1"
  Task1.main
  println! ""

end Day13
