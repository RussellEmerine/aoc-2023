import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.List.BigOperators.Basic

namespace Day9

def differences (l : List ℤ) : List ℤ :=
  l.tail.zipWith (· - ·) l   -- his name is william

theorem length_differences (l : List ℤ)
: (differences l).length = l.length - 1 := by
  simp [differences, min_eq_left (l.length.sub_le 1)]

def extrapolate (l : List ℤ) : ℤ :=
  if h₀ : l.all (· = 0) then
    0
  else
    have h₁ : l ≠ [] := by
      by_contra h
      subst h
      simp at h₀
    have : (differences l).length < l.length := by
      rw [length_differences]
      refine Nat.sub_lt (List.length_pos.mpr h₁) Nat.zero_lt_one
    let c := extrapolate (differences l)
    l.getLast h₁ + c
termination_by _ => l.length 

def extrapolateBack (l : List ℤ) : ℤ :=
  if h₀ : l.all (· = 0) then
    0
  else
    have h₁ : l ≠ [] := by
      by_contra h
      subst h
      simp at h₀
    have : (differences l).length < l.length := by
      rw [length_differences]
      refine Nat.sub_lt (List.length_pos.mpr h₁) Nat.zero_lt_one
    let c := extrapolateBack (differences l)
    l.head h₁ - c
termination_by _ => l.length 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day9/test.txt")
  let history := lines.map (List.filterMap String.toInt? <| String.splitOn ·)
  println! "Test: {(history.map extrapolate).toList.sum}"
  println! "Expected: {114}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day9/task.txt")
  let history := lines.map (List.filterMap String.toInt? <| String.splitOn ·)
  println! "Task: {(history.map extrapolate).toList.sum}"
  
end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day9/test.txt")
  let history := lines.map (List.filterMap String.toInt? <| String.splitOn ·)
  println! "Test: {(history.map extrapolateBack).toList.sum}"
  println! "Expected: {2}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day9/task.txt")
  let history := lines.map (List.filterMap String.toInt? <| String.splitOn ·)
  println! "Task: {(history.map extrapolateBack).toList.sum}"
  
end Task2

def main : IO Unit := do
  println! "Day 9"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day9
