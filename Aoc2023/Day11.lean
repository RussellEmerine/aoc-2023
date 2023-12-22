import Mathlib.Data.Nat.Dist
import «Aoc2023».GridArray

namespace Day11

abbrev Image m n := GridArray m n Bool

namespace Image

def emptyRows (image : Image m n) : Vector ℕ (m + 1) where
  val :=
    image.array.toList.scanl
      (fun acc row => acc + if row.any id then 0 else 1)
      0
  property := by
    rw [List.length_scanl, Array.toList_eq, Array.data_length, image.h₁]

def emptyCols (image : Image m n) : Vector ℕ (n + 1) :=
  emptyRows image.transpose 

def distance 
  (er : Vector ℕ (m + 1))
  (ec : Vector ℕ (n + 1))
  (increase : ℕ := 1)
  (idx₁ idx₂ : Idx m n) : ℕ :=
  idx₁.fst.val.dist idx₂.fst
   + idx₁.snd.val.dist idx₂.snd
   + increase * er[idx₁.fst].dist er[idx₂.fst]
   + increase * ec[idx₁.snd].dist ec[idx₂.snd]

def distances (image : Image m n) (increase : ℕ := 1) : ℕ :=
  let galaxies := (GridArray.indices m n).filter image.get 
  let pairs := ((·,·) <$> galaxies <*> galaxies).filter fun idx =>
    toLex idx.fst < toLex idx.snd
  let er := emptyRows image
  let ec := emptyCols image
  ((distance er ec increase).uncurry <$> pairs).sum

def ofLines (lines : Array String) : Except String ((m : ℕ) × (n : ℕ) × Image m n) := do
  let lines' : Array (Array Bool) := lines.map (List.toArray <| (· = '#') <$> String.toList ·)
  let m := lines'.size
  if hm : 0 < m then
    let n := (lines'.get ⟨0, hm⟩).size 
    if hn : ∀ {i} (hi : i < lines'.size), lines'[i].size = n then
      return ⟨m, n, {
        array := lines'
        h₁ := rfl
        h₂ := hn
      }⟩ 
    else
      Except.error "can't make image from uneven strings"
  else
    Except.error "can't make empty image"

end Image

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day11/test.txt")
  let ⟨_, _, image⟩ ← IO.ofExcept (Image.ofLines lines)
  println! "Test: {Image.distances image}"
  println! "Expected: {374}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day11/task.txt")
  let ⟨_, _, image⟩ ← IO.ofExcept (Image.ofLines lines)
  println! "Task: {Image.distances image}"

end Task1


namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day11/test.txt")
  let ⟨_, _, image⟩ ← IO.ofExcept (Image.ofLines lines)
  println! "Test 1: {Image.distances image 9}"
  println! "Expected: {1030}"
  println! "Test 2: {Image.distances image 99}"
  println! "Expected: {8410}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day11/task.txt")
  let ⟨_, _, image⟩ ← IO.ofExcept (Image.ofLines lines)
  println! "Task: {Image.distances image 999999}"

end Task2

def main : IO Unit := do
  println! "Day 11"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day11
