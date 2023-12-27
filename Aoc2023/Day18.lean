import Lean.Data.Json.Parser
import «Aoc2023».GridArray
import «Aoc2023».DFS

namespace Day18

inductive Direction
| U
| D
| L
| R
deriving Hashable, DecidableEq

namespace Direction

def ofChar : Char → Direction
| 'U' => U
| 'D' => D
| 'L' => L
| _ => R

instance : ToString Direction where
  toString
  | U => "U"
  | D => "D"
  | L => "L"
  | R => "R"

end Direction

structure Step where 
  (dir : Direction)
  (length : ℕ)
  (color : String)

namespace Step

instance : ToString Step where
  toString step := s! "{step.dir} {step.length} (#{step.color})"

open Lean.Parsec

def parser : Lean.Parsec Step := do
  let c ← anyChar
  ws
  let length ← Lean.Json.Parser.natMaybeZero
  ws
  skipString "(#"
  let color ← manyChars hexDigit
  skipString ")"
  return { dir := Direction.ofChar c, length, color } 

end Step

abbrev DigSize : ℕ := 1000

def digEdges (steps : Array Step) : GridArray DigSize DigSize Bool := Id.run <| do
  let mut grid := GridArray.ofFn (fun _ _ => false)
  let mut (i, j) : Idx DigSize DigSize := (
    ⟨DigSize / 2, Nat.div_lt_self' _ _⟩,
    ⟨DigSize / 2, Nat.div_lt_self' _ _⟩
  )
  grid := grid.set (i, j) true 
  for step in steps do
    for _ in List.range step.length do
      match step.dir with
      | Direction.U => i := (finRotate _).symm i
      | Direction.D => i := finRotate _ i
      | Direction.L => j := (finRotate _).symm j
      | Direction.R => j := finRotate _ j
      grid := grid.set (i, j) true
--      if i = 0 ∨ j = 0 ∨ i = Fin.last _ ∨ j = Fin.last _ then
--        grid := panic! "oop" 
  return grid

def neighbors (grid : GridArray m n Bool) : Idx m n → List (Idx m n)
| (i, j) =>
  let u := if 0 < i.val then some ((finRotate _).symm i, j) else none
  let d := if i.val + 1 < m then some (finRotate _ i, j) else none
  let l := if 0 < j.val then some (i, (finRotate _).symm j) else none
  let r := if j.val + 1 < n then some (i, finRotate _ j) else none
  [u, d, l, r].reduceOption.filter (grid.get (i, j) = grid.get ·)

def digVolume (steps : Array Step) : ℕ :=
  let edges := digEdges steps
  let outside := dfs (neighbors edges) (0, 0)
  (DigSize * DigSize) - outside.size

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/test.txt")
  let steps ← IO.ofExcept (lines.mapM Step.parser.run)
  println! "Test: {digVolume steps}"
  println! "Expected: {62}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/task.txt")
  let steps ← IO.ofExcept (lines.mapM Step.parser.run)
  println! "Task: {digVolume steps}"

end Task1

def main : IO Unit := do
  println! "Day 18"
  println! "Task 1"
  Task1.main
  println! ""

end Day18

