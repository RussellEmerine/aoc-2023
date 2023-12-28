import Lean.Data.Json.Parser
import Mathlib.Data.Nat.Digits
import Mathlib.Data.List.Intervals
import Std.Data.Array.Merge
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

def hex : Char → Nat
| '0' => 0
| '1' => 1
| '2' => 2
| '3' => 3
| '4' => 4
| '5' => 5
| '6' => 6
| '7' => 7
| '8' => 8
| '9' => 9
| 'a' => 10
| 'A' => 10
| 'b' => 11
| 'B' => 11
| 'c' => 12
| 'C' => 12
| 'd' => 13
| 'D' => 13
| 'e' => 14
| 'E' => 14
| 'f' => 15
| 'F' => 15
| _ => 0

def swap (step : Step) : Step where
  dir :=
  match step.color.toList.last' with
    | (some '0') => Direction.R
    | (some '1') => Direction.D
    | (some '2') => Direction.L
    | _ => Direction.U 
  length := Nat.ofDigits 16 (hex <$> step.color.toList.dropLast).reverse 
  color := ""

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

def neighbors (grid : GridArray m n Bool) : Idx m n → List (Idx m n)
| (i, j) =>
  let u := if 0 < i.val then some ((finRotate _).symm i, j) else none
  let d := if i.val + 1 < m then some (finRotate _ i, j) else none
  let l := if 0 < j.val then some (i, (finRotate _).symm j) else none
  let r := if j.val + 1 < n then some (i, finRotate _ j) else none
  [u, d, l, r].reduceOption.filter (grid.get (i, j) = grid.get ·)

def coordinates (x : ℤ × ℤ) : List Step → List (ℤ × ℤ)
| [] => [x]
| (step :: steps) =>
  let (i, j) := x
  let x' :=
    match step.dir with
    | Direction.U => (i - step.length, j)
    | Direction.D => (i + step.length, j)
    | Direction.L => (i, j - step.length)
    | Direction.R => (i, j + step.length)
  x :: coordinates x' steps 

def sortedIds (array : Array ℤ) 
: (n : ℕ) × Std.HashMap ℤ (Fin n) :=
  let min := array.toList.minimum?.getD (-1000000000)
  let max := array.toList.maximum?.getD (1000000000)
  let buffered := array.append #[min - 1, min - 2, max + 1, max + 2]
  let sorted := buffered.sortAndDeduplicate 
  ⟨sorted.size, Std.HashMap.ofList (sorted.toList.zip (List.finRange sorted.size))⟩ 

def digVolume (steps : Array Step) : ℕ := Id.run <| do
  let coords := coordinates (0, 0) steps.toList
  let ⟨n', map'⟩ := sortedIds (coords >>= fun (i, j) => [i, i + 1, j, j + 1]).toArray
  match n' with
  | (Nat.succ (Nat.succ n)) => do 
    let map : Std.HashMap ℤ (Fin n.succ.succ) := map'
    let rev := Std.HashMap.ofList (Prod.swap <$> map.toList)
    -- all of these should be find! but that causes panics where the program still works, not sure why
    let sizes : GridArray (n + 1) (n + 1) ℕ := GridArray.ofFn fun i j =>  
      (rev.findD i.succ 0 - rev.findD i 0).toNat * (rev.findD j.succ 0 - rev.findD j 0).toNat 
    let mut grid : GridArray (n + 1) (n + 1) Bool := GridArray.ofFn fun _ _ => false
    for ((x₁, y₁), (x₂, y₂)) in coords.zip (coords.tail ++ [((0, 0) : ℤ × ℤ)]) do
      -- these *really* should be find! but that also panics.
      -- oddly the program still runs fine after the panic message,
      -- and the answer still prints
      -- moreover, i tried making the function return Option ℕ and have this terminate early
      -- ...and it ran fine. so absolutely no idea why the panic message show up
      let ((i₁, j₁), (i₂, j₂)) := ((map.findD x₁ 0, map.findD y₁ 0), (map.findD x₂ 0, map.findD y₂ 0))
      for (i, j) in (·,·) -- his name is jeff
        <$> List.Ico (min i₁ i₂) (finRotate _ (max i₁ i₂))
        <*> List.Ico (min j₁ j₂) (finRotate _ (max j₁ j₂))
      do
        grid := grid.set (i, j) true
    let outside := dfs (neighbors grid) (0, 0)
    return (sizes.get <$> (GridArray.indices (n + 1) (n + 1)).filter (¬outside.contains ·)).sum 
  | _ => return 0

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

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/test.txt")
  let steps ← IO.ofExcept (lines.mapM Step.parser.run)
  println! "Test: {digVolume (steps.map Step.swap)}"
  println! "Expected: {952408144115}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/task.txt")
  let steps ← IO.ofExcept (lines.mapM Step.parser.run)
  println! "Task: {digVolume (steps.map Step.swap)}"

end Task2

def main : IO Unit := do
  println! "Day 18"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day18

