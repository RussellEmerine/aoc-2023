import «Aoc2023».DFS
import «Aoc2023».GridArray

namespace Day16

inductive Direction
| N
| S
| E
| W
deriving DecidableEq, Hashable, Fintype

namespace Direction

instance : ToString Direction where
  toString
  | N => "N"
  | S => "S"
  | E => "E"
  | W => "W"

end Direction

inductive Tile
| NS
| EW
| BS -- backslash
| FS -- forward slash
| Empty
deriving DecidableEq, Hashable, Fintype 

namespace Tile

def ofChar : Char → Tile
| '|' => NS
| '-' => EW
| '\\' => BS
| '/' => FS
| _ => Empty

end Tile

-- Direction here is which direction i point towards upon entering the cell 
def neighbors (grid : GridArray m n Tile) (x : Direction × Idx m n) : List (Direction × Idx m n) :=
  match x with
  | (d, i, j) =>
    -- but these ones are after leaving the cell 
    let north := if i.val > 0 then some (Direction.N, (finRotate _).symm i, j) else none
    let south := if i.val + 1 < m then some (Direction.S, finRotate _ i, j) else none
    let east := if j.val + 1 < n then some (Direction.E, i, finRotate _ j) else none
    let west := if j.val > 0 then some (Direction.W, i, (finRotate _).symm j) else none 
    match d with 
    | Direction.N =>
      match grid.get (i, j) with
      | Tile.EW => [east, west].reduceOption 
      | Tile.BS => [west].reduceOption
      | Tile.FS => [east].reduceOption 
      | _ => [north].reduceOption 
    | Direction.S =>
      match grid.get (i, j) with
      | Tile.EW => [east, west].reduceOption
      | Tile.BS => [east].reduceOption
      | Tile.FS => [west].reduceOption
      | _ => [south].reduceOption
    | Direction.E =>
      match grid.get (i, j) with
      | Tile.NS => [north, south].reduceOption
      | Tile.BS => [south].reduceOption
      | Tile.FS => [north].reduceOption
      | _ => [east].reduceOption
    | Direction.W =>
      match grid.get (i, j) with
      | Tile.NS => [north, south].reduceOption
      | Tile.BS => [north].reduceOption
      | Tile.FS => [south].reduceOption
      | _ => [west].reduceOption

def energized
  (grid : GridArray (m + 1) (n + 1) Tile)
  (start : Direction × Idx (m + 1) (n + 1) := (Direction.E, 0, 0))
: ℕ := Id.run <| do
  let mut set : Lean.HashSet (Idx _ _) := {}
  let lit := dfs (neighbors grid) start
  for (_, idx) in lit do
    set := set.insert idx 
  return set.size

def maxEnergized (grid : GridArray (m + 1) (n + 1) Tile) : Option ℕ :=
  let left := (Direction.E, ·, 0) <$> List.finRange (m + 1)
  let right := (Direction.W, ·, Fin.last n) <$> List.finRange (m + 1)
  let top := (Direction.S, 0, ·) <$> List.finRange (n + 1)
  let bottom := (Direction.N, Fin.last m, ·) <$> List.finRange (n + 1)
  let starts := left ++ right ++ top ++ bottom
  ((energized grid ·) <$> starts).maximum? 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines' (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Test: {energized grid}"
  println! "Expected: {46}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines' (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Task: {energized grid}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines' (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Test: {maxEnergized grid}"
  println! "Expected: {some 51}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day16/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines' (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Task: {maxEnergized grid}"

end Task2

def main : IO Unit := do
  println! "Day 16"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day16
