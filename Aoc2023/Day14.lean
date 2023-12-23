import «Aoc2023».GridArray

namespace Day14

inductive Tile
| Round
| Cubed -- instead of Cube because i want five letters lol
| Empty
deriving DecidableEq

namespace Tile

def ofChar : Char → Tile
| 'O' => Round
| '#' => Cubed
| _ => Empty 

end Tile

def load (grid : GridArray m n Tile) : ℕ := Id.run <| do
  let mut total := 0
  for j in List.finRange n do
    let mut base := m + 1
    for i in List.finRange m do
      match grid.get (i, j) with
      | Tile.Round => do
        base := base - 1
        total := total + base
      | Tile.Cubed => do
        base := m - i.val 
      | Tile.Empty => pure ()
  return total

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Test: {load grid}"
  println! "Expected: {136}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Task: {load grid}"

end Task1

def main : IO Unit := do
  println! "Day 14"
  println! "Task 1"
  Task1.main
  println! "" 

end Day14
