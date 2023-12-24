import «Aoc2023».GridArray

namespace Day14

inductive Tile
| Round
| Cubed -- instead of Cube because i want five letters lol
| Empty
deriving DecidableEq, Hashable

namespace Tile

def ofChar : Char → Tile
| 'O' => Round
| '#' => Cubed
| _ => Empty

instance : ToString Tile where
  toString
  | Round => "O"
  | Cubed => "#"
  | Empty => "."

end Tile

def load (grid : GridArray m n Tile) : ℕ := Id.run <| do
  let mut total := 0
  for j in List.finRange n do
    for i in List.finRange m do
      match grid.get (i, j) with
      | Tile.Round => do
        total := total + m - i.val
      | _ => pure ()
  return total

def shiftNorth (grid : GridArray m n Tile) : GridArray m n Tile := Id.run <| do
  let mut grid' := grid
  for j in List.finRange n do
    -- a list of all counts of round stones
    -- e.g. O#...#OO.# => [1, 0, 2, 0]
    let mut count := [] 
    let mut c := 0
    for i in List.finRange m do
      match grid.get (i, j) with
      | Tile.Round => do
        c := c + 1
      | Tile.Cubed => do
        count := c :: count
        c := 0
      | Tile.Empty => pure ()
    count := (c :: count).reverse
    c := count.headD 0
    count := count.tailD []
    for i in List.finRange m do
      match grid.get (i, j) with
      | Tile.Cubed => do
        c := count.headD 0
        count := count.tailD []
      | _ => do
        if c > 0 then do
          grid' := grid'.set (i, j) Tile.Round
          c := c - 1
        else do
          grid' := grid'.set (i, j) Tile.Empty
  return grid'

def shiftWest (grid : GridArray m n Tile) : GridArray m n Tile :=
  (shiftNorth grid.transpose).transpose

def shiftSouth (grid : GridArray m n Tile) : GridArray m n Tile :=
  (shiftNorth grid.reverseRows).reverseRows

def shiftEast (grid : GridArray m n Tile) : GridArray m n Tile :=
  (shiftWest grid.reverseCols).reverseCols

def cycle (grid : GridArray m n Tile) : GridArray m n Tile :=
  grid |> shiftNorth |> shiftWest |> shiftSouth |> shiftEast

def spinAux (grid : GridArray m n Tile) (i : ℕ) (map : Std.HashMap UInt64 ℕ)
: ℕ → ℕ × ℕ × GridArray m n Tile
| 0 => (0, 0, grid)
| (n + 1) =>
  match map.find? (hash grid) with
  | some j => (j, i - j, grid)
  | none => spinAux (cycle grid) (i + 1) (map.insert (hash grid) i) n

def spin (grid : GridArray m n Tile) : GridArray m n Tile :=
  let (i, k, grid') := spinAux grid 0 {} 1000000000
  let (_, _, grid'') := spinAux grid' 0 {} ((1000000000 - i) % k)
  grid''

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Test: {load (shiftNorth grid)}"
  println! "Expected: {136}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Task: {load (shiftNorth grid)}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Test: {load (spin grid)}"
  println! "Expected: {64}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray.map Tile.ofChar)))
  println! "Task: {load (spin grid)}"

end Task2

def main : IO Unit := do
  println! "Day 14"
  println! "Task 1"
  Task1.main
  println! "" 
  println! "Task 2"
  Task2.main
  println! "" 

end Day14
