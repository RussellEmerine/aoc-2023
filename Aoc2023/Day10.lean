import Mathlib.Logic.Equiv.Fin
import «Aoc2023».DFS 
import «Aoc2023».GridArray

namespace Day10

inductive Tile
| NS
| EW
| NW
| NE
| SW
| SE
| Ground
deriving Hashable, DecidableEq, Fintype 

namespace Tile

def ofChar : Char → Tile
| '|' => NS
| '-' => EW
| 'J' => NW
| 'L' => NE
| '7' => SW
| 'F' => SE
| 'S' => SE
| _ => Ground

def facingN : Finset Tile := {NS, NW, NE}
def facingS : Finset Tile := {NS, SW, SE}
def facingE : Finset Tile := {EW, NE, SE}
def facingW : Finset Tile := {EW, NW, SW}

end Tile

abbrev Idx m n := Fin m × Fin n

namespace Idx

def n {m n} (idx : Idx m n) : Idx m n := ((finRotate _).symm idx.fst, idx.snd)

def s {m n} (idx : Idx m n) : Idx m n := (finRotate _ idx.fst, idx.snd)

def e {m n} (idx : Idx m n) : Idx m n := (idx.fst, finRotate _ idx.snd)

def w {m n} (idx : Idx m n) : Idx m n := (idx.fst, (finRotate _).symm idx.snd)

end Idx

structure Grid (m n : ℕ) where
  (grid : GridArray m n Tile)
  (start : Idx m n)

namespace Grid

def get (grid : Grid m n) (idx : Idx m n) : Tile :=
  grid.grid.get idx 

def next (grid : Grid m n) (prev : Idx m n) (idx : Idx m n) : Idx m n :=
  let chooseTwo (a b : Idx m n) : Idx m n := if a = prev then b else a
  match grid.get idx with
  | Tile.NS => chooseTwo (Idx.n idx) (Idx.s idx)
  | Tile.EW => chooseTwo (Idx.e idx) (Idx.w idx)
  | Tile.NE => chooseTwo (Idx.n idx) (Idx.e idx)
  | Tile.NW => chooseTwo (Idx.n idx) (Idx.w idx)
  | Tile.SE => chooseTwo (Idx.s idx) (Idx.e idx)
  | Tile.SW => chooseTwo (Idx.s idx) (Idx.w idx)
  | Tile.Ground => idx 

def loopAux 
  (grid : Grid m n)
  (prev : Idx m n)
  (idx : Idx m n)
  (acc : List (Idx m n))
: ℕ → List (Idx m n)
| 0 => []
| (n + 1) =>
  if idx = grid.start then
    idx :: acc
  else
    loopAux grid idx (grid.next prev idx) (idx :: acc) n

def loop {m n} (grid : Grid m n) : List (Idx m n) :=
  loopAux grid grid.start (Idx.s grid.start) [grid.start] (m * n)

def maxDistance {m n} (grid : Grid m n) : Option ℕ := Id.run <| do
  let mut distance : GridArray m n (WithTop ℕ) := GridArray.ofFn (fun _ _ => ⊤)
  for (d, idx) in grid.loop.enum do
    distance := distance.modify idx (min · (WithTop.some d))
  for (d, idx) in grid.loop.reverse.enum do
    distance := distance.modify idx (min · (WithTop.some d))
  return (distance.values.reduceOption).maximum?

def adj {m n} (grid : Grid m n)
: GridArray (m + 1) (n + 1) (List (Idx (m + 1) (n + 1))) := Id.run <| do
  let loopSet := Lean.HashSet.ofList grid.loop
  let mut adj := GridArray.ofFn (fun (_ : Fin (m + 1)) (_ : Fin (n + 1)) => [])
  for (i, j) in GridArray.indices m n do
    if ¬loopSet.contains (i, j) ∨ grid.get (i, j) ∉ Tile.facingN then do
      adj := adj.modify (i.castSucc, j.castSucc) ((i.castSucc, j.succ) :: ·)
      adj := adj.modify (i.castSucc, j.succ) ((i.castSucc, j.castSucc) :: ·)
    if ¬loopSet.contains (i, j) ∨ grid.get (i, j) ∉ Tile.facingS then do
      adj := adj.modify (i.succ, j.castSucc) ((i.succ, j.succ) :: ·)
      adj := adj.modify (i.succ, j.succ) ((i.succ, j.castSucc) :: ·)
    if ¬loopSet.contains (i, j) ∨ grid.get (i, j) ∉ Tile.facingE then do
      adj := adj.modify (i.castSucc, j.succ) ((i.succ, j.succ) :: ·)
      adj := adj.modify (i.succ, j.succ) ((i.castSucc, j.succ) :: ·)
    if ¬loopSet.contains (i, j) ∨ grid.get (i, j) ∉ Tile.facingW then do
      adj := adj.modify (i.castSucc, j.castSucc) ((i.succ, j.castSucc) :: ·)
      adj := adj.modify (i.succ, j.castSucc) ((i.castSucc, j.castSucc) :: ·)
  return adj

def enclosed {m n} (grid : Grid m n) : ℕ :=
  let adj := grid.adj
  let outer := dfs adj.get (⟨0, m.succ_pos⟩, ⟨0, n.succ_pos⟩)
  ((GridArray.indices m n).filter fun (i, j) =>
    ¬outer.contains (i.castSucc, j.castSucc)
  ∧ ¬outer.contains (i.succ, j.castSucc)
  ∧ ¬outer.contains (i.castSucc, j.succ)
  ∧ ¬outer.contains (i.succ, j.succ)
    ).length

def ofLines (lines : Array String) : Except String ((m : ℕ) × (n : ℕ) × Grid m n) := do
  let lines' := lines.map (List.toArray <| Tile.ofChar <$> String.toList ·)
  let m := lines'.size
  if hm : 0 < m then
    let n := lines'[0].size
    if hn : ∀ {i} (hi : i < m), lines'[i].size = n then
      let grid : GridArray m n Tile := {
        array := lines'
        h₁ := rfl
        h₂ := hn
      }
      if let (start :: _) :=
        (GridArray.indices m n).filter fun idx =>
          (lines.get? idx.fst).all fun s =>
            (s.get? ⟨idx.snd⟩).all (· = 'S') 
      then
        return ⟨m, n, {
          grid
          start
        }⟩
      else
        Except.error "cannot make Grid without S"
    else 
      Except.error "cannot make Grid of uneven lines"
  else 
    Except.error "cannot make Grid of empty array"

end Grid

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test1.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 1: {grid.maxDistance}"
  println! "Expected: {some 4}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test2.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 2: {grid.maxDistance}"
  println! "Expected: {some 8}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Task: {grid.maxDistance}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test1.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 1: {grid.enclosed}"
  println! "Expected: {some 1}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test2.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 2: {grid.enclosed}"
  println! "Expected: {some 1}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test3.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 3: {grid.enclosed}"
  println! "Expected: {some 4}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test4.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 4: {grid.enclosed}"
  println! "Expected: {some 4}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test5.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Test 5: {grid.enclosed}"
  println! "Expected: {some 8}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (Grid.ofLines lines)
  println! "Task: {grid.enclosed}"
--  println! "Task: [disabled for time, solution was 413]"

end Task2

def main : IO Unit := do
  println! "Day 10"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day10
