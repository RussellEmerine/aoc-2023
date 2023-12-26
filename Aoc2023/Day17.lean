import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Equiv.Fin
import «Aoc2023».Dijkstra
import «Aoc2023».GridArray 

namespace Day17

inductive Direction
| N
| S
| E
| W
deriving Hashable, DecidableEq, Fintype

namespace Direction

instance : ToString Direction where
  toString
  | N => "N"
  | S => "S"
  | E => "E"
  | W => "W"

end Direction

instance : IsEmpty (Fin2 0) where
  false := Fin2.elim0

-- very funny that this isn't already defined... but not too hard to do myself
def FinEquivFin2 : (n : ℕ) → Fin n ≃ Fin2 n
| 0 => {
    toFun := Fin.elim0
    invFun := Fin2.elim0
    left_inv := fun i => i.elim0
    right_inv := fun i => i.elim0 
  }
| (n + 1) => {
    toFun := Fin.cases Fin2.fz (Fin2.fs ∘ FinEquivFin2 n)
    invFun := fun
    | Fin2.fz => 0
    | (Fin2.fs i) => ((FinEquivFin2 n).symm i).succ
    left_inv := fun i => by
      cases i using Fin.cases
      case zero =>
        rfl
      case succ i =>
        simp
    right_inv := fun
    | Fin2.fz => rfl
    | (Fin2.fs i) => by simp
  }

instance {n} : Fintype (Fin2 n) := Fintype.ofEquiv _ (FinEquivFin2 n)

instance {n} : DecidableEq (Fin2 n) := (FinEquivFin2 n).symm.decidableEq

instance {n} : Hashable (Fin2 n) where
  hash := fun i => Nat.toUInt64 i.toNat

instance {n} : ToString (Fin2 n) where
  toString i := toString i.toNat 

-- i use Fin2 to make pattern matching nicer 
abbrev State m n := Direction × Fin2 3 × Idx m n

def neighbors (grid : GridArray m n ℕ) 
: State m n → List (State m n × ℕ)
| (dir, count, i, j) => 
  let north := if 0 < i.val then some ((finRotate _).symm i, j) else none
  let south := if i.val + 1 < m then some (finRotate _ i, j) else none
  let east := if j.val + 1 < n then some (i, finRotate _ j) else none
  let west := if 0 < j.val then some (i, (finRotate _).symm j) else none
  let (forward, left, right) : Option (State m n) × Option (State m n) × Option (State m n) :=
    match (dir, count) with
    | (Direction.N, Fin2.fz) => (
        none,
        (Direction.W, Fin2.ofNat' 2, ·) <$> west,
        (Direction.E, Fin2.ofNat' 2, ·) <$> east
      )
    | (Direction.N, Fin2.fs c) => (
        (Direction.N, Fin2.left 1 c, ·) <$> north,
        (Direction.W, Fin2.ofNat' 2, ·) <$> west,
        (Direction.E, Fin2.ofNat' 2, ·) <$> east
      )
    | (Direction.S, Fin2.fz) => (
        none,
        (Direction.E, Fin2.ofNat' 2, ·) <$> east,
        (Direction.W, Fin2.ofNat' 2, ·) <$> west
      )
    | (Direction.S, Fin2.fs c) => (
        (Direction.S, Fin2.left 1 c, ·) <$> south,
        (Direction.E, Fin2.ofNat' 2, ·) <$> east,
        (Direction.W, Fin2.ofNat' 2, ·) <$> west
      )
    | (Direction.E, Fin2.fz) => (
        none,
        (Direction.N, Fin2.ofNat' 2, ·) <$> north,
        (Direction.S, Fin2.ofNat' 2, ·) <$> south 
      )
    | (Direction.E, Fin2.fs c) => (
        (Direction.E, Fin2.left 1 c, ·) <$> east,
        (Direction.N, Fin2.ofNat' 2, ·) <$> north,
        (Direction.S, Fin2.ofNat' 2, ·) <$> south 
      )
    | (Direction.W, Fin2.fz) => (
        none,
        (Direction.S, Fin2.ofNat' 2, ·) <$> south,
        (Direction.N, Fin2.ofNat' 2, ·) <$> north 
      )
    | (Direction.W, Fin2.fs c) => (
        (Direction.W, Fin2.left 1 c, ·) <$> west,
        (Direction.S, Fin2.ofNat' 2, ·) <$> south,
        (Direction.N, Fin2.ofNat' 2, ·) <$> north 
      )
  (fun state@(_, _, idx) => (state, grid.get idx)) <$> [forward, left, right].reduceOption

def heatLoss (grid : GridArray (m + 1) (n + 1) ℕ) : Option ℕ :=
  let dist₁ := dijkstra (neighbors grid) (Direction.E, Fin2.ofNat' 2, 0, 0)
  let dist₂ := dijkstra (neighbors grid) (Direction.S, Fin2.ofNat' 2, 0, 0)
  let dests : List (State (m + 1) (n + 1)) := (·, ·, Fin.last m, Fin.last n)
    <$> [Direction.E, Direction.S]
    <*> [Fin2.ofNat' 0, Fin2.ofNat' 1, Fin2.ofNat' 2]
  let dists : List ℕ := do
    let dist ← [dist₁, dist₂]
    let dest ← dests
    match dist.find? dest with
    | (some d) => return d
    | none => [] 
  dists.minimum? 

def natGridArray (lines : Array String) : Except String ((m : ℕ) × (n : ℕ) × (GridArray (m + 1) (n + 1) ℕ)) := 
  match lines.mapM fun line => line.toList.toArray.mapM fun c => c.toString.toNat? with
  | none => Except.error "cannot convert non-digit characters to ℕ"
  | some lines => GridArray.ofLines' lines 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day17/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (natGridArray lines)
  println! "Test: {heatLoss grid}"
  println! "Expected: {some 102}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day17/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (natGridArray lines)
  println! "Task: {heatLoss grid}"

end Task1

def main : IO Unit := do
  println! "Day 17"
  println! "Task 1"
  Task1.main
  println! ""

end Day17
