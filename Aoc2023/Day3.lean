import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Dist

def List.mapD (l : List α) (f : (a : α) → (ha : a ∈ l) → β) : List β :=
match l with
| [] => []
| (h :: t) => (f h (List.Mem.head t) :: t.mapD (fun a ha => f a (List.Mem.tail h ha)))

theorem List.mem_mapD (l : List α) (f : (a : α) → (ha : a ∈ l) → β) (b : β)
: b ∈ l.mapD f ↔ ∃ (a : α) (ha : a ∈ l), f a ha = b := by
  induction l
  case nil =>
    unfold mapD 
    simp
  case cons h t ih =>
    unfold mapD
    simp
    constructor
    case mp =>
      intro h
      cases h
      case inl h =>
        subst h
        exact ⟨h, Or.inl rfl, rfl⟩
      case inr h =>
        rw [ih] at h
        rcases h with ⟨a, ha, hb⟩
        subst hb
        exact ⟨a, Or.inr ha, rfl⟩
    case mpr =>
      intro h
      rcases h with ⟨a, ha, hb⟩
      subst hb
      cases ha
      case inl h =>
        subst h
        exact Or.inl rfl
      case inr h =>
        right
        rw [ih]
        exact ⟨a, h, rfl⟩

namespace Fin 

variable {n : ℕ}

def dist (i j : Fin n) : ℕ := 
  i.val.dist j.val

def dist_comm (i j : Fin n) : i.dist j = j.dist i :=
  Nat.dist_comm i.val j.val

def dist_self (i : Fin n) : i.dist i = 0 :=
  Nat.dist_self i.val

def eq_of_dist_eq_zero {i j : Fin n} (h : i.dist j = 0)
: i = j := by
  ext
  exact Nat.eq_of_dist_eq_zero h

end Fin

namespace Grid

inductive Direction where
| NE
| N
| NW
| W
| SW
| S
| SE
| E

namespace Direction

def univ : List Direction := [NE, N, NW, W, SW, S, SE, E]

def shift {m n} (p : Fin m × Fin n) : Direction → Option (Fin m × Fin n)
| NE =>
  if h : p.fst.val + 1 < m ∧ p.snd.val + 1 < n then
    some (⟨_, h.left⟩, ⟨_, h.right⟩)
  else none
| N =>
  if h : p.fst.val + 1 < m then
    some (⟨_, h⟩, p.snd)
  else none
| NW =>
  if h : p.fst.val + 1 < m ∧ p.snd.val > 0 then
    some (⟨_, h.left⟩, ⟨p.snd.val - 1, (p.snd.val.sub_le 1).trans_lt p.snd.is_lt⟩)
  else none
| W =>
  if p.snd.val > 0 then
    some (p.fst, ⟨p.snd.val - 1, (p.snd.val.sub_le 1).trans_lt p.snd.is_lt⟩)
  else none
| SW =>
  if p.fst.val > 0 ∧ p.snd.val > 0 then
    some
      (⟨p.fst.val - 1, (p.fst.val.sub_le 1).trans_lt p.fst.is_lt⟩,
       ⟨p.snd.val - 1, (p.snd.val.sub_le 1).trans_lt p.snd.is_lt⟩)
  else none
| S =>
  if p.fst.val > 0 then
    some (⟨p.fst.val - 1, (p.fst.val.sub_le 1).trans_lt p.fst.is_lt⟩, p.snd)
  else none
| SE =>
  if h : p.fst.val > 0 ∧ p.snd.val + 1 < n then
    some (⟨p.fst.val - 1, (p.fst.val.sub_le 1).trans_lt p.fst.is_lt⟩, ⟨_, h.right⟩)
  else none
| E =>
  if h : p.snd.val + 1 < n then
    some (p.fst, ⟨_, h⟩)
  else none 

end Direction

def neighbors {m n} (p : Fin m × Fin n) : List (Fin m × Fin n) :=
  Direction.univ.filterMap (Direction.shift p)

end Grid

namespace Day3

inductive Tile
| Period : Tile
| Symbol : Tile
| Digit : Fin 10 → Tile
deriving DecidableEq 

namespace Tile

def toChar : Tile → Char 
| Period => '.'
| Symbol => '*'
| (Digit d) => d.val.digitChar

def fromChar : Char → Tile
| '.' => Period
| '0' => Digit 0
| '1' => Digit 1
| '2' => Digit 2
| '3' => Digit 3
| '4' => Digit 4
| '5' => Digit 5
| '6' => Digit 6
| '7' => Digit 7
| '8' => Digit 8
| '9' => Digit 9 
| _ => Symbol 

instance : ToString Tile where
  toString t := t.toChar.toString

def isDigit : Tile → Bool
| Period => false 
| Symbol => false
| (Digit _) => true

def toDigit (t : Tile) (ht : t.isDigit) : Fin 10 := 
match t with
| Period => False.elim (by cases ht)
| Symbol => False.elim (by cases ht)
| (Digit d) => d

end Tile

abbrev Schematic (m n : ℕ) := Matrix (Fin m) (Fin n) Tile

namespace Schematic

-- undocumented: technically never allowed to be empty

def fromLines (lines : Array String) : Option (Σ m n, Schematic m n) :=
  if h₁ : lines.isEmpty then
    none
  else
    let n := (lines.get ⟨0, by
      rw [Array.isEmpty, decide_eq_true_eq, ← Ne.def] at h₁
      exact Nat.pos_of_ne_zero h₁⟩).length
    if lines.data.all (fun line => line.length == n) then
      some ⟨lines.size, n, Matrix.of (fun i j => Tile.fromChar ((lines.get i).get (String.Pos.mk j)))⟩
    else
      none 

structure Subrow {m n} (schematic : Schematic m n) (row : Fin m) where
  (start : ℕ)
  (length : ℕ)
  (start_add_length_le : start + length ≤ n)

namespace Subrow

variable {m n : ℕ} {schematic : Schematic m n} {row : Fin m}

theorem start_le (subrow : Subrow schematic row)
: subrow.start ≤ n := (subrow.start.le_add_right subrow.length).trans subrow.start_add_length_le 

def indices (subrow : Subrow schematic row) : List (Fin n) :=
  (fun (i : Fin subrow.length) =>
    ⟨subrow.start + i,
      (add_lt_add_left i.is_lt subrow.start).trans_le
        subrow.start_add_length_le⟩)
    <$> List.finRange subrow.length

def tiles (subrow : Subrow schematic row) : List Tile :=
  subrow.indices.map (fun j => schematic row j)

structure Number {m n} (schematic : Schematic m n) (row : Fin m) where
  (subrow : Subrow schematic row) -- maybe this could be extends instead 
  (isDigit : ∀ i ∈ subrow.indices, (schematic row i).isDigit)

namespace Number

def digits (number : Number schematic row) : List (Fin 10) :=
  number.subrow.tiles.mapD fun t ht => t.toDigit (by
    unfold Subrow.tiles at ht
    rw [List.mem_map] at ht
    rcases ht with ⟨j, hj, ht⟩
    subst ht
    exact number.isDigit j hj)

def val (number : Number schematic row) : ℕ :=
  number.digits.foldl (fun n d => n * 10 + d) 0

end Number

def numbersAux 
  (i : ℕ)
  (current : Number schematic row)
  (hi : current.subrow.start = i)
  (acc : List (Number schematic row)) :=
match i with
| 0 => current :: acc
| (j + 1) =>
  have hj : j < n := by
    rw [← Nat.add_one_le_iff, ← hi]
    exact current.subrow.start_le
  if h : (schematic row ⟨j, hj⟩).isDigit then
    numbersAux j {
      subrow := {
        start := j
        length := current.subrow.length + 1
        start_add_length_le := by linarith [current.subrow.start_add_length_le]
      }
      isDigit := by
        intro t ht
        unfold Subrow.indices at ht
        simp at ht
        rcases ht with ⟨k, hk⟩
        subst hk
        cases k using Fin.cases
        case zero =>
          simpa
        case succ k =>
          simp [add_comm k.val 1, ← add_assoc, ← hi]
          apply current.isDigit
          unfold Subrow.indices
          simp
    } rfl acc
  else
    numbersAux j {
      subrow := {
        start := j
        length := 0
        start_add_length_le := by
          rw [add_zero]
          exact le_of_lt hj
      }
      isDigit := by
        intro t ht
        unfold Subrow.indices at ht
        simp at ht
    } rfl (current :: acc)

def numbers (row : Fin m) : List (Number schematic row) :=
  numbersAux n {
    subrow := {
      start := n
      length := 0
      start_add_length_le := le_rfl
    }
    isDigit := by
      intro i hi
      unfold indices at hi 
      simp at hi 
  } rfl []

end Subrow

structure Number {m n} (schematic : Schematic m n) where
  (row : Fin m)
  (number : Subrow.Number schematic row)

def numbers {m n} (schematic : Schematic m n) : List (Number schematic) :=
  List.finRange m >>= fun row => Number.mk row <$> Subrow.numbers row

def sum {m n} (schematic : Schematic m n) : ℕ :=
  ((fun number => number.number.val)
    <$> schematic.numbers.filter fun number =>
      number.number.subrow.indices.any fun t =>
        (Grid.neighbors (number.row, t)).any fun p =>
          schematic p.fst p.snd = Tile.Symbol).sum

end Schematic

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day3/test.txt")
  if let some ⟨_, _, schematic⟩ := Schematic.fromLines lines then
    println! "Test: {schematic.sum}"
    println! "Expected: {4361}"
  else
    throw (IO.userError "bad schematic file")
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day3/task.txt")
  if let some ⟨_, _, schematic⟩ := Schematic.fromLines lines then
    println! "Task: {schematic.sum}"
  else
    throw (IO.userError "bad schematic file")

end Task1

def main : IO Unit := do
  println! "Day 3"
  println! "Task 1"
  Task1.main
  println! ""

end Day3
