import Lean.Data.Json.Parser
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Data.List.Intervals
import Mathlib.Data.Vector.Basic 

namespace Day4

structure Card where
  (id : ℕ)
  (winning : List ℕ)
  (having : List ℕ)

namespace Card

open Lean.Parsec

def parser : Lean.Parsec Card := do
  skipString "Card"
  ws
  let id ← Lean.Json.Parser.natNonZero
  skipString ":"
  let s ← manyChars anyChar 
  if let [left, right] := s.splitOn (sep := "|") then
    let winning := left.splitOn.filterMap String.toNat?
    let having := right.splitOn.filterMap String.toNat?
    return { id, winning, having }
  else
    fail "no separator between lists"

def parse (s : String) : Except String Card := parser.run s 

def common (c : Card) : ℕ :=
  (c.having.bagInter c.winning).length

def score' : ℕ → ℕ
| 0 => 0
| 1 => 1
| (n + 1) => 2 * score' n

def score (c : Card) : ℕ := score' c.common

def iterScore (a : Array Card) : ℕ := Id.run <| do
  let mut count := Vector.replicate a.size 1
  let mut total := 0
  for i in List.finRange a.size do
    let common := a[i].common
    let current := count.get i
    total := total + current 
    for j in List.Ico (i + 1) (i + common + 1) do
      if hj : j < a.size then 
        count := count.set ⟨j, hj⟩ (count.get ⟨j, hj⟩ + current)
  return total 

end Card

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/test.txt")
  let cards ← IO.ofExcept (lines.mapM Card.parse)
  println! "Test: {(Card.score <$> cards.data).sum}"
  println! "Expected: {13}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/task.txt")
  let cards ← IO.ofExcept (lines.mapM Card.parse)
  println! "Task: {(Card.score <$> cards.data).sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/test.txt")
  let cards ← IO.ofExcept (lines.mapM Card.parse)
  println! "Test: {Card.iterScore cards}"
  println! "Expected: {30}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/task.txt")
  let cards ← IO.ofExcept (lines.mapM Card.parse)
  println! "Task: {Card.iterScore cards}"

end Task2

def main : IO Unit := do
  println! "Day 4"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day4
