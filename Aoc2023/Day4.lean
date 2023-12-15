import Lean.Data.Json.Parser
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.BigOperators.Basic

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

def main : IO Unit := do
  println! "Day 4"
  println! "Task 1"
  Task1.main
  println! ""

end Day4
