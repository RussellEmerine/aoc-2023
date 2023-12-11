import Lean.Data.Json.Parser
import Mathlib.Data.List.BigOperators.Basic

namespace Day2

def parseRemaining : Lean.Parsec String := fun it =>
  Lean.Parsec.ParseResult.success it.toEnd it.remainingToString

structure Count where
  R : Nat
  G : Nat
  B : Nat

namespace Count

instance : Zero Count where
  zero := {
    R := 0
    G := 0
    B := 0
  }

instance : Add Count where
  add a b := {
    R := a.R + b.R
    G := a.G + b.G
    B := a.B + b.B
  }

instance : Max Count where
  max a b := {
    R := max a.R b.R
    G := max a.G b.G
    B := max a.B b.B
  }

def isValid (c : Count) : Bool :=
  c.R ≤ 12 && c.G ≤ 13 && c.B ≤ 14

def power (c : Count) : Nat :=
  c.R * c.G * c.B 

open Lean.Parsec

def parseOne : Lean.Parsec Count := do
  let n ← Lean.Json.Parser.natNonZero
  ws
  let c ← peek!
  if c == 'r' then
    skipString "red"
    pure {
      R := n
      G := 0
      B := 0 
    }
  else if c == 'g' then
    skipString "green"
    pure {
      R := 0
      G := n
      B := 0 
    }
  else if c == 'b' then
    skipString "blue"
    pure {
      R := 0
      G := 0
      B := n
    }
  else
    fail "invalid color"

def parser : Lean.Parsec Count := do
  let s ← parseRemaining
  let list : Except String (List Count) :=
    (s.splitOn (sep := ",")).mapM fun s => (do ws; parseOne).run s
  match list with
  | Except.ok counts =>
    pure counts.sum
  | Except.error s =>
    fail s 

end Count

structure Game where
  id : Nat 
  rounds : List Count

namespace Game

def isValid (g : Game) : Bool := 
  g.rounds.all Count.isValid

def minSet (g : Game) : Count :=
  /-
  I'd like to use List.maximum or something here but apparently
  mathlib doesn't have a version that uses the type's bot as the start
  -/
  g.rounds.foldl max 0

open Lean.Parsec

def parser : Lean.Parsec Game := do
  ws
  skipString "Game"
  ws
  let id ← Lean.Json.Parser.natNonZero
  skipString ":"
  let s ← parseRemaining
  let list : Except String (List Count) :=
    (s.splitOn (sep := ";")).mapM fun s => (do ws; Count.parser).run s
  match list with
  | Except.ok rounds => 
    pure {
      id
      rounds
    }
  | Except.error s =>
    fail s

def parse (s : String) : Except String Game := parser.run s

end Game

namespace Task1

def task1 (games : List Game) : Nat :=
  (Game.id <$> List.filter Game.isValid games).sum 

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day2/test.txt")
  let games ← IO.ofExcept (lines.data.mapM Game.parse)
  println! "Test: {task1 games}"
  println! "Expected: {8}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day2/task.txt")
  let games ← IO.ofExcept (lines.data.mapM Game.parse)
  println! "Task: {task1 games}"

end Task1

namespace Task2

def task2 (games : List Game) : Nat :=
  (Count.power <$> Game.minSet <$> games).sum

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day2/test.txt")
  let games ← IO.ofExcept (lines.data.mapM Game.parse)
  println! "Test: {task2 games}"
  println! "Expected: {2286}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day2/task.txt")
  let games ← IO.ofExcept (lines.data.mapM Game.parse)
  println! "Task: {task2 games}"

end Task2 

def main : IO Unit := do
  println! "Day 2"
  println! "Task 1"
  Task1.main
  println! ""
  Task2.main
  println! ""

end Day2
