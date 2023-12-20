import Lean.Data.Json.Parser
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.List.BigOperators.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Nat.Digits

namespace Day6

/-
range from start to start + length, inclusive-exclusive
p must be monotone decreasing on the range
finds the last member of p 
-/
def binSearchAux (p : Set ℕ) [DecidablePred (fun m => m ∈ p)] (start : ℕ) (length : ℕ) : ℕ :=
  if h : length ≤ 1 then
    start 
  else
    let m := start + length / 2
    if m ∈ p then
      have : length - length / 2 < length :=
        Nat.sub_lt (by linarith) (Nat.div_pos (by linarith) (by linarith))
      binSearchAux p m (length - length / 2)
    else
      have : length / 2 < length :=
        Nat.div_lt_self (by linarith) (by linarith)
      binSearchAux p start (length / 2)

def binSearch (p : Set ℕ) [DecidablePred (fun m => m ∈ p)] (start : ℕ) (stop : ℕ) : ℕ :=
  binSearchAux p start (stop - start) 

structure Race where
  (time : ℕ)
  (record : ℕ)

namespace Race

def waysToBeat (race : Race) : ℕ :=
  let m := race.time / 2
  let beat := {i | i * (race.time - i) > race.record}
  let b₁ := binSearch beatᶜ 0 m
  let b₂ := binSearch beat m race.time 
  b₂ - b₁  

end Race

structure Races where
  (races : List Race)

namespace Races

open Lean.Parsec

def parser : Lean.Parsec Races := do
  skipString "Time:"
  let time ← many (attempt do ws; Lean.Json.Parser.natMaybeZero)
  ws
  skipString "Distance:"
  let distance ← many (attempt do ws; Lean.Json.Parser.natMaybeZero)
  return { races := time.data.zipWith Race.mk distance.data }

def waysToBeat (races : Races) : ℕ :=
  (Race.waysToBeat <$> races.races).prod

def join (races : Races) : Race where
  time := Nat.ofDigits 10 <| List.reverse <| Race.time <$> races.races >>= List.reverse ∘ Nat.digits 10
  record := Nat.ofDigits 10 <| List.reverse <| Race.record <$> races.races >>= List.reverse ∘ Nat.digits 10

end Races

namespace Task1

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day6/test.txt")
  let races ← IO.ofExcept (Races.parser.run s)
  println! "Test: {races.waysToBeat}"
  println! "Expected: {288}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day6/task.txt")
  let races ← IO.ofExcept (Races.parser.run s)
  println! "Task: {races.waysToBeat}"

end Task1

namespace Task2

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day6/test.txt")
  let races ← IO.ofExcept (Races.parser.run s)
  println! "Test: {races.join.waysToBeat}"
  println! "Expected: {71503}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day6/task.txt")
  let races ← IO.ofExcept (Races.parser.run s)
  println! "Task: {races.join.waysToBeat}"

end Task2

def main : IO Unit := do
  println! "Day 6"
  println! "Task 1"
  Task1.main 
  println! ""
  println! "Task 2"
  Task2.main 
  println! ""

end Day6
