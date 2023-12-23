import Mathlib.Data.Vector.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith.Frontend

namespace Day12

structure Record where
  (damaged : Array (Option Bool)) -- (some true) is known damaged
  (groups : List ℕ)

namespace Record

instance : ToString Record where
  toString record :=
    String.mk ((fun
      | some true => '#'
      | some false => '.'
      | none => '?')
      <$> record.damaged.toList)
    ++ " " ++
    ",".intercalate (toString <$> record.groups)

def length (record : Record) : ℕ := record.damaged.size

def arrangements (record : Record) : ℕ := Id.run <| do
  let mut dp := Vector.replicate (record.length + 1) 0
  dp := dp.set 0 1
  for i in List.finRange record.length do
    if record.damaged[i].all not then
      dp := dp.set i.succ (dp.get i)
  for n in record.groups do
    let mut dp' := Vector.replicate (record.length + 1) 0
    for i in List.finRange (record.length + 1) do
      let prior :=
        if i > 0 ∧ record.damaged[i]?.all (·.all not) then
          dp'.get (i - 1)
        else
          0
      let boost :=
        if h₁ : n ≤ i
            ∧ (record.damaged.toSubarray (i - n) i).all (·.all id)
            ∧ record.damaged[i]?.all (·.all not)
            ∧ (n = i ∨ record.damaged[i - n - 1]?.all (·.all not))
        then
          if h₂ : n = i then dp[0] else dp[i - n - 1]
        else
          0
      dp' := dp'.set i (prior + boost)
    dp := dp'
  return dp.last 

def unfold (record : Record) : Record where
  damaged :=
    let d := record.damaged
    let n := #[none]
    #[d, n, d, n, d, n, d, n, d].join
  groups :=
    let g := record.groups 
    [g, g, g, g, g].join

open Lean.Parsec

def parser : Lean.Parsec Record := do
  let s ← manyChars (pchar '#' <|> pchar '.' <|> pchar '?')
  ws
  let t ← manyChars anyChar
  return {
    damaged := ((fun | '#' => some true | '.' => some false | _ => none) <$> s.toList).toArray
    groups := (t.splitOn ",").filterMap String.toNat? 
  }

end Record

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/test.txt")
  let records ← IO.ofExcept (lines.mapM Record.parser.run)
  println! "Test: {(records.map Record.arrangements).toList.sum}"
  println! "Expected: {21}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/task.txt")
  let records ← IO.ofExcept (lines.mapM Record.parser.run)
  println! "Task: {(records.map Record.arrangements).toList.sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/test.txt")
  let records ← IO.ofExcept (lines.mapM Record.parser.run)
  println! "Test: {(records.map (·.unfold.arrangements)).toList.sum}"
  println! "Expected: {525152}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/task.txt")
  let records ← IO.ofExcept (lines.mapM Record.parser.run)
  println! "Task: {(records.map (·.unfold.arrangements)).toList.sum}"

end Task2

def main : IO Unit := do
  println! "Day 12"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day12
