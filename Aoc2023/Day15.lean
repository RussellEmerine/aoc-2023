import Mathlib.Data.ByteArray
import Mathlib.Data.Vector.Basic

namespace Day15

def hash (s : String) : UInt8 := Id.run <| do
  let mut current := 0
  for c in s.toAsciiByteArray do
    current := 17 * (current + c)
  current

structure Operation where
  (label : String)
  (focal : Option ℕ)

namespace Operation

def box (op : Operation) : UInt8 :=
  hash op.label 

open Lean.Parsec

def parser : Lean.Parsec Operation := do
  let label ← manyChars asciiLetter
  let focal ← (do skipString "-"; return none) <|> do
    skipString "="
    let n ← Lean.Json.Parser.natMaybeZero
    return some n
  return { label, focal }

end Operation

structure Lens where
  (label : String)
  (focal : ℕ)

abbrev HashMap := Vector (List Lens) 256

def operate (map : HashMap) (op : Operation) : HashMap :=
  let box := map.get op.box.val
  match (op.focal, box.findIdx? (·.label = op.label)) with
  | (some focal, some i) => map.set op.box.val (box.set i { label := op.label, focal })
  | (some focal, none) => map.set op.box.val (box ++ [{ label := op.label, focal }])
  | (none, some i) => map.set op.box.val (box.removeNth i)
  | (none, none) => map

def operations (ops : List Operation) : HashMap :=
  ops.foldl operate default

def focusingPower (map : HashMap) : ℕ :=
  (map.toList.enum >>= fun (i, box) =>
    box.enum.map fun (j, lens) =>
      (i + 1) * (j + 1) * lens.focal).sum 

namespace Task1

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day15/test.txt")
  let words := s.trim.splitOn ","
  println! "Test: {(UInt8.toNat <$> hash <$> words).sum}"
  println! "Expected: {1320}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day15/task.txt")
  let words := s.trim.splitOn ","
  println! "Task: {(UInt8.toNat <$> hash <$> words).sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day15/test.txt")
  let ops ← IO.ofExcept ((s.trim.splitOn ",").mapM Operation.parser.run)
  println! "Test: {focusingPower (operations ops)}"
  println! "Expected: {145}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day15/task.txt")
  let ops ← IO.ofExcept ((s.trim.splitOn ",").mapM Operation.parser.run)
  println! "Task: {focusingPower (operations ops)}"

end Task2

def main : IO Unit := do
  println! "Day 15"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day15
