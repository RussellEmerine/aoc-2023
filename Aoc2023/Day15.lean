import Mathlib.Data.ByteArray

namespace Day15

def hash (s : String) : UInt8 := Id.run <| do
  let mut current := 0
  for c in s.toAsciiByteArray do
    current := 17 * (current + c)
  current

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

def main : IO Unit := do
  println! "Day 15"
  println! "Task 1"
  Task1.main
  println! ""

end Day15
