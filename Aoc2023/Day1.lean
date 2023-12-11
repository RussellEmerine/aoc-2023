import Std.Data.HashMap.Basic

namespace Day1

namespace Task1

def calibration (s : String) : Option Nat := do
  let l := s.data.filter Char.isDigit
  (String.mk [<- l.head?, <- l.last']).toNat?

def task1 (input : List String) : Option Nat :=
  List.foldr (·+·) 0 <$> List.mapM calibration input

def main : IO Unit := do
  let test <- IO.FS.lines (System.FilePath.mk "Data/Day1/test.txt")
  println! "Test: {task1 test.data}"
  println! "Expected: {some 142}"
  let task <- IO.FS.lines (System.FilePath.mk "Data/Day1/task.txt")
  println! "Task: {task1 task.data}"

end Task1

namespace Task2

def digits : Std.HashMap String Nat :=
  Std.HashMap.ofList [
  ("0", 0),
  ("1", 1),
  ("2", 2),
  ("3", 3),
  ("4", 4),
  ("5", 5),
  ("6", 6),
  ("7", 7),
  ("8", 8),
  ("9", 9),
  ("one", 1),
  ("two", 2),
  ("three", 3),
  ("four", 4),
  ("five", 5),
  ("six", 6),
  ("seven", 7),
  ("eight", 8),
  ("nine", 9),
]

def leftDigit' : List Char → Option Nat
| (h :: t) => 
  let s := String.mk (h :: t)
  digits.fold
    (fun acc pre n => acc <|> if s.startsWith pre then some n else none)
    none
    <|> leftDigit' t
| [] => none

def leftDigit (s : String) : Option Nat :=
  leftDigit' s.data 

def rightDigit' : List Char → Option Nat
| (h :: t) =>
  let s := String.mk (h :: t).reverse
  digits.fold
    (fun acc post n => acc <|> if s.endsWith post then some n else none)
    none
    <|> rightDigit' t
| [] => none

def rightDigit (s : String) : Option Nat :=
  rightDigit' s.data.reverse

def calibration (s : String) : Option Nat := do
  (<- leftDigit s) * 10 + (<- rightDigit s)

def task2 (input : List String) : Option Nat :=
  List.foldr (·+·) 0 <$> List.mapM calibration input

def main : IO Unit := do
  let test <- IO.FS.lines (System.FilePath.mk "Data/Day1/test.txt")
  println! "Test: {task2 test.data}"
  println! "Expected: {some 142}"
  let test <- IO.FS.lines (System.FilePath.mk "Data/Day1/test2.txt")
  println! "Test: {task2 test.data}"
  println! "Expected: {some 281}"
  let task <- IO.FS.lines (System.FilePath.mk "Data/Day1/task.txt")
  println! "Task: {task2 task.data}"

end Task2

def main : IO Unit := do
  println! "Day 1"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day1
