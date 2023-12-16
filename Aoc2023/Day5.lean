import Lean.Data.Json.Parser
import Mathlib.Data.Set.Intervals.Basic

namespace Day5

inductive MapLabel
| seedToSoil
| soilToFertilizer
| fertilizerToWater
| waterToLight
| lightToTemperature
| temperatureToHumidity
| humidityToLocation
deriving DecidableEq, Hashable 

namespace MapLabel

def univ : List MapLabel := [
  seedToSoil,
  soilToFertilizer,
  fertilizerToWater,
  waterToLight,
  lightToTemperature,
  temperatureToHumidity,
  humidityToLocation
]

instance : ToString MapLabel where
  toString
  | seedToSoil => "seed-to-soil"
  | soilToFertilizer => "soil-to-fertilizer"
  | fertilizerToWater => "fertilizer-to-water"
  | waterToLight => "water-to-light"
  | lightToTemperature => "light-to-temperature"
  | temperatureToHumidity => "temperature-to-humidity"
  | humidityToLocation => "humidity-to-location"

end MapLabel

structure Almanac where
  (seeds : List ℕ)
  (maps : MapLabel → List (ℕ × ℕ × ℕ))

namespace Almanac

open Lean.Parsec

def mapFromRanges (acc : List (ℕ × ℕ × ℕ)) : List ℕ → Option (List (ℕ × ℕ × ℕ))
| [] => some acc
| (a :: b :: n :: t) => mapFromRanges ((a, b, n) :: acc) t
| _ => none 

def parser : Lean.Parsec Almanac := do
  skipString "seeds:"
  let seeds ← many (attempt do -- oh so this is how attempt works 
      ws
      let c ← peek?
      if c.any Char.isDigit then 
        Lean.Json.Parser.natMaybeZero
      else
        fail "not a number")
  let mut maps : MapLabel → List (ℕ × ℕ × ℕ) := Function.const _ []
  for label in MapLabel.univ do
    ws 
    skipString (toString label)
    ws
    skipString "map:"
    let ranges ← many (attempt do -- oh so this is how attempt works 
      ws
      let c ← peek?
      if c.any Char.isDigit then 
        Lean.Json.Parser.natMaybeZero
      else
        fail "not a number")
    if let some map := mapFromRanges [] ranges.data then
      maps := Function.update maps label map
    else
      fail "bad map"
  return { seeds := seeds.data, maps }

def parse (s : String) : Except String Almanac := parser.run s

def get (almanac : Almanac) (label : MapLabel) (i : ℕ) : ℕ :=
  ((almanac.maps label).firstM fun (a, b, n) =>
    if i ∈ Set.Ico b (b + n) then
      some (a + i - b)
    else
      none).getD
    i

def locations (almanac : Almanac) : List ℕ := 
  MapLabel.univ.foldl
    (fun current label => almanac.get label <$> current)
    almanac.seeds

def min_location (almanac : Almanac) : Option ℕ :=
  almanac.locations.minimum?

end Almanac

structure RangeAlmanac where
  (seeds : List (ℕ × ℕ))
  (maps : MapLabel → List (ℕ × ℕ × ℕ))

namespace RangeAlmanac

def pairs (acc : List (ℕ × ℕ)) : List ℕ → Option (List (ℕ × ℕ))
| [] => some acc
| (a :: b :: t) => pairs ((a, b) :: acc) t
| _ => none

def fromAlmanac (almanac : Almanac) : Except String RangeAlmanac :=
match pairs [] almanac.seeds with
| some seeds => Except.ok { seeds, maps := almanac.maps }
| none => Except.error "invalid seeds"

def parse : String → Except String RangeAlmanac :=
  Almanac.parse >=> fromAlmanac

def next (unshifted : List (ℕ × ℕ)) (shifted : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ)
| [] => (unshifted ++ shifted).filter (Prod.snd · > 0)
| ((a, b, n) :: t) =>
  let (unshifted', shifted') := Id.run <| do
    let mut unshifted' : List (ℕ × ℕ) := []
    let mut shifted' := shifted
    for (start, length) in unshifted do
      if start + length ≤ b then do
        unshifted' := (start, length) :: unshifted'
      else if start + length ≤ b + n then do
        if start < b then do
          unshifted' := (start, b - start) :: unshifted'
          shifted' := (a, start + length - b) :: shifted'
        else do
          shifted' := (a + start - b, length) :: shifted'
      else if start < b then do
        unshifted' := (start, b - start) :: unshifted'
        shifted' := (a, n) :: shifted'
        unshifted' := (b + n, start + length - b - n) :: unshifted' 
      else if start < b + n then do
        shifted' := (a + start - b, b + n - start) :: shifted'
        unshifted' := (b + n, start + length - b - n) :: unshifted' 
      else do
        unshifted' := (start, length) :: unshifted'
    return (unshifted', shifted')
  next unshifted' shifted' t

def locationRanges (almanac : RangeAlmanac) : List (ℕ × ℕ) := 
  MapLabel.univ.foldl
    (fun current label => next current [] (almanac.maps label))
    almanac.seeds

def min_location (almanac : RangeAlmanac) : Option ℕ :=
  (Prod.fst <$> almanac.locationRanges.filter (Prod.snd · > 0)).minimum?

end RangeAlmanac

namespace Task1

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day5/test.txt")
  let almanac ← IO.ofExcept (Almanac.parse s)
  println! "Test: {almanac.min_location}"
  println! "Expected: {some 35}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day5/task.txt")
  let almanac ← IO.ofExcept (Almanac.parse s)
  println! "Task: {almanac.min_location}"

end Task1

namespace Task2

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day5/test.txt")
  let almanac ← IO.ofExcept (RangeAlmanac.parse s)
  println! "Test: {almanac.min_location}"
  println! "Expected: {some 46}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day5/task.txt")
  let almanac ← IO.ofExcept (RangeAlmanac.parse s)
  println! "Task: {almanac.min_location}"

end Task2

def main : IO Unit := do
  println! "Day 5"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day5
