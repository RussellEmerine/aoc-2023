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

def main : IO Unit := do
  println! "Day 5"
  println! "Task 1"
  Task1.main
  println! ""

end Day5
