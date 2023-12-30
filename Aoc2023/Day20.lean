import Mathlib.Data.HashMap
import Mathlib.Init.Data.List.Instances
import Init.Data.Queue

namespace Day20

open Lean.Parsec 

abbrev Pulse := Bool

abbrev Pulse.low := false
abbrev Pulse.high := true
attribute [match_pattern] Pulse.low Pulse.high 

-- (from, to, pulse)
abbrev Signal := String × String × Pulse 

inductive Module.State
| FlipFlop : Bool → Module.State
| Conj : Std.HashMap String Bool → Module.State
| Broadcast : Module.State

namespace Module.State

def run : Module.State → Signal → Module.State × Option Pulse
| FlipFlop b, (_, _, Pulse.low)  => (FlipFlop (not b), some (not b))
| FlipFlop b, (_, _, Pulse.high) => (FlipFlop b, none)
| Conj map,   (name, _, pulse)   =>
    let map' := map.insert name pulse
    (Conj map', some (not (map'.values.all id)))
| Broadcast,  (_, _, pulse)      => (Broadcast, some pulse)

def parser : Lean.Parsec (String × Module.State) := (do 
  skipString "broadcaster"
  return ("broadcaster", Broadcast)
) <|> (do
  skipString "%"
  let name ← manyChars asciiLetter
  return (name, FlipFlop false)
) <|> (do
  skipString "&"
  let name ← manyChars asciiLetter
  return (name, Conj {})
)

end Module.State

structure Module where
  (name : String) 
  (state : Module.State)
  (out : List String)

namespace Module

def run (mod : Module) (sig : Signal) : Module × List Signal :=
  let (state', pulse) := mod.state.run sig
  ({ name := mod.name, state := state', out := mod.out }, do
    let pulse ← pulse.toList -- (it's probably more efficient to put this first)
    let target ← mod.out
    return (mod.name, target, pulse))

def parser : Lean.Parsec Module := do
  let (name, state) ← State.parser
  ws
  skipString "->"
  ws
  let head ← manyChars asciiLetter
  let tail ← many <| do
    skipString ","
    ws
    let name ← manyChars asciiLetter
    return name
  return { name, state, out := head :: tail.toList }

end Module

abbrev System := Std.HashMap String Module

namespace System

def countPulses (sys' : System) : System × ℕ × ℕ := Id.run <| do
  let mut sys := sys'
  let mut q := Std.Queue.empty.enqueue ("button", "broadcaster", Pulse.low)
  let mut (lo, hi) := (0, 0)
  for _ in [0 : sys'.size * sys'.size * sys'.size] do
    match q.dequeue? with
    | none => return (sys, lo, hi)
    | some (sig@(_, to, pulse), q') => 
      q := q'
      if pulse then
        hi := hi + 1
      else
        lo := lo + 1
      if let some mod := sys[to] then 
        let (mod', out) := mod.run sig
        sys := sys.insert to mod'
        for sig in out do
          q := q.enqueue sig
  return ({}, 0, 0)

def pulseProduct (sys' : System) : ℕ := Id.run <| do
  let mut (sys, lo, hi) := (sys', 0, 0)
  for _ in [0 : 1000] do 
    let (sys', dlo, dhi) := sys.countPulses
    sys := sys'
    lo := lo + dlo
    hi := hi + dhi
  return lo * hi

def ofLines (lines : Array String) : Except String System := do
  let map' ← lines.mapM Module.parser.run
  let mut map := Std.HashMap.ofList ((fun module => (module.name, module)) <$> map'.toList)
  -- this is great and all, but the Conj modules do not know their input nodes yet
  for mod in map.values do
    let fr := mod.name
    for to in mod.out do
      if let some mod := map[to] then
        -- let the Conj module know its input
        let (mod', _) := mod.run (fr, to, Pulse.low)
        -- but also flip the FlipFlop back to its original state 
        let (mod'', _) := mod'.run (fr, to, Pulse.low)
        map := map.insert to mod''
  return map  

end System

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/test1.txt")
  let sys ← IO.ofExcept (System.ofLines lines) -- oooooh that's weird
  println! "Test 1: {sys.pulseProduct}"
  println! "Expected: {32000000}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/test2.txt")
  let sys ← IO.ofExcept (System.ofLines lines) -- but whatever
  println! "Test 2: {sys.pulseProduct}"
  println! "Expected: {11687500}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/task.txt")
  let sys ← IO.ofExcept (System.ofLines lines)
  println! "Task: {sys.pulseProduct}"

end Task1

def main : IO Unit := do
  println! "Day 20"
  println! "Task 1"
  Task1.main
  println! ""

end Day20
