import Lean.Data.Parsec
import Std.Data.HashMap.Basic
import Mathlib.Logic.Equiv.Fin

namespace Day8

structure Network where 
  (turns : Array Bool)
  (turns_size_pos : 0 < turns.size)
  (nodes : Std.HashMap String (String × String))

namespace Network

instance : ToString Network where
  toString network := s!
    "turns: {network.turns}\nnodes: {network.nodes.toList}"

structure State (network : Network) where
  (i : Fin network.turns.size)
  (node : String)

namespace State

instance {network : Network} : ToString network.State where
  toString state := s! "i: {state.i}\nnode: {state.node}"

instance {network : Network} : Inhabited network.State where
  default := { i := ⟨0, network.turns_size_pos⟩, node := "AAA" }

def next {network : Network} (state : network.State) : network.State where
  i := finRotate _ state.i
  node :=
    let (left, right) := network.nodes.findD state.node ("", "")
    if network.turns[state.i] then right else left

end State

-- ensure termination by hard cap on number of iterations
def stepsAux {network : Network} (state : network.State) (count : ℕ) : ℕ → ℕ
| 0 => 0
| (n + 1) =>
  if state.node = "ZZZ" then
    count
  else
    stepsAux state.next (count + 1) n

-- this works since the number of states is the given bound 
def steps (network : Network) : ℕ :=
  stepsAux (default : network.State) 0 (network.turns.size * network.nodes.size) 

open Lean.Parsec

def parser : Lean.Parsec Network := do
  let turns ← manyChars asciiLetter
  let turns : Array Bool := turns.toList.toArray.map (· = 'R')
  if turns_size_pos : 0 < turns.size then do
    let nodes ← many <| attempt do
      ws
      let a ← manyChars asciiLetter
      ws
      skipString "="
      ws
      skipString "("
      let b ← manyChars asciiLetter
      skipString ","
      ws
      let c ← manyChars asciiLetter
      skipString ")"
      return (a, (b, c))
    return {
      turns
      turns_size_pos
      nodes := Std.HashMap.ofList nodes.toList
    }
  else
    fail "turns was size zero"

end Network

namespace Task1

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day8/test1.txt")
  let network ← IO.ofExcept (Network.parser.run s)
  println! "Test 1: {network.steps}"
  println! "Expected: {2}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day8/test2.txt")
  let network ← IO.ofExcept (Network.parser.run s)
  println! "Test 2: {network.steps}"
  println! "Expected: {6}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day8/task.txt")
  let network ← IO.ofExcept (Network.parser.run s)
  println! "Task: {network.steps}"

end Task1

def main : IO Unit := do
  println! "Day 8"
  println! "Task 1"
  Task1.main
  println! ""

end Day8
