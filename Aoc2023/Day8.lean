import Lean.Data.Parsec
import Mathlib.Data.HashMap
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

def stateCount (network : Network) : ℕ :=
  network.turns.size * network.nodes.size

structure State (network : Network) where
  (i : Fin network.turns.size)
  (node : String)
deriving Hashable, DecidableEq 

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

def starts (network : Network) : List network.State :=
  mk ⟨0, network.turns_size_pos⟩ <$> network.nodes.keys.filter (String.endsWith · "A")

def stops {network : Network} (state : network.State) : Bool :=
  state.node.endsWith "Z"

def loopFromAux {network : Network}
  (state : network.State)
  (start : network.State)
  (acc : List network.State)
: ℕ → List network.State
| 0 => []
| (n + 1) =>
  if state = start then
    acc.reverse
  else
    loopFromAux state.next start (state :: acc) n

-- find the loop from an element known to be in the loop 
def loopFrom {network : Network} (state : network.State)
: List network.State :=
  loopFromAux state.next state [state] network.stateCount

def loopAux {network : Network}
  (state : network.State)
  (set : Lean.HashSet network.State)
: ℕ → Lean.HashSet network.State
| 0 => {}
| (n + 1) =>
  if set.contains state then
    Lean.HashSet.ofList state.loopFrom
  else
    loopAux state.next (set.insert state) n

-- find the eventual ending loop 
def loop {network : Network} (state : network.State)
: Lean.HashSet network.State :=
  loopAux state {} network.stateCount 

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
  stepsAux (default : network.State) 0 network.stateCount

def startLoopsAux {network : Network}
  (states : List network.State)
  (loops : List (Lean.HashSet network.State))
  (count : ℕ)
: ℕ → ℕ × List network.State
| 0 => (0, [])
| (n + 1) =>
  if (loops.zip states).all Lean.HashSet.contains.uncurry then
    (count, states)
  else
    startLoopsAux (State.next <$> states) loops (count + 1) n

def startLoops (network : Network)
: ℕ × List network.State :=
  let starts := State.starts network 
  startLoopsAux starts (State.loop <$> starts) 0 network.stateCount 

-- ensure termination by hard cap on number of iterations
def parallelStepsAux {network : Network} (states : List network.State) (count : ℕ) : ℕ → ℕ
| 0 => 0
| (n + 1) =>
  if states.all State.stops then
    count
  else
    parallelStepsAux (State.next <$> states) (count + 1) n

def walmartChineseRemainderAux (a n b m : ℕ) (_ : m ≤ n) : ℕ × ℕ := Id.run <| do
  for i in List.range m do
    let x := n * i + a
    if x % m = b % m then
      return (x, n.lcm m)
  return (0, 0)

def walmartChineseRemainder (p₁ : ℕ × ℕ) (p₂ : ℕ × ℕ) : ℕ × ℕ :=
  if h : p₁.snd < p₂.snd then
    walmartChineseRemainderAux p₂.fst p₂.snd p₁.fst p₁.snd (le_of_lt h)
  else
    walmartChineseRemainderAux p₁.fst p₁.snd p₂.fst p₂.snd (Nat.ge_of_not_lt h)

def parallelSteps (network : Network) : ℕ := Id.run <| do
  let (n₁, startLoops) := network.startLoops
  let traceSteps := parallelStepsAux (State.starts network) 0 n₁
  if traceSteps > 0 then do
    return traceSteps
  else do
    -- key feature: there are at most 6 starts and at most 6 stops for each start
    -- (verified by regex ctrl-f)
    let coords := 
      (fun list => (Prod.fst ·, list.length)
        <$> list.enum.filter (State.stops ∘ Prod.snd))
      <$> State.loopFrom
      <$> startLoops
    -- learned the f <$> a <*> b idiom from haskell quite a whiles ago
    let results :=
      coords.foldl
        (List.filter (· ≠ (0, 0)) <| walmartChineseRemainder <$> · <*> ·)
        [(0, 1)]
    let n₂ := (Prod.fst <$> results).minimum?.getD 0
    return n₁ + n₂ 

open Lean.Parsec

def parser : Lean.Parsec Network := do
  let turns ← manyChars (asciiLetter <|> digit)
  let turns : Array Bool := turns.toList.toArray.map (· = 'R')
  if turns_size_pos : 0 < turns.size then do
    let nodes ← many <| attempt do
      ws
      let a ← manyChars (asciiLetter <|> digit)
      ws
      skipString "="
      ws
      skipString "("
      let b ← manyChars (asciiLetter <|> digit)
      skipString ","
      ws
      let c ← manyChars (asciiLetter <|> digit)
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

namespace Task2

def main : IO Unit := do
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day8/test3.txt")
  let network ← IO.ofExcept (Network.parser.run s)
  println! "Test: {network.parallelSteps}"
  println! "Expected: {6}"
  let s ← IO.FS.readFile (System.FilePath.mk "Data/Day8/task.txt")
  let network ← IO.ofExcept (Network.parser.run s)
  println! "Task: {network.parallelSteps}"

end Task2

def main : IO Unit := do
  println! "Day 8"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day8
