import Lean.Data.Json.Parser
import Mathlib.Data.List.BigOperators.Basic

namespace Day19

open Lean.Parsec

inductive Cat where
| X
| M
| A
| S

def Cat.parser : Lean.Parsec Cat :=
      (skipString "x" *> pure X)
  <|> (skipString "m" *> pure M)
  <|> (skipString "a" *> pure A)
  <|> (skipString "s" *> pure S)

inductive Rule.Cmp
| LT
| GT

def Rule.Cmp.parser : Lean.Parsec Rule.Cmp :=
  (skipString "<" *> pure LT) <|> (skipString ">" *> pure GT)

structure Rule where
  (cat : Cat)
  (cmp : Rule.Cmp)
  (val : ℕ)

def Rule.parser : Lean.Parsec Rule := do
  let cat ← Cat.parser
  let cmp ← Cmp.parser
  let val ← Lean.Json.Parser.natMaybeZero
  return { cat, cmp, val }

structure Part where
  (x : ℕ)
  (m : ℕ)
  (a : ℕ)
  (s : ℕ)

namespace Part

def cat (part : Part) : Cat → ℕ
| Cat.X => part.x
| Cat.M => part.m
| Cat.A => part.a
| Cat.S => part.s

def cond (part : Part) (rule : Rule) : Bool :=
  match rule.cmp with
  | Rule.Cmp.LT => part.cat rule.cat < rule.val
  | Rule.Cmp.GT => part.cat rule.cat > rule.val

def sum (part : Part) : ℕ :=
  part.x + part.m + part.a + part.s

def parser : Lean.Parsec Part := do
  skipString "{x="
  let x ← Lean.Json.Parser.natMaybeZero
  skipString ",m="
  let m ← Lean.Json.Parser.natMaybeZero
  skipString ",a="
  let a ← Lean.Json.Parser.natMaybeZero
  skipString ",s="
  let s ← Lean.Json.Parser.natMaybeZero
  skipString "}"
  return { x, m, a, s }

end Part

structure Range where
  (start : ℕ) -- inclusive
  (stop : ℕ) -- exclusive 
  (h : start < stop) -- nonempty 

namespace Range

instance : Inhabited Range where
  default := { start := 1, stop := 4001, h := by simp }

def length (range : Range) : ℕ :=
  range.stop - range.start 

def cond (range : Range) (val : ℕ) : Rule.Cmp → Option Range × Option Range
| Rule.Cmp.LT =>
  if h₁ : val ≤ range.start then
    (none, some range)
  else if h₂ : val < range.stop then (
    some { start := range.start, stop := val, h := lt_of_not_le h₁ },
    some { start := val, stop := range.stop, h := h₂ }
  ) else
    (some range, none)
| Rule.Cmp.GT =>
  if h₁ : val + 1 ≤ range.start then
    (some range, none)
  else if h₂ : val + 1 < range.stop then (
    some { start := val + 1, stop := range.stop, h := h₂ },
    some { start := range.start, stop := val + 1, h := lt_of_not_le h₁ } 
  ) else
    (none, some range)  

end Range

structure PartRange where
  (x : Range)
  (m : Range)
  (a : Range)
  (s : Range)
deriving Inhabited

namespace PartRange

def cat (pr : PartRange) : Cat → Range
| Cat.X => pr.x
| Cat.M => pr.m
| Cat.A => pr.a
| Cat.S => pr.s

def cond (pr : PartRange) (rule : Rule) : Option PartRange × Option PartRange :=
  let range := pr.cat rule.cat
  let (yes, no) := range.cond rule.val rule.cmp
  let build : Range → PartRange := fun range =>
    match rule.cat with
    | Cat.X => { x := range, m := pr.m, a := pr.a, s := pr.s }
    | Cat.M => { x := pr.x, m := range, a := pr.a, s := pr.s }
    | Cat.A => { x := pr.x, m := pr.m, a := range, s := pr.s }
    | Cat.S => { x := pr.x, m := pr.m, a := pr.a, s := range }
  (build <$> yes, build <$> no)

def count (pr : PartRange) : ℕ :=
  pr.x.length * pr.m.length * pr.a.length * pr.s.length

end PartRange

inductive Workflow.Result where 
| Send : String → Workflow.Result
| Accept : Workflow.Result
| Reject : Workflow.Result

def Workflow.Result.parser : Lean.Parsec Workflow.Result := do
  let s ← manyChars asciiLetter
  return match s with
  | "A" => Accept
  | "R" => Reject
  | _ => Send s 

inductive Workflow where 
| Last : Workflow.Result → Workflow
| Cond : Rule → Workflow.Result → Workflow → Workflow

namespace Workflow

def run (part : Part) : Workflow → Result
| (Last res) => res
| (Cond cond res rule) => if part.cond cond then res else rule.run part 

def evaluateAux (workflows : Std.HashMap String Workflow) (current : String) (part : Part) : ℕ → Bool
| 0 => false
| (n + 1) =>
  match workflows[current] with
  | none => false
  | some workflow =>
    match workflow.run part with
    | Result.Send next => evaluateAux workflows next part n 
    | Result.Accept => true
    | Result.Reject => false 

def evaluate (workflows : Std.HashMap String Workflow) (part : Part) : Bool :=
  evaluateAux workflows "in" part (workflows.size + 2)

mutual -- fun interesting termination predicate
  def evaluateRanges₁ (workflows : Std.HashMap String Workflow) (pr : PartRange) (fuel : ℕ) : Workflow → ℕ
  | Last res =>
    have : 1 < 1 + sizeOf res + 1 :=
      Nat.lt_add_of_pos_left (by simp)
    evaluateRanges₂ workflows pr fuel res 
  | Cond cond res workflow =>
    let (yes, no) := pr.cond cond
    have : 1 < 1 + sizeOf cond + sizeOf res + sizeOf workflow + 1 :=
      Nat.lt_add_of_pos_left (by simp)
    let yesCount := (evaluateRanges₂ workflows · fuel res) <$> yes
    have : sizeOf workflow < 1 + sizeOf cond + sizeOf res + sizeOf workflow :=
      Nat.lt_add_of_pos_left (by simp)
    let noCount := (evaluateRanges₁ workflows · fuel workflow) <$> no 
    yesCount.getD 0 + noCount.getD 0 

  def evaluateRanges₂ (workflows : Std.HashMap String Workflow) (pr : PartRange) (fuel : ℕ) : Result → ℕ
  | Result.Accept => pr.count
  | Result.Reject => 0
  | Result.Send next => evaluateRanges₃ workflows next pr fuel 

  def evaluateRanges₃ (workflows : Std.HashMap String Workflow) (current : String) (pr : PartRange) : ℕ → ℕ 
  | 0 => 0
  | (n + 1) =>
    match workflows[current] with
    | none => 0
    | some workflow =>
      evaluateRanges₁ workflows pr n workflow 
end

termination_by
  evaluateRanges₁ _ _ fuel wf => (sizeOf fuel, sizeOf wf + 1)
  evaluateRanges₂ _ _ fuel _ => (sizeOf fuel, 1)
  evaluateRanges₃ _ _ _ fuel => (sizeOf fuel, 0)

def evaluateRanges (workflows : Std.HashMap String Workflow) : ℕ :=
  evaluateRanges₃ workflows "in" default (workflows.size + 2)

def parser : Lean.Parsec Workflow := do
  skipString "{"
  let conds ← many <| attempt do
    let rule ← Rule.parser
    skipString ":"
    let res ← Result.parser
    skipString ","
    return (rule, res) 
  let last ← Result.parser
  return conds.foldr Cond.uncurry (Last last)

def namedParser : Lean.Parsec (String × Workflow) := do
  let name ← manyChars asciiLetter
  let workflow ← parser
  return (name, workflow)

end Workflow

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/test.txt")
  if let [wfs, pts] := lines.toList.splitOn "" then
    let workflows := Std.HashMap.ofList (← IO.ofExcept (wfs.mapM Workflow.namedParser.run))
    let parts ← IO.ofExcept (pts.mapM Part.parser.run)
    println! "Test: {(Part.sum <$> parts.filter (Workflow.evaluate workflows)).sum}"
    println! "Expected: {19114}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/task.txt")
  if let [wfs, pts] := lines.toList.splitOn "" then
    let workflows := Std.HashMap.ofList (← IO.ofExcept (wfs.mapM Workflow.namedParser.run))
    let parts ← IO.ofExcept (pts.mapM Part.parser.run)
    println! "Task: {(Part.sum <$> parts.filter (Workflow.evaluate workflows)).sum}"

end Task1

namespace Task2 

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/test.txt")
  if let [wfs, _] := lines.toList.splitOn "" then
    let workflows := Std.HashMap.ofList (← IO.ofExcept (wfs.mapM Workflow.namedParser.run))
    println! "Test: {Workflow.evaluateRanges workflows}"
    println! "Expected: {167409079868000}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/task.txt")
  if let [wfs, _] := lines.toList.splitOn "" then
    let workflows := Std.HashMap.ofList (← IO.ofExcept (wfs.mapM Workflow.namedParser.run))
    println! "Task: {Workflow.evaluateRanges workflows}"

end Task2

def main : IO Unit := do
  println! "Day 19"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day19
