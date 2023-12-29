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
  evaluateAux workflows "in" part workflows.size

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

def main : IO Unit := do
  println! "Day 19"
  println! "Task 1"
  Task1.main
  println! ""

end Day19
