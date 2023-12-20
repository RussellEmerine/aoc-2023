import Lean.Data.Json.Parser
import Mathlib.Data.Set.Basic
import Mathlib.Data.Vector
import Mathlib.Util.Superscript -- for Char Hashable instance 
import Mathlib.Data.HashMap
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Basic
import Mathlib.Data.BinaryHeap

namespace Day7

def cards : Finset Char := {'2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A'}

structure Card where
  (char : cards)
deriving DecidableEq, Hashable 

namespace Card

def Two : Card where
  char := ⟨'2', by simp [cards]⟩
def Three : Card where
  char := ⟨'3', by simp [cards]⟩
def Four : Card where
  char := ⟨'4', by simp [cards]⟩
def Five : Card where
  char := ⟨'5', by simp [cards]⟩
def Six : Card where
  char := ⟨'6', by simp [cards]⟩
def Seven : Card where
  char := ⟨'7', by simp [cards]⟩
def Eight : Card where
  char := ⟨'8', by simp [cards]⟩
def Nine : Card where
  char := ⟨'9', by simp [cards]⟩
def Ten : Card where
  char := ⟨'T', by simp [cards]⟩
def Jack : Card where
  char := ⟨'J', by simp [cards]⟩
def Queen : Card where
  char := ⟨'Q', by simp [cards]⟩
def King : Card where
  char := ⟨'K', by simp [cards]⟩
def Ace : Card where
  char := ⟨'A', by simp [cards]⟩

def univ : List Card :=
  [Two, Three, Four, Five, Six, Seven, Eight, Nine, Ten, Jack, Queen, King, Ace]

def val : Card → ℕ
| (mk (Subtype.mk '2' _)) => 2
| (mk (Subtype.mk '3' _)) => 3
| (mk (Subtype.mk '4' _)) => 4
| (mk (Subtype.mk '5' _)) => 5
| (mk (Subtype.mk '6' _)) => 6
| (mk (Subtype.mk '7' _)) => 7
| (mk (Subtype.mk '8' _)) => 8
| (mk (Subtype.mk '9' _)) => 9
| (mk (Subtype.mk 'T' _)) => 10
| (mk (Subtype.mk 'J' _)) => 11
| (mk (Subtype.mk 'Q' _)) => 12
| (mk (Subtype.mk 'K' _)) => 13
| (mk (Subtype.mk 'A' _)) => 14
| (mk (Subtype.mk _ _)) => 0

theorem val_inj : val.Injective := by
  intro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩ h
  simp [cards] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    <;> rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl 
    <;> cases h
    <;> rfl

instance : LinearOrder Card := LinearOrder.lift' val val_inj

open Lean.Parsec 

def parser : Lean.Parsec Card := do
  let c ← anyChar
  if h : c ∈ cards then do 
    return mk ⟨c, h⟩
  else
    fail "Invalid Character"

end Card

structure Hand where 
  (cards : Vector Card 5)

namespace Hand

inductive Typ
| HighCard
| OnePair
| TwoPair
| ThreeKind
| FullHouse
| FourKind
| FiveKind
deriving DecidableEq

namespace Typ

def val : Typ → ℕ
| HighCard => 0
| OnePair => 1
| TwoPair => 2
| ThreeKind => 3
| FullHouse => 4
| FourKind => 5
| FiveKind => 6

theorem val_inj : val.Injective := by
  intro a b h
  cases a <;> cases b <;> cases h <;> rfl

instance : LinearOrder Typ := LinearOrder.lift' val val_inj 

end Typ

def typ (hand : Hand) : Typ := Id.run <| do
  let mut count := Std.HashMap.ofList ((·, 0) <$> Card.univ)
  for card in hand.cards.toList do
    count := count.modify card (fun _ c => c + 1)
  let mut multiplicity := Std.HashMap.ofList ((·, 0) <$> List.range 6)
  for c in count.values do
    multiplicity := multiplicity.modify c (fun _ c => c + 1)
  if multiplicity[5] = some 1 then
    return Typ.FiveKind
  else if multiplicity[4] = some 1 then
    return Typ.FourKind
  else if multiplicity[3] = some 1 ∧ multiplicity[2] = some 1 then
    return Typ.FullHouse
  else if multiplicity[3] = some 1 then
    return Typ.ThreeKind
  else if multiplicity[2] = some 2 then
    return Typ.TwoPair
  else if multiplicity[2] = some 1 then
    return Typ.OnePair
  else 
    return Typ.HighCard

instance : LinearOrder Hand :=
  LinearOrder.lift'
    (fun hand => toLex (hand.typ, hand.cards.toList)) (by
      intro ⟨a⟩ ⟨b⟩ h
      replace h := congrArg (Prod.snd ∘ ofLex) h
      simp at h
      congr
      exact Vector.eq _ _ h)

open Lean.Parsec

def parser : Lean.Parsec Hand := do
  let a ← Card.parser
  let b ← Card.parser
  let c ← Card.parser
  let d ← Card.parser
  let e ← Card.parser
  return ⟨[a, b, c, d, e], by simp⟩

end Hand

structure Game where
  (hands : Array (Hand × ℕ))

namespace Game

def winnings (game : Game) : ℕ :=
  let sorted := game.hands.heapSort (toLex · < toLex ·)
  ((fun (i, hand) => (i + 1) * hand.snd) <$> sorted.toList.enum).sum 

open Lean.Parsec

def lineParser : Lean.Parsec (Hand × ℕ) := do
  ws
  let hand ← Hand.parser
  ws
  let bid ← Lean.Json.Parser.natMaybeZero
  ws
  return (hand, bid)

def fromArray (array : Array String) : Except String Game :=
  mk <$> Array.mapM lineParser.run array 

end Game

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day7/test.txt")
  let games ← IO.ofExcept (Game.fromArray lines)
  println! "Test: {games.winnings}"
  println! "Expected: {6440}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day7/task.txt")
  let games ← IO.ofExcept (Game.fromArray lines)
  println! "Task: {games.winnings}"

end Task1

def main : IO Unit := do
  println! "Day 7"
  println! "Task 1"
  Task1.main 
  println! ""

end Day7
