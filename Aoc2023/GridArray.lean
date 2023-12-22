import Mathlib.Data.Matrix.Basic

def Array.modify' (a : Array α) (i : Fin a.size) (f : α → α) : Array α := 
  a.set i (f (a.get i))

theorem Array.size_modify' (a : Array α) (i : Fin a.size) (f : α → α)
: (a.modify' i f).size = a.size := by
  unfold modify'
  rw [Array.size_set]

abbrev Idx m n := Fin m × Fin n

structure GridArray (m n : ℕ) (α) where
  (array : Array (Array α))
  (h₁ : array.size = m)
  (h₂ : ∀ {i} (h : i < array.size), array[i].size = n)

namespace GridArray

def indices (m n : ℕ) : List (Idx m n) :=
  Prod.mk <$> List.finRange m <*> List.finRange n

variable {m n} {α}

def ofMatrix (mat : Matrix (Fin m) (Fin n) α) : GridArray m n α where
  array := Array.ofFn (fun i => Array.ofFn (mat i))
  h₁ := by rw [Array.size_ofFn]
  h₂ := fun h => by rw [Array.getElem_ofFn _ _ h, Array.size_ofFn]

def ofFn (f : Fin m → Fin n → α) : GridArray m n α :=
  ofMatrix (Matrix.of f)

instance [ToString α] : ToString (GridArray m n α) where
  toString grid := toString grid.array 

def get (grid : GridArray m n α) (p : Idx m n) : α :=
  (grid.array.get
    ⟨p.fst, by rw [grid.h₁]; exact p.fst.is_lt⟩).get
      ⟨p.snd, by rw [Array.get_eq_getElem, grid.h₂]; exact p.snd.is_lt⟩

def modify (grid : GridArray m n α) (p : Idx m n) (f : α → α)
: GridArray m n α := {
    array := grid.array.modify' ⟨p.fst, by rw [grid.h₁]; exact p.fst.is_lt⟩ fun row =>
      row.modify p.snd f
    h₁ := by rw [Array.size_modify']; exact grid.h₁
    h₂ := by
      intro i hi
      unfold Array.modify'
      dsimp
      rw [Array.get_set]
      split_ifs
      · rw [Array.size_modify, grid.h₂]
      · apply grid.h₂
      convert hi using 1
      rw [Array.size_modify']
  }

def set (grid : GridArray m n α) (p : Idx m n) (a : α)
: GridArray m n α :=
  grid.modify p (Function.const _ a)

def values (grid : GridArray m n α) : List α :=
  grid.get <$> indices m n 

def transpose (grid : GridArray m n α) : GridArray n m α :=
  ofFn fun j i => grid.get (i, j)

end GridArray
