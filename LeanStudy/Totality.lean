import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.DeriveFintype

inductive Index
| A | B | C
deriving DecidableEq, Inhabited, Fintype, Ord, Repr

/-- Fixed enumeration of the three coordinate axes. -/
def Index.allList : List Index :=
  [Index.A, Index.B, Index.C]

@[simp] lemma Index.mem_allList (index : Index) :
    index ∈ Index.allList := by
  cases index <;> simp [Index.allList]

@[simp] lemma Index.allList_nodup : Index.allList.Nodup := by
  classical
  simp [Index.allList]

/-- Selecting one of the `n` lamps along a fixed line through the cube. -/
structure IndexedValue (n : ℕ) where
  index : Index
  value : Fin n
deriving DecidableEq, Fintype, Ord, Repr

def IndexedValue.allList (n : ℕ) : List (IndexedValue n) := do
  let index <- Index.allList
  let value <- List.finRange n
  pure ⟨index, value⟩

lemma IndexedValue.allList_total (n : ℕ) :
    ∀ value : IndexedValue n, value ∈ IndexedValue.allList n := by
  classical
  intro value
  cases value with
  | mk index val =>
    simp [IndexedValue.allList, List.bind_eq_flatMap, List.mem_flatMap, Index.mem_allList]

lemma IndexedValue.allList_nodup (n : ℕ) :
    (IndexedValue.allList n).Nodup := by
  sorry
