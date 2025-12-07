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
structure AlgValue (n : ℕ) where
  index : Index
  value : Fin n
deriving DecidableEq, Fintype, Ord, Repr

def AlgValue.allList (n : ℕ) : List (AlgValue n) :=
  (Index.allList ×ˢ List.finRange n).map (fun p : Index × Fin n => ⟨p.1, p.2⟩)

lemma AlgValue.allList_total (n : ℕ) :
    ∀ value : AlgValue n, value ∈ AlgValue.allList n := by
  classical
  intro value
  have hi : value.index ∈ Index.allList := Index.mem_allList value.index
  have hv : value.value ∈ List.finRange n := by
    grind [List.mem_finRange]
  have hpair :
      (value.index, value.value) ∈ Index.allList ×ˢ List.finRange n := by
    grind [List.mem_product]
  have hmap :
      (⟨value.index, value.value⟩ : Index × Fin n)
        ∈ (Index.allList ×ˢ List.finRange n).map
          (fun p : Index × Fin n => ⟨p.1, p.2⟩) := by
    grind only [usr List.contains_iff_exists_mem_beq, = List.contains_eq_mem, = List.mem_map,
      =_ List.contains_iff_mem, = List.contains_map, → List.eq_nil_of_map_eq_nil]
  grind [AlgValue.allList]

lemma AlgValue.allList_nodup (n : ℕ) :
    (AlgValue.allList n).Nodup := by
  classical
  have hprod :
      (Index.allList ×ˢ List.finRange n).Nodup :=
    List.Nodup.product Index.allList_nodup (List.nodup_finRange n)
  have hf : Function.Injective (fun p : Index × Fin n => (⟨p.1, p.2⟩: Index × Fin n) ) := by
    intro p q h
    simp only [Prod.mk.eta] at h
    exact h
  have hmap :
      ((Index.allList ×ˢ List.finRange n).map
          (fun p : Index × Fin n => (⟨p.1, p.2⟩: Index × Fin n))).Nodup := List.Nodup.map hf hprod
  grind [AlgValue.allList]
