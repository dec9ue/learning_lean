import Mathlib

set_option linter.mathlibStandardSet false

universe u v w

/--
直積的な型 `NewFin A B C`。 `A, B, C` の各元を 1 つずつ取って構成される。
辞書式順序を入れたいので、コンストラクタは 1 つだけ (`mk`)。
-/
inductive NewFin (A : Type u) (B : Type v) (C : Type w) where
  | mk : A → B → C → NewFin A B C
  deriving Repr, DecidableEq

namespace NewFin

variable {A : Type u} {B : Type v} {C : Type w}

/-- `NewFin A B C` から `A × B × C` への変換。 -/
def toProd : NewFin A B C → A × B × C
  | .mk a b c => (a, b, c)

/-- `A × B × C` から `NewFin A B C` への変換。 -/
def ofProd : A × B × C → NewFin A B C
  | (a, b, c) => .mk a b c

@[simp]
theorem ofProd_toProd (x : NewFin A B C) : ofProd (toProd x) = x := by
  cases x; rfl

@[simp]
theorem toProd_ofProd (p : A × B × C) : toProd (ofProd p) = p := by
  rcases p with ⟨a, b, c⟩
  rfl

/-! ## Finset によるすべての要素の集合 -/

section AllSet
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

/-- すべての `NewFin A B C` の要素からなる Finset。
`Finset.biUnion` をモナド生成子風に重ねている
(現在の mathlib では `Finset.bind` の代わりに `Finset.biUnion` が使われる)。 -/
def allSet : Finset (NewFin A B C) :=
  (Finset.univ : Finset A).biUnion fun a =>
    (Finset.univ : Finset B).biUnion fun b =>
      (Finset.univ : Finset C).biUnion fun c =>
        ({NewFin.mk a b c} : Finset (NewFin A B C))

theorem mem_allSet (x : NewFin A B C) :
    x ∈ allSet (A := A) (B := B) (C := C) := by
  cases x with
  | mk a b c =>
      simp only [allSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_singleton,
        true_and]
      exact ⟨a, b, c, rfl⟩

/-- `NewFin A B C` 自身の `Fintype` インスタンス。 -/
instance instFintype : Fintype (NewFin A B C) where
  elems := allSet
  complete := mem_allSet

theorem allSet_eq_univ :
    allSet (A := A) (B := B) (C := C) =
      (Finset.univ : Finset (NewFin A B C)) := by
  ext x
  simp [mem_allSet]

end AllSet

/-! ## LinearOrder

辞書式順序を入れる。`A ×ₗ (B ×ₗ C)` (mathlib の lex 直積) への単射
`toLex'` を作り、`LinearOrder.lift'` で持ち上げる。
-/

section LinearOrderSection
variable [LinearOrder A] [LinearOrder B] [LinearOrder C]

/-- `NewFin A B C` を辞書式直積 `A ×ₗ (B ×ₗ C)` に埋め込む写像。 -/
private def toLex' : NewFin A B C → A ×ₗ (B ×ₗ C)
  | .mk a b c => toLex (a, toLex (b, c))

private theorem toLex'_injective :
    Function.Injective (toLex' : NewFin A B C → A ×ₗ (B ×ₗ C)) := by
  rintro ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ h
  simp only [toLex', toLex_inj, Prod.mk.injEq] at h
  obtain ⟨ha, hb, hc⟩ := h
  subst ha; subst hb; subst hc
  rfl

/-- 辞書式順序による `LinearOrder (NewFin A B C)`。 -/
instance instLinearOrder : LinearOrder (NewFin A B C) :=
  LinearOrder.lift' (toLex' : NewFin A B C → A ×ₗ (B ×ₗ C)) toLex'_injective

end LinearOrderSection

/-! ## ソート済みリスト -/

section AllList
variable [Fintype A] [Fintype B] [Fintype C]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]
variable [LinearOrder A] [LinearOrder B] [LinearOrder C]

/-- `allSet` を辞書式順序でソートした、canonical な list。 -/
noncomputable def allList : List (NewFin A B C) :=
  (allSet (A := A) (B := B) (C := C)).sort (· ≤ ·)

theorem allList_nodup :
    (allList (A := A) (B := B) (C := C)).Nodup := by
  unfold allList
  exact Finset.sort_nodup _ _

theorem allList_all (x : NewFin A B C) :
    x ∈ allList (A := A) (B := B) (C := C) := by
  unfold allList
  rw [Finset.mem_sort]
  exact mem_allSet x

theorem allList_toFinset_eq_univ :
    (allList (A := A) (B := B) (C := C)).toFinset =
      (Finset.univ : Finset (NewFin A B C)) := by
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  rw [List.mem_toFinset]
  exact allList_all x

end AllList

end NewFin
