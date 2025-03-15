import Lean
import Mathlib.Tactic.Ring

def my_head {α : Type} (xs : List α) (h : xs ≠ []) : α :=
  match xs with
  | [] => absurd rfl h
  | x :: _ => x

def my_tail {α : Type} (xs : List α) (h : xs ≠ []) : List α :=
  match xs with
  | [] => absurd rfl h
  | _ :: tl => tl

theorem length_partition :
  ∀ {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α),
  xs.length = (xs.partition p).1.length + (xs.partition p).2.length := by
    intros α p h xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp [List.partition]
      by_cases hpx : p x
      sorry
      sorry

def my_quick_sort {α : Type} [LT α][DecidableLT α] : List α → List α :=
  λ l => match l with
  | [] => []
  | [x] => [x]
  | pivot :: xs =>
    let p := (fun x => x < pivot)
    let parted := xs.partition p
    let smaller := parted.1
    let larger := parted.2
    have p_decidable : DecidablePred p := by
      infer_instance
    have l_ : l = pivot :: xs := by sorry
    have : l.length = smaller.length + 1 + larger.length := by
      -- rewrite l to pivot :: xs
      rw[l_]
      rw[List.length_cons]
      rw [length_partition p xs]
      dsimp[smaller, larger,parted]
      ring_nf
      congr <;> ext x <;> simp

    my_quick_sort smaller ++ [pivot] ++ my_quick_sort larger
