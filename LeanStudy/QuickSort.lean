import Lean
import Mathlib.Tactic.Ring

theorem filter_length : ∀ {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α),
  (xs.filter p).length ≤ xs.length := by
    intros α p h xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter, List.length_cons]
      by_cases hpx : p x
      .
        simp only [hpx, decide_true, List.length_cons, add_le_add_iff_right]
        exact ih
      .
        simp only [hpx, decide_false]
        calc
          _ ≤ xs.length := by simp only [ih]
          _ ≤ xs.length + 1 := by apply Nat.le_add_right

def my_quick_sort {α : Type} [LT α][DecidableLT α] : List α → List α :=
  λ l => match hl : l with
  | [] => []
  | [x] => [x]
  | pivot :: xs =>
    let p := (fun x => x < pivot)
    let parted := xs.partition p
    let smaller := parted.1
    let larger := parted.2
    have p_decidable : DecidablePred p := by
      infer_instance
    have : smaller.length < l.length := by
      simp only [parted, larger, smaller]
      simp only [List.partition_eq_filter_filter]
      rw [hl]
      rw [List.length_cons]
      calc
        _ ≤ xs.length := by
          sorry
        _ < xs.length + 1 := by
          exact lt_add_one xs.length
    have : larger.length < l.length := by
      simp only [parted, larger, smaller]
      simp only [List.partition_eq_filter_filter]
      rw [hl]
      rw [List.length_cons]
      calc
        _ ≤ xs.length := by
          sorry
        _ < xs.length + 1 := by
          exact lt_add_one xs.length
    have : (List.filter (fun b ↦ decide (b < pivot)) xs).length < xs.length + 1 := by
      calc
        _ ≤ xs.length := by apply filter_length
        _ < xs.length + 1 := by exact lt_add_one xs.length
    my_quick_sort smaller ++ [pivot] ++ my_quick_sort larger
termination_by x1 => x1.length
