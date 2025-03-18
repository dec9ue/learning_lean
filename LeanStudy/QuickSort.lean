import Lean
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Basic

def my_partition {α : Type} (p : α → Bool) (as : List α) : List α × List α :=
  loop p as ([], [])
where
  @[specialize] loop (p : α → Bool): List α → List α × List α → List α × List α
  | [],    (bs, cs) => (bs.reverse, cs.reverse)
  | a::as, (bs, cs) =>
    match p a with
    | true  => loop p as (a::bs, cs)
    | false => loop p as (bs, a::cs)

lemma partition_loop_length {α : Type} (p : α → Bool) (as : List α) (bs cs : List α) :
  (my_partition.loop p as (bs, cs)).1.length + (my_partition.loop p as (bs, cs)).2.length = as.length + bs.length + cs.length := by
  induction as generalizing bs cs with
  | nil =>
    rw [my_partition.loop]
    simp
  | cons a as ih =>
    simp only [my_partition.loop]
    by_cases hpa : p a
    .
      simp only [hpa, decide_true]
      simp only [ih]
      simp only [List.length_cons]
      ring
    .
      simp only [hpa, decide_false]
      simp only [ih]
      simp only [List.length_cons]
      ring

lemma partition_length {α : Type} (p : α → Bool) (as : List α) :
  (my_partition p as).1.length + (my_partition p as).2.length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [my_partition]
    by_cases hpa : p a
    .
      simp only [my_partition.loop]
      simp only [hpa, decide_true]
      simp only [List.length_cons]
      rw [partition_loop_length]
      simp only [List.length_cons, List.length_nil, zero_add, add_zero]
    .
      simp only [my_partition.loop]
      simp only [hpa, decide_false]
      simp only [List.length_cons]
      rw [partition_loop_length]
      simp only [List.length_cons, List.length_nil, zero_add, add_zero]

theorem filter_length {α : Type} (p : α → Prop) [DecidablePred p] (xs : List α) :
  (xs.filter p).length ≤ xs.length := by
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
          _ ≤ xs.length + 1 := by exact Nat.le_add_right xs.length 1

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
    have list_filter_lemma :
      (List.filter (fun b ↦ decide (b < pivot)) xs).length < xs.length + 1 := by
      calc
        _ ≤ xs.length := by apply filter_length
        _ < xs.length + 1 := by exact lt_add_one xs.length
    have filter_length_lemma (xs : List α):
      (xs.filter p).length ≤ xs.length := by
      apply filter_length
    have : smaller.length < l.length := by
      simp only [parted, larger, smaller]
      simp only [List.partition_eq_filter_filter]
      rw [hl]
      rw [List.length_cons]
      calc
        _ ≤ xs.length := by
          exact?
        _ < xs.length + 1 := by
          exact lt_add_one xs.length
    have : larger.length < l.length := by
      simp only [parted, larger, smaller]
      simp only [List.partition_eq_filter_filter]
      rw [hl]
      rw [List.length_cons]
      calc
        _ ≤ xs.length := by
          exact?
        _ < xs.length + 1 := by
          exact lt_add_one xs.length
    my_quick_sort smaller ++ [pivot] ++ my_quick_sort larger
termination_by x1 => x1.length
