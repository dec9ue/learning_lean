import Lean
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Basic

-- option that non-terminated function can be used


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

lemma decidable_eta_filter {α : Type}{p : α → Prop}{b : List α} (hp : DecidablePred p) :
  List.filter (fun b0 : α => decide (p b0)) b = List.filter p b := by
  induction b with
  | nil =>
    simp only [List.filter, List.length_nil]
  | cons x xs ih =>
    simp only [List.filter, List.length_cons]

lemma filter_length_smaller {α : Type} {p : α → Prop} (hdecidable : ∀ b : α, Decidable (p b)) (b : List α) :
  (List.filter (fun b0 : α => @decide (p b0) (@hdecidable b0)) b).length ≤ b.length := by
  induction b with
  | nil =>
    rfl
  | cons x xh ih =>
    simp only [List.filter, List.length_cons]
    by_cases hpx : p x
    .
      simp only [hpx, decide_true, List.length_cons, add_le_add_iff_right]
      exact ih
    .
      simp only [hpx, decide_false]
      calc
        _ ≤ xh.length := by exact ih
        _ ≤ xh.length + 1 := by norm_num

def my_head {α : Type} (xs : List α) (hnonempty : xs ≠ []): α :=
  match hl : xs with
  | [] => absurd (by rfl) hnonempty
  | x::_ => x

def my_tail {α : Type} (xs : List α) (hnonempty : xs ≠ []): List α :=
  match hl : xs with
  | [] => absurd (by rfl) hnonempty
  | _::xs => xs

def my_quick_sort  {α : Type} [instlt : LT α][instdc : DecidableLT α] : List α → List α :=
  fun l =>
    if hlength : l.length = 0
    then []
    else
      have lnonempty : l ≠ [] := by
        intro h
        apply hlength
        rw [h]
        exact rfl
      let pivot := my_head l lnonempty
      let xs := my_tail l lnonempty
      let parted := xs.partition (fun x => x < pivot)
      let smaller := parted.1
      let larger  := parted.2
      have hl2 : l.length = (pivot :: xs).length := by
        cases hll : l
        case nil => contradiction
        case cons y ys =>
          rw [List.length_cons,List.length_cons]
          have hxseqys : xs = ys := by
            dsimp [xs]
            simp only [hll]
            dsimp[my_tail]
          rw [hxseqys]
      have hsmaller : (List.filter (fun b ↦ decide (b < my_head l lnonempty)) (my_tail l lnonempty)).length < l.length := by
        rw [hl2]
        rw [List.length_cons]
        dsimp [xs]
        generalize my_head l lnonempty = y
        generalize my_tail l lnonempty = ys
        induction ys with
        | nil => simp
        | cons z zh ih =>
          calc
            _ ≤ (z :: zh).length := by
              simp only [List.filter, List.length_cons]
              by_cases hpx : z < y
              .
                simp only [hpx, decide_true, List.length_cons, add_le_add_iff_right]
                exact filter_length_smaller (fun b ↦ instdc b y) zh
              .
                simp only [hpx, decide_false]
                calc
                  _ ≤ zh.length := by exact filter_length_smaller (fun b ↦ instdc b y) zh
                  _ ≤ zh.length + 1 := by norm_num
            _ < (z :: zh).length + 1 := by norm_num
      have hlarger : (List.filter (not ∘ (fun b ↦ decide (b < my_head l lnonempty))) (my_tail l lnonempty)).length < l.length := by
        rw [hl2]
        rw [List.length_cons]
        dsimp [xs]
        generalize my_head l lnonempty = y
        generalize my_tail l lnonempty = ys
        induction ys with
        | nil => simp
        | cons z zh ih =>
          calc
            _ ≤ (z :: zh).length := by
              simp only [List.filter, List.length_cons]
              have fun_comp_not {f : α → Bool}: (not ∘ f) = (fun x => not (f x)) := by
                funext y
                simp
              by_cases hpx : z < y
              .
                simp only [Function.comp_apply, hpx, decide_true, Bool.not_true, xs]
                rw [fun_comp_not]
                exact Nat.le_of_succ_le ih
              .
                simp only [Function.comp_apply, hpx, decide_false, Bool.not_false, List.length_cons,
                  add_le_add_iff_right, xs]
                rw [fun_comp_not]
                exact List.length_filter_le (fun x ↦ !decide (x < y)) zh
            _ < (z :: zh).length + 1 := by norm_num
      (my_quick_sort smaller ++ [pivot] ++ my_quick_sort larger)
  termination_by xs => xs.length
