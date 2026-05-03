import Mathlib.Data.Set.Basic

-- 1) intro を1回だけ実行する tactic
macro "my_intro" : tactic =>
  `(tactic| intro)

-- 2) simp を実行する tactic
macro "my_simp" : tactic =>
  `(tactic|
     try simp
     )

example (P Q : Prop) : P → Q → P := by
  my_intro
  my_intro
  exact ‹P›

example (a b : Nat) : a + b = b + a := by
  my_simp
  rw [Nat.add_comm]
