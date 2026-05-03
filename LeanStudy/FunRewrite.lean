import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul


noncomputable section

def f (x : ℝ) : ℝ := x ^ 2

def g (x : ℝ) : ℝ := x ^ 3

example {x : ℝ} : (f x) ^ 3 = (g x) ^ 2 := by
  rw [f, g] -- this works
  ring

example {x₀ f' g' : ℝ} :
    (fun x => f x + g x) x₀ = (x₀ ^ 2 + x₀ ^ 3) := by
  -- rw [f, g] -- this does not work
  dsimp [f, g] -- this works
  -- simp [f, g] -- this also works

example {x₀ f' g' : ℝ} :
    HasDerivAt (fun x => f x + g x) (2 * x₀ + 3 * x₀ ^ 2) x₀ := by
  -- rw [f, g] -- this does not work
  dsimp [f, g] -- this works
  apply HasDerivAt.add
  sorry
  sorry
