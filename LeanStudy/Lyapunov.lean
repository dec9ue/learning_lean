import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open scoped Topology
open Metric

variable {n : ℕ}
abbrev E n := EuclideanSpace ℝ (Fin n)

/-- (Lyapunov) Stability of the flow `x` at equilibrium `x₀`. -/
def isStable (x : E n → ℝ → E n) (x₀ : E n) : Prop :=
  ∀ ⦃ε⦄, 0 < ε → ∃ δ > 0, ∀ ⦃x0⦄, dist x0 x₀ < δ → ∀ ⦃t⦄, 0 ≤ t → dist (x x0 t) x₀ < ε

/--
A minimal Lyapunov package sufficient for Lyapunov (not asymptotic) stability:

* `cont` : `V` is continuous
* `zero_at` : `V x₀ = 0`
* `nonincreasing` : `t ↦ V (x x0 t)` is nonincreasing for every initial condition `x0`
* `init` : the flow starts at the initial condition
* `sublevel_small` : small sublevel sets of `V` sit inside any prescribed ε-ball around `x₀`
  (this follows from `cont` + strict local minimum at `x₀`; you can also assume it directly).
-/
structure isLyapunovFunction (V : E n → ℝ) (f : E n → E n) (x : E n → ℝ → E n) (x₀ : E n) where
  cont : Continuous V
  zero_at : V x₀ = 0
  nonincreasing :
    ∀ x0 {t₁ t₂}, 0 ≤ t₁ → t₁ ≤ t₂ → V (x x0 t₂) ≤ V (x x0 t₁)
  init : ∀ x0, x x0 0 = x0
  sublevel_small :
    ∀ {ε}, 0 < ε → ∃ α > 0, {y : E n | V y ≤ α} ⊆ ball x₀ ε

/-- (Lyapunov’s 2nd theorem — stability) If `V` is a Lyapunov function in the above sense,
then the equilibrium `x₀` is (Lyapunov) stable. -/
theorem lyapunov_second_theorem
  (V : E n → ℝ)
  (f : E n → E n)
  (x : E n → ℝ → E n)
  (x₀ : E n)
  (h : isLyapunovFunction V f x x₀)
  : isStable x x₀ := by
  classical
  intro ε hε
  -- 1) Choose a small sublevel {V ≤ α} inside the ε-ball.
  obtain ⟨α, hαpos, hSub⟩ := h.sublevel_small (ε := ε) hε
  -- 2) Continuity of V at x₀ (with V x₀ = 0) → close initial states have V ≤ α.
  have hcontAt : ContinuousAt (fun y => V y) x₀ := h.cont.continuousAt
  have hEV :
      {y : E n | dist (V y) (V x₀) < α} ∈ 𝓝 x₀ :=
    (Metric.tendsto_nhds.mp (h.cont.continuousAt)) α hαpos
  rcases Metric.mem_nhds_iff.mp hEV with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x0 hx0 t ht
  have hx0V : V x0 ≤ α := by
    have hx0_ball : x0 ∈ ball x₀ δ := by simpa [mem_ball] using hx0
    have hx0dist : dist (V x0) (V x₀) < α := hδ hx0_ball
    have hx0abs  : |V x0 - V x₀| < α := by simpa [Real.dist_eq] using hx0dist
    have hx0abs0 : |V x0| < α := by simpa [h.zero_at, sub_zero] using hx0abs
    exact (abs_lt.1 hx0abs0).2.le
  -- 3) Along trajectories V is nonincreasing and x x0 0 = x0.
  have hmono := h.nonincreasing x0 (t₁ := 0) (t₂ := t) (by exact le_of_eq rfl) ht
  have : V (x x0 t) ≤ V (x x0 0) := hmono
  have : V (x x0 t) ≤ V x0 := by simpa [h.init x0] using this
  have : V (x x0 t) ≤ α := this.trans hx0V
  -- 4) Sublevel inclusion gives the metric bound.
  have : x x0 t ∈ ball x₀ ε := hSub this
  simpa [mem_ball] using this
