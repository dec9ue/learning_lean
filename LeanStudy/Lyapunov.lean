import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section
open scoped Topology
open Metric

variable {n : ℕ}
abbrev E n := EuclideanSpace ℝ (Fin n)

/-- (Lyapunov) Stability of the flow `x` at equilibrium `x₀`. -/
def isStable (x : E n → ℝ → E n) (x₀ : E n) : Prop :=
  ∀ ⦃ε⦄, 0 < ε → ∃ δ > 0, ∀ ⦃x0⦄, dist x0 x₀ < δ → ∀ ⦃t⦄, 0 ≤ t → dist (x x0 t) x₀ < ε

/-- V の幾何コア：連続・局所最小（小サブレベル包含）。 -/
structure IsLyapCore (V : E n → ℝ) (x₀ : E n) : Prop where
  cont : Continuous V
  zero_at : V x₀ = 0
  sublevel_small :
    ∀ {ε}, 0 < ε → ∃ α > 0, {y : E n | V y ≤ α} ⊆ ball x₀ ε

/-- V の単調性が与えられたときの Lyapunov 安定性。 -/
 theorem lyapunov_stability_from_nonincreasing
  (V : E n → ℝ) (x : E n → ℝ → E n) (x₀ : E n)
  (hcore : IsLyapCore V x₀)
  (hinit : ∀ x0, x x0 0 = x0)
  (hmono : ∀ x0 {t₁ t₂}, 0 ≤ t₁ → t₁ ≤ t₂ → V (x x0 t₂) ≤ V (x x0 t₁))
  : isStable x x₀ := by
  classical
  intro ε hε
  obtain ⟨α, hαpos, hSub⟩ := hcore.sublevel_small (ε := ε) hε
  -- 連続性から「初期を十分近く → V(x0) ≤ α」
  have hcontAt : ContinuousAt V x₀ := hcore.cont.continuousAt
  have hEV : {y : E n | dist (V y) (V x₀) < α} ∈ 𝓝 x₀ :=
    (Metric.tendsto_nhds.mp hcontAt) α hαpos
  rcases Metric.mem_nhds_iff.mp hEV with ⟨δ, hδpos, hδ⟩
  refine ⟨δ, hδpos, ?_⟩
  intro x0 hx0 t ht
  -- V(x0) ≤ α
  have hx0V : V x0 ≤ α := by
    have hx0_ball : x0 ∈ ball x₀ δ := by simpa [mem_ball] using hx0
    have hx0dist : dist (V x0) (V x₀) < α := hδ hx0_ball
    have hx0abs  : |V x0 - V x₀| < α := by simpa [Real.dist_eq] using hx0dist
    have hx0abs0 : |V x0| < α := by simpa [hcore.zero_at, sub_zero] using hx0abs
    exact (abs_lt.1 hx0abs0).2.le
  -- 単調性で V(x(t)) ≤ V(x0)
  have : V (x x0 t) ≤ V (x x0 0) := hmono x0 (by exact le_of_eq rfl) ht
  have : V (x x0 t) ≤ V x0 := by simpa [hinit x0] using this
  have : V (x x0 t) ≤ α := this.trans hx0V
  -- サブレベル包含から距離評価
  have : x x0 t ∈ ball x₀ ε := hSub this
  simpa [mem_ball] using this

open ContinuousLinearMap

/-- Chain rule：`(V ∘ x)` の導関数（fderiv 版）。 -/
lemma deriv_V_along_flow_fderiv
  {V : E n → ℝ} {x : ℝ → E n} {f : E n → E n} {t : ℝ}
  (hV : ContDiff ℝ 1 V)
  (hx : HasDerivAt x (f (x t)) t) :
  HasDerivAt (fun s => V (x s)) ((fderiv ℝ V (x t)) (f (x t))) t := by
  have hxf := hx.hasFDerivAt
  have hV0 : HasStrictFDerivAt V (fderiv ℝ V (x t)) (x t) :=
    hV.hasStrictFDerivAt (by norm_num)
  have hV1 := hV0.hasFDerivAt
  have hVx0 := hV1.comp t hxf
  have hVx1 := hVx0.hasDerivAt
  convert hVx1
  simp

/-- `(fderiv V y) (f y) ≤ 0` 全点で ⇒ `V ∘ x` は非増大。 -/
lemma nonincreasing_of_chain_rule_fderiv
  {V : E n → ℝ} {x : E n → ℝ → E n} {f : E n → E n}
  (hV : ContDiff ℝ 1 V)
  (hxC1 : ∀ x0, ContDiff ℝ 1 (fun t => x x0 t))
  (hode : ∀ x0 t, HasDerivAt (fun s => x x0 s) (f (x x0 t)) t)
  (hle : ∀ y, (fderiv ℝ V y) (f y) ≤ 0)
  : ∀ x0 {t₁ t₂}, 0 ≤ t₁ → t₁ ≤ t₂ → V (x x0 t₂) ≤ V (x x0 t₁) := by
  intro x0 t1 t2 ht1 ht12
  have hderiv_chain{x0 :E n} {t : ℝ} :
      HasDerivAt (fun s => V (x x0 s)) ((fderiv ℝ V (x x0 t)) (f (x x0 t))) t := by
    exact deriv_V_along_flow_fderiv hV (hode x0 t)
  have hderiv_nonpos (t1 : ℝ) :
    deriv (fun s => V (x x0 s)) t1 ≤ 0 := by
    rw [HasDerivAt.deriv (@hderiv_chain x0 t1)]
    apply hle
  have hdiff : Differentiable ℝ (fun s => V (x x0 s)) := by
      simpa [Function.comp] using ((hV.comp (hxC1 x0)).differentiable le_rfl)
  apply antitone_of_deriv_nonpos hdiff hderiv_nonpos
  assumption

/--
This is a lemma that states that the Riesz representation theorem holds for finite-dimensional inner product spaces.
It states that for any continuous linear map `ℓ` from an inner product space `E` to `𝕜`, there exists a unique element `y` in `E` suc
This proof is just a confirmation of bijectivity of `InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))`
-/
lemma riesz_representation
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n))
  (g : (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ)
  :
  (g f) = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm g ⬝ᵥ f := by
    let ggg := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm g
    have hgg_eq_dual_ggg : g = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) ggg := by
      dsimp [ggg]
      rw [(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).apply_symm_apply g]
    rw [hgg_eq_dual_ggg]
    -- cancel toDual and tuDual.symm
    rw [(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm_apply_apply ggg]
    simp only [InnerProductSpace.toDual_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      dotProduct, mul_comm]

/-- Euclid での同一視：`(fderiv V y) v = ⟪∇V(y), v⟫`. -/
lemma fderiv_apply_eq_inner_grad {V : E n → ℝ} {y v: E n}
  :
  (fderiv ℝ V y) v = (gradient V) y ⬝ᵥ v := by
  dsimp [gradient]
  apply riesz_representation

/-- 勾配版の単調性。 -/
lemma nonincreasing_of_chain_rule_grad
  {x : E n → ℝ → E n} {f : E n → E n} {V : E n → ℝ}
  (hV : ContDiff ℝ 1 V)
  (hxC1 : ∀ x0, ContDiff ℝ 1 (fun t => x x0 t))
  (hode : ∀ x0 t, HasDerivAt (fun s => x x0 s) (f (x x0 t)) t)
  (hle_grad : ∀ y, ((gradient V) y) ⬝ᵥ (f y) ≤ 0)
  : ∀ x0 {t₁ t₂}, 0 ≤ t₁ → t₁ ≤ t₂ → V (x x0 t₂) ≤ V (x x0 t₁) := by
  -- fderiv 版へ還元
  have h₀ := @fderiv_apply_eq_inner_grad n V
  refine nonincreasing_of_chain_rule_fderiv (V:=V) (x:=x) (f:=f) hV hxC1 hode ?_
  intro y; simp only [h₀, hle_grad]

/-- 代表的な“全部のせ”形。 -/
lemma lyapunov_stability_full
  (V : E n → ℝ) (f : E n → E n) (x : E n → ℝ → E n) (x₀ : E n)
  (hcore : IsLyapCore V x₀)
  (hinit : ∀ x0, x x0 0 = x0)
  (hV_C1 : ContDiff ℝ 1 V)
  (hx_C1 : ∀ x0, ContDiff ℝ 1 (fun t => x x0 t))
  (hode : ∀ x0 t, HasDerivAt (fun s => x x0 s) (f (x x0 t)) t)
  (hle_grad : ∀ y, ((gradient V) y) ⬝ᵥ (f y) ≤ 0)
  : isStable x x₀ := by
  apply lyapunov_stability_from_nonincreasing (V:=V) (x:=x) (x₀:=x₀)
  · exact hcore
  · exact hinit
  · apply nonincreasing_of_chain_rule_grad hV_C1 (fun x0 ↦ hx_C1 x0) hode hle_grad
