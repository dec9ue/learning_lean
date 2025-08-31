import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Order.Filter.Basic

noncomputable section
open scoped Topology
open Metric
open Set Filter

variable {n : ℕ}
abbrev E n := EuclideanSpace ℝ (Fin n)

namespace LaSalle

-- A minimal semiflow notion on nonnegative time
structure Semiflow (E : Type _) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  φ     : E → ℝ → E
  φ0    : ∀ x0, φ x0 0 = x0
  φ_add : ∀ x0 t s, 0 ≤ t → 0 ≤ s → φ x0 (t + s) = φ (φ x0 t) s

variable {V : E n → ℝ} {f : E n → E n}
variable {φ : E n → ℝ → E n}

/-- Derivative of `V` along the vector field `f` at point `x`. -/
def dVdt (V : E n → ℝ) (f : E n → E n) (x : E n) : ℝ :=
  (fderiv ℝ V x) (f x)

/-- Forward (positive) invariance of a set for a semiflow `φ`. -/
def PositivelyInvariant (φ : E n → ℝ → E n) (S : Set (E n)) : Prop :=
  ∀ ⦃x0⦄, x0 ∈ S → ∀ ⦃t⦄, 0 ≤ t → φ x0 t ∈ S

/-- The set where the Lie derivative (time derivative of `V` along `f`) vanishes. -/
def Z (V : E n → ℝ) (f : E n → E n) : Set (E n) :=
  {x | dVdt V f x = 0}

/-- Chain rule for `V ∘ φ x0` at time `t`. -/
lemma hasDerivAt_V_along
    (hV : ContDiff ℝ 1 V)
    {x0 : E n} {t : ℝ}
    (hx : HasDerivAt (fun s => φ x0 s) (f (φ x0 t)) t) :
    HasDerivAt (fun s => V (φ x0 s))
      ((fderiv ℝ V (φ x0 t)) (f (φ x0 t))) t := by
  have hxf := hx.hasFDerivAt
  have hV_diffAt : DifferentiableAt ℝ V (φ x0 t) :=
    (hV.differentiable le_rfl).differentiableAt
  have hV1 : HasFDerivAt V (fderiv ℝ V (φ x0 t)) (φ x0 t) :=
    hV_diffAt.hasFDerivAt
  have hcomp := hV1.comp t hxf
  simpa using hcomp.hasDerivAt

/-- If `d/dt V(φ x0 t) ≤ 0` everywhere, then `V ∘ φ x0` is nonincreasing in `t`. -/

lemma V_nonincreasing_along
    (hV : ContDiff ℝ 1 V)
    (hxC1 : ∀ x0, ContDiff ℝ 1 (fun t => φ x0 t))
    (hode : ∀ x0 t, HasDerivAt (fun s => φ x0 s) (f (φ x0 t)) t)
    (hle : ∀ y, dVdt V f y ≤ 0) :
    ∀ x0 {t₁ t₂}, 0 ≤ t₁ → t₁ ≤ t₂ → V (φ x0 t₂) ≤ V (φ x0 t₁) := by
  intro x0 t1 t2 ht1 h12
  have hdiff : Differentiable ℝ (fun s => V (φ x0 s)) := by
    simpa [Function.comp] using ((hV.comp (hxC1 x0)).differentiable le_rfl)
  have hderiv_nonpos : ∀ t, deriv (fun s => V (φ x0 s)) t ≤ 0 := by
    intro t
    have h := hasDerivAt_V_along (V:=V) (φ:=φ) (x0:=x0) (t:=t) hV (hode x0 t)
    have hderiv_eq : deriv (fun s => V (φ x0 s)) t
        = (fderiv ℝ V (φ x0 t)) (f (φ x0 t)) := (HasDerivAt.deriv h)
    simpa [dVdt, hderiv_eq] using (hle (φ x0 t))
  exact (antitone_of_deriv_nonpos hdiff hderiv_nonpos) h12

/-- The largest positively invariant subset of `S` as a union of all such subsets. -/
def MaxInvIn (φ : E n → ℝ → E n) (S : Set (E n)) : Set (E n) :=
  ⋃₀ {T : Set (E n) | T ⊆ S ∧ PositivelyInvariant φ T}

lemma MaxInvIn_subset (φ : E n → ℝ → E n) (S : Set (E n)) :
    MaxInvIn φ S ⊆ S := by
  intro x hx
  rcases Set.mem_sUnion.mp hx with ⟨T, hTmem, hxT⟩
  exact hTmem.1 hxT

lemma MaxInvIn_invariant (φ : E n → ℝ → E n) (S : Set (E n)) :
    PositivelyInvariant φ (MaxInvIn φ S) := by
  intro x hx t ht
  rcases Set.mem_sUnion.mp hx with ⟨T, hTmem, hxT⟩
  have hxT' : φ x t ∈ T := (hTmem.2) hxT ht
  exact Set.mem_sUnion.mpr ⟨T, hTmem, hxT'⟩

/- One standard definition of the ω-limit set of the trajectory from `x0`. -/
def omegaLimit (φ : E n → ℝ → E n) (x0 : E n) : Set (E n) :=
  {y | ∃ u : ℕ → ℝ, (∀ k, 0 ≤ u k) ∧ Tendsto u atTop atTop ∧
        Tendsto (fun k => φ x0 (u k)) atTop (𝓝 y)}

/-- Adding a nonnegative constant preserves divergence to `+∞` (as a map on the codomain). -/
lemma tendsto_atTop_add_const_right (s : ℝ) :
    Tendsto (fun t : ℝ => t + s) atTop atTop := by
  -- For any threshold `B`, eventually `t + s ≥ B` once `t ≥ B - s`.
  refine Filter.tendsto_atTop.2 ?_
  intro B
  refine Filter.eventually_atTop.2 ?_
  refine ⟨B - s, ?_⟩
  intro t ht
  have : (B - s) + s ≤ t + s := add_le_add_right ht s
  have hB : B = (B - s) + s := by ring
  simpa [hB.symm] using this

/-- For trajectories starting in `Ω` where `dV/dt ≤ 0` on `Ω`, the value of `V` is
constant along the ω-limit orbit under any fixed forward shift. (Sketch: the map
`t ↦ V (φ x0 t)` is nonincreasing on `[0,∞)`, hence has a (possibly extended) limit
as `t → ∞`; therefore `lim_{k} V(φ x0 (u_k)) = lim_{k} V(φ x0 (u_k+σ))` for any fixed `σ ≥ 0`.
Taking subsequences realizing `y` and `φ y σ` via ω-limit yields the equality.) -/
/- For trajectories from `x0`, if the scalar function `g(t)=V(φ x0 t)` has a (finite)
limit as `t → +∞`, then for any ω-limit point `y` and any shift `σ ≥ 0` we have
`V(φ y σ) = V y`.
We additionally assume the semiflow shift law and continuity in the state variable
(to identify the limits of the shifted sequences). -/
lemma V_equal_on_omega_shift
    {Ω : Set (E n)} {x0 : E n}
    (hV : ContDiff ℝ 1 V)
    (hxC1 : ∀ x0, ContDiff ℝ 1 (fun t => φ x0 t))
    (hode : ∀ x0 t, HasDerivAt (fun s => φ x0 s) (f (φ x0 t)) t)
    (hΩ_inv : PositivelyInvariant φ Ω)
    (hx0 : x0 ∈ Ω)
    (hφ_add : ∀ x t s, 0 ≤ t → 0 ≤ s → φ x (t + s) = φ (φ x t) s)
    (hcont_in_x : ∀ s ≥ 0, Continuous (fun z : E n => φ z s))
    (hLimit : ∃ L, Tendsto (fun t => V (φ x0 t)) atTop (𝓝 L)) :
    ∀ {y}, y ∈ omegaLimit φ x0 → ∀ {σ}, 0 ≤ σ → V (φ y σ) = V y := by
  classical
  intro y hy σ hσ
  rcases hy with ⟨u, hu_nonneg, hu_toInf, hconv⟩
  rcases hLimit with ⟨L, hglim⟩
  -- define g(t) := V(φ x0 t)
  let g : ℝ → ℝ := fun t => V (φ x0 t)
  -- along u(k), g(u(k)) → L by composition
  have hlim_u : Tendsto (fun k => g (u k)) atTop (𝓝 L) := hglim.comp hu_toInf
  -- and also, by continuity and the ω-limit convergence, g(u(k)) → V y
  have hcontV : Continuous V := hV.continuous
  have hlim_toVy : Tendsto (fun k => g (u k)) atTop (𝓝 (V y)) := by
    simpa using (hcontV.tendsto y).comp hconv
  -- uniqueness of limits in ℝ forces V y = L
  have hVy : V y = L := tendsto_nhds_unique hlim_toVy hlim_u
  -- now treat the shifted sequence u(k)+σ
  have h_toInf_shift : Tendsto (fun k => u k + σ) atTop atTop :=
    (tendsto_atTop_add_const_right σ).comp hu_toInf
  have hlim_shift_toL : Tendsto (fun k => g (u k + σ)) atTop (𝓝 L) :=
    hglim.comp h_toInf_shift
  -- identify its state-space limit as φ y σ via the shift law + continuity in state
  have hrew : (fun k => φ x0 (u k + σ)) = (fun k => φ (φ x0 (u k)) σ) := by
    funext k; simpa using hφ_add x0 (u k) σ (hu_nonneg k) hσ
  have hcontφσ : Continuous (fun z : E n => φ z σ) := hcont_in_x σ hσ
  have hstate_shift : Tendsto (fun k => φ x0 (u k + σ)) atTop (𝓝 (φ y σ)) := by
    have : Tendsto ((fun z : E n => φ z σ) ∘ fun k => φ x0 (u k)) atTop (𝓝 (φ y σ)) :=
      (hcontφσ.tendsto y).comp hconv
    simpa [Function.comp, hrew] using this
  -- hence g(u(k)+σ) → V(φ y σ)
  have hlim_toVφy : Tendsto (fun k => g (u k + σ)) atTop (𝓝 (V (φ y σ))) := by
    simpa using (hcontV.tendsto (φ y σ)).comp hstate_shift
  -- uniqueness again: V(φ y σ) = L
  have hVφy : V (φ y σ) = L := tendsto_nhds_unique hlim_toVφy hlim_shift_toL
  -- conclude equality
  simp [hVy, hVφy]

/-- If `Ω` is positively invariant and `x0 ∈ Ω`, the trajectory stays in `Ω` for all `t ≥ 0`. -/
lemma traj_mem_of_posInvariant
    {Ω : Set (E n)} {x0 : E n}
    (hΩ_inv : PositivelyInvariant φ Ω) (hx0 : x0 ∈ Ω) :
    ∀ {t}, 0 ≤ t → φ x0 t ∈ Ω := by
  intro t ht
  exact hΩ_inv hx0 ht

/-- Under closedness and positive invariance, the ω-limit set from `x0 ∈ Ω` is contained in `Ω`. -/
lemma omegaLimit_subset_of_closed_posInvariant
    {Ω : Set (E n)} {x0 : E n}
    (hΩ_closed : IsClosed Ω) (hΩ_inv : PositivelyInvariant φ Ω) (hx0 : x0 ∈ Ω) :
    omegaLimit φ x0 ⊆ Ω := by
  intro y hy
  rcases hy with ⟨u, hu_nonneg, hu_toInf, hconv⟩
  have h_all : ∀ k, φ x0 (u k) ∈ Ω := by
    intro k; exact hΩ_inv hx0 (hu_nonneg k)
  have h_eventually : ∀ᶠ k in atTop, φ x0 (u k) ∈ Ω := Eventually.of_forall h_all
  exact hΩ_closed.mem_of_tendsto hconv h_eventually

/-- For `C¹` Lyapunov function and continuous vector field, the Lie derivative `x ↦ dVdt V f x` is continuous. -/
lemma continuous_dVdt_of_C1
    (hV : ContDiff ℝ 1 V) (hf : Continuous f) :
    Continuous (fun x => dVdt V f x) := by
  -- continuity of x ↦ fderiv V x under C¹
  have h1 : Continuous (fun x : E n => fderiv ℝ V x) := by
    have hhV : Continuous (fun x : E n => fderiv ℝ V x) :=
      hV.continuous_fderiv (by norm_num)
    simpa using hhV
  -- pair with x ↦ f x
  have hpair : Continuous (fun x : E n => (fderiv ℝ V x, f x)) := h1.prod_mk hf
  -- evaluation (A,v) ↦ A v is continuous
  have happly : Continuous (fun p : (E n →L[ℝ] ℝ) × (E n) => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  -- compose and simplify to the target function
  have hcomp : Continuous (fun x : E n => (fun p : (E n →L[ℝ] ℝ) × (E n) => p.1 p.2)
                                    (fderiv ℝ V x, f x)) :=
    happly.comp hpair
  simpa [dVdt] using hcomp

/-
/-- Adding a nonnegative constant preserves divergence to `+∞` (as a map on the codomain). -/
lemma tendsto_atTop_add_const_right (s : ℝ) :
    Tendsto (fun t : ℝ => t + s) atTop atTop := by
  -- For any threshold `B`, eventually `t + s ≥ B` once `t ≥ B - s`.
  refine Filter.tendsto_atTop.2 ?_
  intro B
  refine Filter.eventually_atTop.2 ?_
  refine ⟨B - s, ?_⟩
  intro t ht
  have : (B - s) + s ≤ t + s := add_le_add_right ht s
  have hB : B = (B - s) + s := by ring
  simpa [hB.symm] using this
-/
/-- The ω-limit set is positively invariant under the semiflow when
    (i) the semigroup/shift property holds and (ii) the map `z ↦ φ z s` is
    continuous for each fixed nonnegative `s`. -/
lemma omegaLimit_posInvariant (x0 : E n)
    (hφ_add : ∀ x t s, 0 ≤ t → 0 ≤ s → φ x (t + s) = φ (φ x t) s)
    (hcont_in_x : ∀ s ≥ 0, Continuous (fun z => φ z s)) :
    PositivelyInvariant φ (omegaLimit φ x0) := by
  -- Take any `y ∈ ω(x0)` and shift the witnessing times by `s ≥ 0`.
  intro y hy s hs
  rcases hy with ⟨u, hu_nonneg, hu_toInf, hconv⟩
  -- Candidate shifted time sequence
  refine ⟨fun k => u k + s, ?_, ?_, ?_⟩
  · -- nonnegativity
    intro k; exact add_nonneg (hu_nonneg k) hs
  · -- divergence to +∞ is preserved by adding a constant on the right
    have : Tendsto (fun k => (u k) + s) atTop atTop :=
      (tendsto_atTop_add_const_right s).comp hu_toInf
    simpa using this
  · -- convergence of states via continuity in the initial condition and the shift law
    have hcomp : Tendsto (fun k => φ (φ x0 (u k)) s) atTop (𝓝 (φ y s)) := by
      have : Tendsto ((fun z : E n => φ z s) ∘ fun k => φ x0 (u k)) atTop (𝓝 (φ y s)) :=
        ((hcont_in_x s hs).tendsto y).comp hconv
      simpa [Function.comp] using this
    have hshift : (fun k => φ x0 (u k + s)) = (fun k => φ (φ x0 (u k)) s) := by
      funext k; simpa using hφ_add x0 (u k) s (hu_nonneg k) hs
    simpa [hshift] using hcomp

/-- If `Ω` is closed and positively invariant, `V` is `C¹`, the ODE chain rule holds,
    `dV/dt ≤ 0` on `Ω`, and the Lie derivative is continuous in the state; moreover the
    semiflow has the local "stay in a small ball for a short time" property and satisfies
    the shift law, then every ω-limit point lies in the zero set of the Lie derivative. -/
lemma omegaLimit_subset_Z
    {Ω : Set (E n)}
    (hΩ_closed : IsClosed Ω) (hΩ_inv : PositivelyInvariant φ Ω)
    (hV : ContDiff ℝ 1 V)
    (hxC1 : ∀ x0, ContDiff ℝ 1 (fun t => φ x0 t))
    (hode : ∀ x0 t, HasDerivAt (fun s => φ x0 s) (f (φ x0 t)) t)
    (hleΩ : ∀ x ∈ Ω, dVdt V f x ≤ 0)
    (hdV : Continuous (fun x => dVdt V f x))
    (h_stay : ∀ (y : E n) (r : ℝ), 0 < r → ∃ σ > 0,
                ∀ {z : E n}, z ∈ Metric.ball y r → ∀ {s}, s ∈ Icc (0:ℝ) σ →
                  φ z s ∈ Metric.ball y r)
    (hφ_add : ∀ x t s, 0 ≤ t → 0 ≤ s → φ x (t + s) = φ (φ x t) s)
    (hcont_in_x : ∀ s ≥ 0, Continuous (fun z : E n => φ z s))
    {x0 : E n} (hx0 : x0 ∈ Ω)
    (hLimit_x0 : ∃ L, Tendsto (fun t => V (φ x0 t)) atTop (𝓝 L)) :
    omegaLimit φ x0 ⊆ Z V f := by
  intro y hy
  have hy0 : y ∈ omegaLimit φ x0 := hy
  -- y is an ω-limit point ⇒ y ∈ Ω
  have hyΩ : y ∈ Ω :=
    (omegaLimit_subset_of_closed_posInvariant (φ:=φ) (x0:=x0)
      hΩ_closed hΩ_inv hx0) hy
  -- On Ω we have dV/dt ≤ 0
  have hy_le : dVdt V f y ≤ 0 := hleΩ y hyΩ
  -- If it were strictly negative, we derive a contradiction
  classical
  by_cases hzero : dVdt V f y = 0
  · -- already in Z
    simpa [Z, dVdt, hzero]
  · have hy_lt : dVdt V f y < 0 := lt_of_le_of_ne hy_le hzero
    -- pick ε > 0 with margin below
    set ε := (- (dVdt V f y)) / 2 with hεdef
    have hεpos : 0 < ε := by
      have : 0 < - (dVdt V f y) := by exact neg_pos.mpr hy_lt
      simpa [hεdef] using half_pos this
    -- continuity of Lie derivative ⇒ uniform negativity near y
    have hpre : ((fun x => dVdt V f x) ⁻¹' Metric.ball (dVdt V f y) ε) ∈ 𝓝 y := by
      simpa [hεdef] using (hdV.tendsto y) (Metric.ball_mem_nhds _ hεpos)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨r, rpos, hball⟩
    have hneg_near : ∀ {z}, z ∈ Metric.ball y r → dVdt V f z ≤ -ε := by
      intro z hz
      have hz' : |dVdt V f z - dVdt V f y| < ε := by
        have hz'' := hball hz
        simpa [Metric.mem_ball] using hz''
      have h1 : dVdt V f z ≤ dVdt V f y + ε := by
        have habs := abs_lt.mp hz'
        linarith
      -- Using ε = -(dVdt y)/2, we have dVdt y + ε = -ε
      have hε' : ε = - (dVdt V f y) / 2 := by simpa using hεdef
      have hsum_eq : dVdt V f y + ε = -ε := by
        have : dVdt V f y + (- (dVdt V f y) / 2) = dVdt V f y / 2 := by ring
        rw [hε', this]
        ring_nf
      simpa [hsum_eq] using h1
    -- local stay property: once near y, stay near y for a uniform σ > 0
    obtain ⟨σ, σpos, hstay⟩ := h_stay y r rpos
    -- choose k large so that φ x0 (u k) is inside the ball
    rcases hy with ⟨u, hu_nonneg, hu_toInf, hconv⟩
    have h_in : ∀ᶠ k in atTop, φ x0 (u k) ∈ Metric.ball y r :=
      (hconv.eventually (Metric.ball_mem_nhds _ rpos))
    -- build a fixed-time drop using mean value theorem on [u k, u k + σ]
    have drop : ∀ᶠ k in atTop,
        V (φ x0 (u k + σ)) ≤ V (φ x0 (u k)) - ε*σ := by
      -- The core analytic argument: along [u k, u k + σ], derivative ≤ -ε
      -- thanks to `hneg_near` and `hstay`; apply mean value theorem to `g(t)=V(φ x0 t)`.
      refine h_in.mono ?_
      intro k hk
      have hz : φ x0 (u k) ∈ Metric.ball y r := hk
      -- for t in [0,σ], semigroup law keeps the state in the ball
      have hball_path : ∀ {s}, s ∈ Icc (0:ℝ) σ →
          φ x0 (u k + s) ∈ Metric.ball y r := by
        intro s hs
        have : φ x0 (u k + s) = φ (φ x0 (u k)) s :=
          hφ_add x0 (u k) s (hu_nonneg k) hs.1
        simpa [this] using hstay (z:=φ x0 (u k)) hz (s:=s) hs
      -- On that interval, the time derivative of g(t) is ≤ -ε
      have hderiv_on : ∀ t ∈ Icc (u k) (u k + σ),
          HasDerivAt (fun s => V (φ x0 s)) (dVdt V f (φ x0 t)) t := by
        intro t ht
        simpa [dVdt] using hasDerivAt_V_along (V:=V) (φ:=φ) (x0:=x0) (t:=t) hV (hode x0 t)
      have hderiv_le : ∀ t ∈ Icc (u k) (u k + σ),
          dVdt V f (φ x0 t) ≤ -ε := by
        intro t ht
        have : t = u k + (t - u k) := by ring
        have hs : (t - u k) ∈ Icc (0:ℝ) σ := by
          have ht0 : u k ≤ t := by exact ht.1
          have ht1 : t ≤ u k + σ := by exact ht.2
          constructor <;> linarith
        have hmem : φ x0 t ∈ Metric.ball y r := by
          have : φ x0 t = φ x0 (u k + (t - u k)) := by ring_nf
          simpa [this] using hball_path (s:=(t - u k)) hs
        exact hneg_near hmem
      -- Mean value theorem / integral argument to obtain a fixed drop ε*σ
      -- NOTE: this step can be filled using either FTC or `exists_hasDerivAt_eq_slope`.
      have : V (φ x0 (u k + σ)) ≤ V (φ x0 (u k)) - ε*σ := by
        -- Use the Mean Value Theorem (via `exists_hasDerivAt_eq_slope`) on g(t) = V (φ x0 t)
        set a : ℝ := u k
        set b : ℝ := u k + σ
        set g : ℝ → ℝ := fun s => V (φ x0 s)
        have hcont : ContinuousOn g (Icc a b) :=
          ((hV.comp (hxC1 x0)).continuous).continuousOn
        have hderiv : ∀ t ∈ Icc a b, HasDerivAt g (dVdt V f (φ x0 t)) t := by
          intro t ht; simpa [g, dVdt, a, b] using hderiv_on t (by simpa [a, b] using ht)
        have hlt : a < b := by dsimp [a, b]; linarith [σpos]
        -- Derivative on the open interval is enough for the MVT lemma
        have hderiv' : ∀ t ∈ Ioo a b, HasDerivAt g (dVdt V f (φ x0 t)) t := by
          intro t ht
          exact hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
        obtain ⟨c, hc, hc_slope⟩ :=
          exists_hasDerivAt_eq_slope (f := g)
            (f' := fun t => dVdt V f (φ x0 t))
            hlt hcont hderiv'
        -- From the derivative bound on the interval we get a bound on the slope
        have hslope_le : slope g a b ≤ -ε := by
          have hcIcc : c ∈ Icc a b := ⟨le_of_lt hc.1, le_of_lt hc.2⟩
          have hdc : dVdt V f (φ x0 c) ≤ -ε := by
            simpa [a, b] using hderiv_le c (by simpa [a, b] using hcIcc)
          -- slope g a b = (g b - g a)/(b - a) since a ≠ b
          have hne : a ≠ b := ne_of_lt hlt
          have hs : slope g a b = (g b - g a) / (b - a) := by
            simp [slope_def_field, hne]
          -- combine with the derivative equality at c
          have : (g b - g a) / (b - a) ≤ -ε := by
            simpa [hc_slope] using hdc
          simpa [hs] using this
        -- Multiply by (b-a)>0 to turn the slope bound into a difference bound
        have hbpos : 0 < b - a := sub_pos.mpr hlt
        have hdiff_le' : (b - a) * slope g a b ≤ (b - a) * (-ε) :=
          mul_le_mul_of_nonneg_left hslope_le (le_of_lt hbpos)
        have hbne_zero_0 : b - a ≠ 0 := ne_of_gt hbpos
        have hdiff_le : g b - g a ≤ -ε * (b - a) := by
          rw [slope] at hdiff_le'
          field_simp at hdiff_le'
          simpa [slope_def_field, hbne_zero_0, g, a, b,
                 mul_comm, mul_left_comm, mul_assoc] using hdiff_le'
        have hdiff_le : g b - g a ≤ -ε * (b - a) := by
          have hbne_zero_1 : b - a ≠ 0 := ne_of_gt hbpos
          -- simplify (b-a) * slope g a b = g b - g a
          rw [slope] at hdiff_le'
          field_simp at hdiff_le'
          simpa [slope_def_field, hbne_zero_1, g, a, b,
                 mul_comm, mul_left_comm, mul_assoc] using hdiff_le'
        -- rearrange: g b ≤ g a - ε*(b-a)
        have hfinal : g b ≤ g a - ε * (b - a) := by
          have : g b ≤ -ε * (b - a) + g a := (sub_le_iff_le_add).mp hdiff_le
          simp [add_comm, add_left_comm, add_assoc, this]
          linarith
        -- substitute the definitions of g,a,b and (b-a)=σ
        simpa [g, a, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfinal
      exact this
    -- take limits along the ω-sequence and use positive invariance to reach a contradiction
    have hlim1 : Tendsto (fun k => V (φ x0 (u k))) atTop (𝓝 (V y)) := by
      have hcontV : Continuous V := hV.continuous
      exact (hcontV.tendsto y).comp hconv
    have hrew : (fun k => φ x0 (u k + σ)) = (fun k => φ (φ x0 (u k)) σ) := by
      funext k; simpa using hφ_add x0 (u k) σ (hu_nonneg k) (le_of_lt σpos)
    have hcontφσ : Continuous (fun z : E n => φ z σ) := hcont_in_x σ (le_of_lt σpos)
    have hφσ : Tendsto (fun k => φ x0 (u k + σ)) atTop (𝓝 (φ y σ)) := by
      have hcomp : Tendsto ((fun z : E n => φ z σ) ∘ fun k => φ x0 (u k)) atTop (𝓝 (φ y σ)) :=
        (hcontφσ.tendsto y).comp hconv
      simpa [Function.comp, hrew] using hcomp
    have hlim2 : Tendsto (fun k => V (φ x0 (u k + σ))) atTop (𝓝 (V (φ y σ))) :=
      (hV.continuous.tendsto _).comp hφσ
    have hg : Tendsto (fun k => V (φ x0 (u k)) - ε*σ) atTop (𝓝 (V y - ε*σ)) := by
      simpa using hlim1.sub tendsto_const_nhds
    have hdrop_limit : V (φ y σ) ≤ V y - ε*σ :=
      le_of_tendsto_of_tendsto hlim2 hg drop
    have hpos : 0 < ε*σ := mul_pos hεpos σpos
    have Veq : V (φ y σ) = V y :=
      V_equal_on_omega_shift (φ:=φ) (V:=V) (f:=f) (Ω:=Ω) (x0:=x0)
        hV hxC1 hode hΩ_inv hx0 hφ_add hcont_in_x (hLimit := hLimit_x0)
        (y:=y) hy0 (σ:=σ) (le_of_lt σpos)
    have : False := by
      have : V y ≤ V y - ε*σ := by simpa [Veq] using hdrop_limit
      linarith [hpos]
    exact this.elim

/-- **LaSalle's invariance principle** (sketch):
If `Ω` is closed and positively invariant, `V` is `C¹`, and `dV/dt ≤ 0` on `Ω`,
then the ω-limit set of any trajectory starting in `Ω` is contained in the
largest positively invariant subset of `Ω ∩ {dV/dt = 0}`.  The full proof
requires additional compactness/limit-set facts and is left as `sorry`.
-/
theorem laSalle_invariance
    (Ω : Set (E n))
    (hΩ_closed : IsClosed Ω)
    (hΩ_inv : PositivelyInvariant φ Ω)
    (V : E n → ℝ)
    (hV : ContDiff ℝ 1 V)
    (hleΩ : ∀ x ∈ Ω, dVdt V f x ≤ 0)
    (hxC1 : ∀ x0, ContDiff ℝ 1 (fun t => φ x0 t))
    (hode : ∀ x0 t, HasDerivAt (fun s => φ x0 s) (f (φ x0 t)) t)
    (hdV : Continuous (fun x => dVdt V f x))
    (h_stay : ∀ (y : E n) (r : ℝ), 0 < r → ∃ σ > 0,
                ∀ {z : E n}, z ∈ Metric.ball y r → ∀ {s}, s ∈ Icc (0:ℝ) σ →
                  φ z s ∈ Metric.ball y r)
    (hφ_add : ∀ x t s, 0 ≤ t → 0 ≤ s → φ x (t + s) = φ (φ x t) s)
    (hcont_in_x : ∀ s ≥ 0, Continuous (fun z => φ z s))
    (hLimit_all : ∀ x0 ∈ Ω, ∃ L, Tendsto (fun t => V (φ x0 t)) atTop (𝓝 L)) :
    ∀ {x0}, x0 ∈ Ω → omegaLimit φ x0 ⊆ MaxInvIn φ (Ω ∩ Z V f) := by
  intro x0 hx0 y hy
  -- ω-limit is contained in Ω by closedness + positive invariance
  have hΩ' : omegaLimit φ x0 ⊆ Ω :=
    omegaLimit_subset_of_closed_posInvariant (φ:=φ) (x0:=x0) hΩ_closed hΩ_inv hx0
  -- ω-limit is contained in Z by LaSalle’s key lemma (still to be filled)
  have hZ' : omegaLimit φ x0 ⊆ Z V f :=
    omegaLimit_subset_Z (Ω:=Ω) (φ:=φ) (V:=V) (f:=f)
      hΩ_closed hΩ_inv hV hxC1 hode hleΩ hdV h_stay hφ_add hcont_in_x
      (x0:=x0) hx0 (hLimit_x0 := hLimit_all x0 hx0)
  -- Thus ω-limit ⊆ Ω ∩ Z
  have hsubset : omegaLimit φ x0 ⊆ (Ω ∩ Z V f) := by
    intro z hz; exact ⟨hΩ' hz, hZ' hz⟩
  -- And ω-limit itself is positively invariant (under the shift and continuity assumptions)
  have hinv : PositivelyInvariant φ (omegaLimit φ x0) :=
    omegaLimit_posInvariant (φ:=φ) (x0:=x0) hφ_add hcont_in_x
  -- By definition of MaxInvIn (sUnion of all positively invariant subsets of Ω ∩ Z),
  -- the ω-limit set is one of the candidates; hence any y ∈ ω-limit lies in MaxInvIn.
  refine Set.mem_sUnion.mpr ?_
  refine ⟨omegaLimit φ x0, ⟨hsubset, hinv⟩, ?_⟩
  simpa using (show y ∈ omegaLimit φ x0 from ‹y ∈ omegaLimit φ x0›)

end LaSalle
