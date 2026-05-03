import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Basic
import Mathlib.Order.RelIso.Basic

open Real Set

lemma real_sinh : ∀ x : ℝ, sinh x = (exp x - exp (-x)) / 2 := by
  intro x
  rw [sinh,Complex.sinh]
  rw [exp,exp]
  simp

lemma real_cosh : ∀ x : ℝ, cosh x = (exp x + exp (-x)) / 2 := by
  intro x
  rw [cosh,Complex.cosh]
  rw [exp,exp]
  simp

theorem strictMono_tanh : StrictMono tanh := by
  rintro x y hxy
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh,
    div_lt_div_iff₀ (cosh_pos _) (cosh_pos _), mul_comm, ← sub_pos,
    real_cosh, real_sinh,real_cosh,real_sinh]
  ring_nf
  field_simp
  rw [← exp_add,← exp_add]
  simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_add_neg_iff_add_lt, zero_add, exp_lt_exp]
  linarith

lemma tanh_eq_sinh_div_cosh_abst : tanh = fun x => sinh x / cosh x := by
  ext x
  rw [tanh_eq_sinh_div_cosh]

lemma range_tanh : range tanh = (Ioo (-1) 1 : Set ℝ) := by
  rw [tanh_eq_sinh_div_cosh_abst]
  have eq_fun :
  (fun x => sinh x / cosh x) = (fun x => (exp x - exp (-x)) / (exp x + exp (-x))) := by
    ext x
    rw [real_sinh, real_cosh]
    field_simp
  rw [eq_fun]
  apply Set.ext
  intro y
  constructor
  ·
    -- show that y = (exp x - exp(-x)) / (exp x + exp(-x)) is in (-1, 1).
    rintro ⟨x, rfl⟩
    set a := exp x
    have ha : 0 < a := exp_pos x
    set y := (a - 1/a) / (a + 1/a)
    -- Numerator < Denominator because a > 0
    have num_lt_den : (a - 1/a) < (a + 1/a) := by
      have : 0 < 1/a := one_div_pos.mpr ha
      linarith
    have : y < 1 := by
      dsimp[y]
      calc
        _ < (a + 1 / a) / (a + 1 / a) := by
          refine (div_lt_div_iff_of_pos_right ?_).mpr num_lt_den
          linarith
        _ = 1 := by
          refine div_self (ne_of_gt ?_)
          linarith
    have : -1 < y := by
      dsimp[y]
      field_simp
      have ha1_pos : a * a + 1  > 0 := by nlinarith
      have ha1_pos' : a ^ 2 + 1  > 0 := by nlinarith
      have : - (a * a + 1) < a * a - 1 := by
        simp
        ring_nf
        field_simp
        simp only [lt_add_iff_pos_right, Nat.ofNat_pos, mul_pos_iff_of_pos_right]
        apply sq_pos_of_ne_zero (ne_of_gt ha)
      show -1 < (a ^ 2 - 1) / (a ^ 2 + 1)
      have : (- a ^ 2 - 1) / (a ^ 2 + 1) < (a ^ 2 - 1) / (a ^ 2 + 1) := by
        apply (div_lt_div_iff_of_pos_right ?_).mpr
        simp
        apply sq_pos_of_ne_zero (ne_of_gt ha)
        apply ha1_pos'
      apply lt_of_eq_of_lt ?_ this
      field_simp
      linarith
    have : y ∈ Ioo (-1) 1 := ⟨ by linarith, by linarith ⟩
    convert this
    dsimp[y,a]
    rw [exp_neg]
    field_simp
  · intro hy
    -- For y ∈ (-1, 1), find x s.t. tanh x = y using x = (1/2) * log((1 + y) / (1 - y)).
    set x := 1 / 2 * Real.log ((1 + y) / (1 - y))
    use x
    simp
    rw [exp_neg]
    field_simp
    have : exp x ^ 2 = exp (2 * x) := by
      have : exp x * exp x = exp (2 * x) := by
        rw [← exp_add]
        ring_nf
      rw [← this]
      ring_nf
    rw [this]
    dsimp [x]
    ring_nf
    rw [exp_log]
    grind
    show 0 < y * (1 - y)⁻¹ + (1 - y)⁻¹
    have : y * (1 - y)⁻¹ + (1 - y)⁻¹ = (y + 1) * (1 - y)⁻¹ := by
      ring
    rw [this]
    apply div_pos
    linarith [hy.1]
    linarith [hy.2]

lemma image_tanh : tanh '' univ = (Ioo (-1) 1 : Set ℝ) := by
  rw [image_univ]
  exact range_tanh

/-- `Real.tanh` as an `OrderIso` between `ℝ` and `ℝ`. -/
noncomputable def tanhOrderIso : ℝ ≃o (Ioo (-1) 1 : Set ℝ) :=
  (strictMono_tanh.orderIso _).trans <|
    (OrderIso.setCongr _ _ range_tanh)

theorem tanhOrderIso_eq_tanh (x : ℝ) : tanhOrderIso x = tanh x := by
  exact rfl

/-- Inverse of the `tanh` function, takes the domain of the range `-1 < artanh x` and
`artanh x < 1` -/
noncomputable def artanhOrderIso (x : (Ioo (-1) 1 : Set ℝ)) : ℝ :=
  tanhOrderIso.symm x

noncomputable def artanh (x : ℝ) : ℝ :=
  if h : x ∈ Ioo (-1) 1 then
    artanhOrderIso ⟨x, h⟩
  else
    0

theorem artanhOrderIso_symm (x : ℝ) : artanhOrderIso (tanhOrderIso x) = x := by
  simp [artanhOrderIso]

theorem artanh_tanh (x : ℝ) : artanh (tanh x) = x := by
  rw [artanh, dif_pos]
  exact tanhOrderIso.left_inv x

theorem tanh_artanh (x : (Ioo (-1) 1 : Set ℝ)) : tanh (artanh x) = x := by
  have ⟨y, hy⟩ : ∃ y : ℝ, x = tanhOrderIso y :=
    ⟨artanhOrderIso x, (OrderIso.symm_apply_eq tanhOrderIso).mp rfl⟩
  rw [hy]
  dsimp [artanh]
  simp only [Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
  rw [artanhOrderIso_symm]
  rw [tanhOrderIso_eq_tanh]
