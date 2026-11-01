import TernaryGoldbach.Explicit.ZeroSumBound

/-!
# The explicit-formula bound for `S_χ(δ, x)` (`χ` primitive, `χ ≠ 1`)

`explicit_formula` + `zero_sum_bound` + the line `ℜs = −1/2` (`|L'/L| ≤ (2/log 2 + 4.8)(D_N + 37 + 2.6|y|)`,
`|G_δ| ≤ 112 e^{−θ_δ|y|}`):
`|S_χ(δ, x)| ≤ E₀ + E₁ √x + E₂ x + V/(2π√x)` under GRH up to `T₀ ≥ max(10π|δ|, 50)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace TernaryGoldbach.Explicit

theorem integral_exp_neg_mul_abs {θ : ℝ} (hθ : 0 < θ) :
    ∫ y : ℝ, Real.exp (-(θ * |y|)) = 2 / θ := by
  have := integral_comp_abs (f := fun t => Real.exp (-(θ * t)))
  rw [this]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := θ) one_pos hθ
  simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] at h
  rw [h]; ring

theorem integral_abs_mul_exp_neg_mul_abs {θ : ℝ} (hθ : 0 < θ) :
    ∫ y : ℝ, |y| * Real.exp (-(θ * |y|)) = 2 / θ ^ 2 := by
  have := integral_comp_abs (f := fun t => t * Real.exp (-(θ * t)))
  rw [this]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := θ) two_pos hθ
  have e : ∫ t in Ioi (0:ℝ), t * Real.exp (-(θ * t)) =
      ∫ t in Ioi (0:ℝ), t ^ ((2:ℝ) - 1) * Real.exp (-(θ * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    norm_num
  rw [e, h, Real.Gamma_two, Real.rpow_two]
  field_simp

theorem integrable_abs_mul_exp {θ : ℝ} (hθ : 0 < θ) :
    Integrable fun y : ℝ => |y| * Real.exp (-(θ * |y|)) := by
  refine ((integrable_exp_neg_abs (c := θ / 2) (by positivity)).const_mul (2 / θ)).mono'
    (by fun_prop) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have ha : θ / 2 * |y| ≤ Real.exp (θ / 2 * |y|) := by
    linarith [Real.add_one_le_exp (θ / 2 * |y|)]
  have hE : Real.exp (θ / 2 * |y|) * Real.exp (-(θ * |y|)) = Real.exp (-(θ / 2 * |y|)) := by
    rw [← Real.exp_add]; ring_nf
  calc |y| * Real.exp (-(θ * |y|)) = 2 / θ * (θ / 2 * |y| * Real.exp (-(θ * |y|))) := by
        field_simp
    _ ≤ 2 / θ * (Real.exp (θ / 2 * |y|) * Real.exp (-(θ * |y|))) := by gcongr
    _ = 2 / θ * Real.exp (-(θ / 2 * |y|)) := by rw [hE]

/-- The vertical-line constant `V = 112 (2/log 2 + 4.8)((D_N + 37)(2/θ_δ) + 2.6 (2/θ_δ²))`. -/
noncomputable def Vb (N : ℕ) (δ : ℝ) : ℝ :=
  112 * (2 / Real.log 2 + 4.8) * ((DN N + 37) * (2 / thetaD δ) + 2.6 * (2 / thetaD δ ^ 2))

/-- **The line `ℜs = −1/2`**: `|∫ hInt(−1/2 + iy) dy| ≤ x^{−1/2} V`. -/
theorem norm_integral_hInt_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖∫ y : ℝ, hInt χ δ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ x ^ (-(1 / 2) : ℝ) * Vb N δ := by
  set θ := thetaD δ with hθ
  have hθ0 : 0 < θ := thetaD_pos δ
  set c₁ := 2 / Real.log 2 + 4.8 with hc₁
  have hc₁0 : 0 ≤ c₁ := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hD : 0 ≤ DN N + 37 := by linarith [DN_nonneg N]
  set g : ℝ → ℝ := fun y => x ^ (-(1 / 2) : ℝ) * 112 * c₁ *
    ((DN N + 37) * Real.exp (-(θ * |y|)) + 2.6 * (|y| * Real.exp (-(θ * |y|)))) with hg
  have hgi : Integrable g :=
    (((integrable_exp_neg_abs hθ0).const_mul (DN N + 37)).add
      ((integrable_abs_mul_exp hθ0).const_mul 2.6)).const_mul _
  have hpt : ∀ y : ℝ, ‖hInt χ δ x (((-1 / 2 : ℝ) : ℂ) + y * I)‖ ≤ g y := by
    intro y
    set s : ℂ := ((-1 / 2 : ℝ) : ℂ) + y * I with hs
    have hsre : s.re = -1 / 2 := by simp [hs]
    have hsim : s.im = y := by simp [hs]
    rw [hInt, norm_mul, norm_mul, norm_cpow_x hx, hsre]
    have hL := norm_logDeriv_L_left hχ hχ1 y
    have hLB := LB_le_linear (N := N) y
    have hL' : ‖logDeriv χ.LFunction s‖ ≤ c₁ * (DN N + 37 + 2.6 * |y|) := by
      refine hL.trans ?_
      have e : Real.log (BT N y / 0.355) / Real.log 2 / (1 / 2) + 4.8 * Real.log (BT N y / 0.355) =
          c₁ * Real.log (BT N y / 0.355) := by rw [hc₁]; ring
      rw [e]; exact mul_le_mul_of_nonneg_left hLB hc₁0
    have hGs := norm_G_uniform s δ (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
    rw [hsim] at hGs
    have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
    have e2 : x ^ (-1 / 2 : ℝ) = x ^ (-(1 / 2) : ℝ) := by norm_num
    calc ‖logDeriv χ.LFunction s‖ * (‖Gr s δ 0‖ * x ^ (-1 / 2 : ℝ))
        ≤ (c₁ * (DN N + 37 + 2.6 * |y|)) * (112 * Real.exp (-(θ * |y|)) * x ^ (-1 / 2 : ℝ)) :=
          mul_le_mul hL' (mul_le_mul_of_nonneg_right hGs hxp) (by positivity) (by positivity)
      _ = g y := by rw [hg, e2]; ring
  refine (norm_integral_le_of_norm_le hgi (Eventually.of_forall hpt)).trans (le_of_eq ?_)
  rw [hg, integral_const_mul, integral_add ((integrable_exp_neg_abs hθ0).const_mul _)
    ((integrable_abs_mul_exp hθ0).const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_neg_mul_abs hθ0, integral_abs_mul_exp_neg_mul_abs hθ0]
  unfold Vb; rw [← hθ, ← hc₁]; ring

/-- **The explicit-formula bound** (`χ` primitive, `χ ≠ 1`): under GRH up to `T₀ ≥ max(10π|δ|, 50)`,
for `x ≥ 1`, `|S_χ(δ, x)| ≤ E₀ + E₁ √x + E₂ x + x^{−1/2} V/(2π)`. -/
theorem norm_Ssum_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T0 : ℝ} (hT0 : max (10 * π * |δ|) 50 ≤ T0)
    (hG : ∀ ρ : ℂ, χ.LFunction ρ = 0 → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ T0 → ρ.re = 1 / 2) :
    ‖Ssum χ δ x‖ ≤ E0b N + √x * E1b N T0 + x * E2b N T0 δ + x ^ (-(1 / 2) : ℝ) * Vb N δ / (2 * π) := by
  have hx0 : 0 < x := by linarith
  obtain ⟨Tk, -, hlim⟩ := explicit_formula hχ hχ1 δ hx0
  set I0 := ∫ y : ℝ, hInt χ δ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have h1 : ‖-Ssum χ δ x - (1 / (2 * π) : ℂ) * I0‖ ≤ E0b N + √x * E1b N T0 + x * E2b N T0 δ :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k =>
      zero_sum_bound hχ hχ1 δ hx hT0 hG (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * Vb N δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hInt_le hχ hχ1 δ hx0) (by positivity)
  have e : Ssum χ δ x = -((-Ssum χ δ x - (1 / (2 * π) : ℂ) * I0) + (1 / (2 * π) : ℂ) * I0) := by ring
  rw [e, norm_neg]
  exact (norm_add_le _ _).trans (by linarith)

end TernaryGoldbach.Explicit
