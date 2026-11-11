import RSBounds.SchoenfeldBalanceV

/-!
# Theorem 11 parameter balance: the split parameter for `X ≥ 13.41`

`log x ≥ 1737` gives `X = √(log x/R) ≥ 13.41`. For such `X` this file discharges the
numerical hypotheses of `SchoenfeldBalanceV.exists_k_eq_one`, so Schoenfeld's split
parameter `v` with `k(v) = 1` exists in `(v₀, v₁)` (7.27)–(7.30), with `d = log(17/2π)`.
Only `2.7 < e < 3` and `3 < π < 3.15` are used, together with two elementary monotonicity
lemmas proved without derivatives.
-/

open Real Set

namespace TernaryGoldbach.RSBounds.SchoenfeldBalanceVNumeric

open SchoenfeldBalanceAlgebra SchoenfeldBalanceV

/-- `log(cX)/X` decreases on `X ≥ X₀` once `log(cX₀) ≥ 1`. -/
theorem log_div_le {c X X0 : ℝ} (hc : 0 < c) (hX0 : 0 < X0) (hX : X0 ≤ X)
    (h1 : 1 ≤ Real.log (c * X0)) : Real.log (c * X) / X ≤ Real.log (c * X0) / X0 := by
  have hXp : 0 < X := lt_of_lt_of_le hX0 hX
  have hsplit : Real.log (c * X) = Real.log (c * X0) + Real.log (X / X0) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hle : Real.log (X / X0) ≤ X / X0 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [div_le_div_iff₀ hXp hX0, hsplit]
  have hq : X / X0 * X0 = X := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right hle hX0.le, mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hX)]

/-- `log(cX)²/X` decreases on `X ≥ X₀` once `log(cX₀) ≥ 2`. -/
theorem log_sq_div_le {c X X0 : ℝ} (hc : 0 < c) (hX0 : 0 < X0) (hX : X0 ≤ X)
    (h2 : 2 ≤ Real.log (c * X0)) :
    Real.log (c * X) ^ 2 / X ≤ Real.log (c * X0) ^ 2 / X0 := by
  have hXp : 0 < X := lt_of_lt_of_le hX0 hX
  set L := Real.log (c * X0) with hL
  set t := Real.log (X / X0) with ht
  have ht0 : 0 ≤ t := Real.log_nonneg (by rw [le_div_iff₀ hX0]; linarith)
  have hsplit : Real.log (c * X) = L + t := by
    rw [hL, ht, ← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hXe : X = X0 * Real.exp t := by
    rw [ht, Real.exp_log (by positivity)]
    field_simp
  have hq : 1 + t + t ^ 2 / 2 ≤ Real.exp t := Real.quadratic_le_exp_of_nonneg ht0
  have key : (L + t) ^ 2 ≤ L ^ 2 * Real.exp t := by
    have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
    have h1 : (L + t) ^ 2 ≤ L ^ 2 * (1 + t + t ^ 2 / 2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h2) ht0, mul_nonneg (mul_nonneg ht0 ht0) (sub_nonneg.mpr h2)]
    exact h1.trans (mul_le_mul_of_nonneg_left hq hL2)
  rw [hsplit, div_le_div_iff₀ hXp hX0, hXe]
  nlinarith [key, hX0]

theorem d_eq : SchoenfeldWeightedZeros.d = Real.log (17 / (2 * π)) := rfl

theorem quarter_lt_d : 1 / 4 < SchoenfeldWeightedZeros.d := by
  rw [d_eq]
  have hpos : 0 < 17 / (2 * π) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hpi : π < 3.15 := Real.pi_lt_d2
  have : (17 / (2 * π))⁻¹ < 3 / 4 := by
    rw [inv_div, div_lt_iff₀ (by norm_num : (0 : ℝ) < 17)]
    linarith
  linarith

theorem d_nonneg : 0 ≤ SchoenfeldWeightedZeros.d := by
  have := quarter_lt_d
  linarith

theorem exp_one_bounds : 2.7 < Real.exp 1 ∧ Real.exp 1 < 3 := by
  constructor
  · have := Real.exp_one_gt_d9
    linarith
  · have := Real.exp_one_lt_d9
    linarith

/-- `1 − v_j = log(c_j X)/(2X)` with `c_j = 17/((2+3j)π)`. -/
theorem one_sub_vj (j X : ℝ) (hX : 0 < X) :
    1 - vj j X = Real.log (17 / ((2 + 3 * j) * π) * X) / (2 * X) := by
  unfold vj
  congr 2
  ring

/-- For `X ≥ 13.41`: `1 − v₀ ≤ 4/26.82`. -/
theorem one_sub_v0_le {X : ℝ} (hX : 13.41 ≤ X) : 1 - vj 0 X ≤ 4 / (2 * 13.41) := by
  have hX0 : (0 : ℝ) < 13.41 := by norm_num
  have hXp : 0 < X := by linarith
  have hc : 0 < 17 / ((2 + 3 * (0 : ℝ)) * π) := by positivity
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi : π < 3.15 := Real.pi_lt_d2
  obtain ⟨he1, he2⟩ := exp_one_bounds
  have harg : 17 / ((2 + 3 * (0 : ℝ)) * π) * 13.41 ≤ 38 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have harg' : 3 ≤ 17 / ((2 + 3 * (0 : ℝ)) * π) * 13.41 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hlog1 : 1 ≤ Real.log (17 / ((2 + 3 * (0 : ℝ)) * π) * 13.41) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hlog4 : Real.log (17 / ((2 + 3 * (0 : ℝ)) * π) * 13.41) ≤ 4 := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he1.le 4]
  have hmono := log_div_le hc hX0 hX hlog1
  rw [one_sub_vj 0 X hXp]
  have : Real.log (17 / ((2 + 3 * 0) * π) * X) / (2 * X) =
      (Real.log (17 / ((2 + 3 * 0) * π) * X) / X) / 2 := by
    field_simp
  rw [this]
  have h2 : Real.log (17 / ((2 + 3 * (0 : ℝ)) * π) * 13.41) / 13.41 ≤ 4 / 13.41 :=
    div_le_div_of_nonneg_right hlog4 hX0.le
  have : 4 / (2 * (13.41 : ℝ)) = 4 / 13.41 / 2 := by norm_num
  rw [this]
  linarith

/-- Bounds on `log(c₁ · 13.41)`, where `c₁ = 17/(5π)`. -/
theorem log_c1_bounds :
    2 ≤ Real.log (17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41) ∧
      Real.log (17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41) ≤ 3 := by
  have hpi3 : 3 < π := Real.pi_gt_three
  have hpi : π < 3.15 := Real.pi_lt_d2
  obtain ⟨he1, he2⟩ := exp_one_bounds
  have hlo : 9 ≤ 17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hhi : 17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41 ≤ 16 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  constructor
  · rw [Real.le_log_iff_exp_le (by linarith)]
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    nlinarith
  · rw [Real.log_le_iff_le_exp (by linarith)]
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he1.le 3]

/-- For `X ≥ 13.41`: `1 − v₁ ≤ 3/26.82`, so `v₁ ≥ 0.888`. -/
theorem one_sub_v1_le {X : ℝ} (hX : 13.41 ≤ X) : 1 - vj 1 X ≤ 3 / (2 * 13.41) := by
  have hX0 : (0 : ℝ) < 13.41 := by norm_num
  have hXp : 0 < X := by linarith
  have hc : 0 < 17 / ((2 + 3 * (1 : ℝ)) * π) := by positivity
  obtain ⟨hl2, hl3⟩ := log_c1_bounds
  have hmono := log_div_le hc hX0 hX (by linarith)
  rw [one_sub_vj 1 X hXp]
  have e : Real.log (17 / ((2 + 3 * 1) * π) * X) / (2 * X) =
      (Real.log (17 / ((2 + 3 * 1) * π) * X) / X) / 2 := by
    field_simp
  rw [e]
  have h2 : Real.log (17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41) / 13.41 ≤ 3 / 13.41 :=
    div_le_div_of_nonneg_right hl3 hX0.le
  have : 3 / (2 * (13.41 : ℝ)) = 3 / 13.41 / 2 := by norm_num
  rw [this]
  linarith

/-- For `X ≥ 13.41`: `X(1 − v₁)² ≤ 9/(4 · 13.41)`. -/
theorem X_one_sub_v1_sq_le {X : ℝ} (hX : 13.41 ≤ X) :
    X * (1 - vj 1 X) ^ 2 ≤ 9 / (4 * 13.41) := by
  have hX0 : (0 : ℝ) < 13.41 := by norm_num
  have hXp : 0 < X := by linarith
  have hc : 0 < 17 / ((2 + 3 * (1 : ℝ)) * π) := by positivity
  obtain ⟨hl2, hl3⟩ := log_c1_bounds
  have hmono := log_sq_div_le hc hX0 hX hl2
  rw [one_sub_vj 1 X hXp]
  have e : X * (Real.log (17 / ((2 + 3 * 1) * π) * X) / (2 * X)) ^ 2 =
      (Real.log (17 / ((2 + 3 * 1) * π) * X) ^ 2 / X) / 4 := by
    field_simp
    ring
  rw [e]
  have hl0 : 0 ≤ Real.log (17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41) := by linarith
  have h9 : Real.log (17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41) ^ 2 ≤ 9 := by nlinarith
  have h2 : Real.log (17 / ((2 + 3 * (1 : ℝ)) * π) * 13.41) ^ 2 / 13.41 ≤ 9 / 13.41 :=
    div_le_div_of_nonneg_right h9 hX0.le
  have : 9 / (4 * (13.41 : ℝ)) = 9 / 13.41 / 4 := by norm_num
  rw [this]
  linarith

/-- The numerical inequality behind `k(v₁) > 1` (7.29), for `X ≥ 13.41`. -/
theorem k_v1_numeric {X : ℝ} (hX : 13.41 ≤ X) :
    1 < (2 + 3 * 1) / 2 * Real.sqrt (vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1)) *
      Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X)) := by
  have hv : 0.888 ≤ vj 1 X := by
    have h := one_sub_v1_le hX
    have : (3 : ℝ) / (2 * 13.41) ≤ 0.112 := by norm_num
    linarith
  have hv1 : vj 1 X ≤ 1 := by
    have hXp : 0 < X := by linarith
    rw [← sub_nonneg, one_sub_vj 1 X hXp]
    have hc : 1 ≤ 17 / ((2 + 3 * (1 : ℝ)) * π) * X := by
      have hpi : π < 3.15 := Real.pi_lt_d2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    exact div_nonneg (Real.log_nonneg hc) (by positivity)
  -- `√(v₁⁶(2v₁² − 1)) ≥ 0.53`, since the expression increases in `v₁ ≥ 0.888`.
  have hpoly : (0.53 : ℝ) ^ 2 ≤ vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1) := by
    have h6 : (0.888 : ℝ) ^ 6 ≤ vj 1 X ^ 6 := pow_le_pow_left₀ (by norm_num) hv 6
    have h2 : (0.888 : ℝ) ^ 2 ≤ vj 1 X ^ 2 := pow_le_pow_left₀ (by norm_num) hv 2
    have hq : 0 ≤ 2 * (0.888 : ℝ) ^ 2 - 1 := by norm_num
    calc (0.53 : ℝ) ^ 2 ≤ 0.888 ^ 6 * (2 * 0.888 ^ 2 - 1) := by norm_num
      _ ≤ vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1) := by
          apply mul_le_mul h6 (by linarith) hq (by positivity)
  have hsqrt : 0.53 ≤ Real.sqrt (vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1)) :=
    Real.le_sqrt_of_sq_le hpoly
  -- `e^{−X(1−v₁)²/v₁} ≥ 0.81`, since `X(1−v₁)²/v₁ ≤ 0.19`.
  have harg : X * (1 - vj 1 X) ^ 2 / vj 1 X ≤ 0.19 := by
    have h := X_one_sub_v1_sq_le hX
    have hv0 : 0 < vj 1 X := by linarith
    rw [div_le_iff₀ hv0]
    have : (9 : ℝ) / (4 * 13.41) ≤ 0.19 * 0.888 := by norm_num
    nlinarith
  have hexp : 0.81 ≤ Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X)) := by
    have h := Real.add_one_le_exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X))
    linarith
  have : (1 : ℝ) < (2 + 3 * 1) / 2 * 0.53 * 0.81 := by norm_num
  calc (1 : ℝ) < (2 + 3 * 1) / 2 * 0.53 * 0.81 := this
    _ ≤ (2 + 3 * 1) / 2 * Real.sqrt (vj 1 X ^ 6 * (2 * vj 1 X ^ 2 - 1)) *
        Real.exp (-(X * (1 - vj 1 X) ^ 2 / vj 1 X)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hexp (by norm_num)
        positivity

/-- **Schoenfeld's split parameter exists for `X ≥ 13.41`** (7.27)–(7.30): there is
`v ∈ (v₀, v₁)` with `k(v) = 1`, for `d = log(17/2π)`. -/
theorem exists_split_parameter {X : ℝ} (hX : 13.41 ≤ X) :
    ∃ v ∈ Ioo (vj 0 X) (vj 1 X), k SchoenfeldWeightedZeros.d X v = 1 := by
  have hXp : 0 < X := by linarith
  have hd := d_nonneg
  have hv0 : 0.85 ≤ vj 0 X := by
    have h := one_sub_v0_le hX
    have : (4 : ℝ) / (2 * 13.41) ≤ 0.15 := by norm_num
    linarith
  have hv1 : 0.888 ≤ vj 1 X := by
    have h := one_sub_v1_le hX
    have : (3 : ℝ) / (2 * 13.41) ≤ 0.112 := by norm_num
    linarith
  have hv02 : 1 < 2 * vj 0 X ^ 2 := by nlinarith
  have hv12 : 1 < 2 * vj 1 X ^ 2 := by nlinarith
  -- `v₀ + d/X ≤ 1`: equivalent to `17/(2π) ≤ X`.
  have hsum : vj 0 X + SchoenfeldWeightedZeros.d / X ≤ 1 := by
    have hpi3 : 3 < π := Real.pi_gt_three
    have hc : 0 < 17 / (2 * π) := by positivity
    have hlog : Real.log (17 * X / ((2 + 3 * 0) * π)) =
        SchoenfeldWeightedZeros.d + Real.log X := by
      rw [d_eq, ← Real.log_mul hc.ne' hXp.ne']
      congr 1
      ring
    have hdX : SchoenfeldWeightedZeros.d ≤ Real.log X := by
      rw [d_eq]
      apply Real.log_le_log hc
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    unfold vj
    rw [hlog]
    have e : SchoenfeldWeightedZeros.d / X = 2 * SchoenfeldWeightedZeros.d / (2 * X) := by
      field_simp
    rw [e, ← sub_nonneg]
    have : 1 - (1 - (SchoenfeldWeightedZeros.d + Real.log X) / (2 * X) +
        2 * SchoenfeldWeightedZeros.d / (2 * X)) =
        (Real.log X - SchoenfeldWeightedZeros.d) / (2 * X) := by
      field_simp
      ring
    rw [this]
    exact div_nonneg (by linarith) (by positivity)
  exact exists_k_eq_one hXp hd (by linarith) hv02
    (k_v0_lt_one hXp hd (by linarith) hv02 hsum)
    (one_lt_k_v1 hXp quarter_lt_d (by linarith) hv12 (k_v1_numeric hX))

end TernaryGoldbach.RSBounds.SchoenfeldBalanceVNumeric

