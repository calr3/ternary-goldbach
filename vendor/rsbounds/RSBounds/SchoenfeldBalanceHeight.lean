import RSBounds.SchoenfeldBalanceVNumeric

/-!
# Theorem 11 parameter balance: the split height clears the finite-RH height

Schoenfeld (1976), p. 345: "For `log x ≥ 1737`, we now get from (7.5) and (7.29) that
`T₂ > 17e^{v₀X} > A`." Here `A` is the height `1894438.5122` of the finite-RH premise (RS75's A rounded down).
With `v ≥ v₀`, `vX ≥ X − log(17X/2π)/2`. That function of `X` increases, and at `X = 13.4192`
(implied by `log x ≥ 1737`) it exceeds `log(1894438.5122/17)` by about `0.00197`, so the threshold
`1737` is essentially sharp for this step. The final comparison uses `e > 2.7182818283`,
`π > 3.141592`, and seven terms of the exponential series.
-/

open Real Set

namespace TernaryGoldbach.RSBounds.SchoenfeldBalanceHeight

open SchoenfeldBalanceV

/-- `log x ≥ 1737` gives `X = √(log x / R) ≥ 13.4192`. -/
theorem X_ge_of_log_ge {x : ℝ} (hx : 1737 ≤ Real.log x) :
    13.4192 ≤ Real.sqrt (Real.log x / 9.645908801) := by
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

/-- `v₀X = X − log(17X/(2π))/2`. -/
theorem vj0_mul (X : ℝ) (hX : 0 < X) :
    vj 0 X * X = X - Real.log (17 * X / ((2 + 3 * 0) * π)) / 2 := by
  unfold vj
  field_simp

/-- `X ↦ X − log(17X/2π)/2` is increasing on `X ≥ X₁ ≥ 1/2`. -/
theorem g_mono {X X1 : ℝ} (hX1 : 1 / 2 ≤ X1) (hX : X1 ≤ X) :
    X1 - Real.log (17 * X1 / ((2 + 3 * 0) * π)) / 2 ≤
      X - Real.log (17 * X / ((2 + 3 * 0) * π)) / 2 := by
  have hX1p : 0 < X1 := by linarith
  have hXp : 0 < X := by linarith
  have hc : (0 : ℝ) < 17 / ((2 + 3 * 0) * π) := by positivity
  have hsplit : Real.log (17 * X / ((2 + 3 * 0) * π)) =
      Real.log (17 * X1 / ((2 + 3 * 0) * π)) + Real.log (X / X1) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hle : Real.log (X / X1) ≤ X / X1 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have hq : X / X1 - 1 = (X - X1) / X1 := by field_simp
  have hk : (X - X1) / X1 ≤ 2 * (X - X1) := by
    rw [div_le_iff₀ hX1p]
    nlinarith
  rw [hsplit]
  linarith

/-- The sharp numerical step at `X = 13.4192`. -/
theorem g_at_13_4192 :
    Real.log (1894438.5122 / 17) ≤ 13.4192 - Real.log (17 * 13.4192 / ((2 + 3 * 0) * π)) / 2 := by
  have hpi : 3.141592 < π := Real.pi_gt_d6
  have hpos : (0 : ℝ) < 17 * 13.4192 / ((2 + 3 * 0) * π) := by positivity
  -- Equivalent form: `(1894438.5122/17)² · (17·13.4192/(2π)) ≤ e^{2·13.4192}`.
  have hlhs : (1894438.5122 / 17 : ℝ) ^ 2 * (17 * 13.4192 / ((2 + 3 * 0) * π)) ≤
      (1894438.5122 / 17 : ℝ) ^ 2 * (17 * 13.4192 / (2 * 3.141592)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  have he1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h26 : (2.7182818283 : ℝ) ^ 26 ≤ Real.exp 26 := by
    have : Real.exp 26 = Real.exp 1 ^ 26 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) he1.le 26
  have htail : ∑ i ∈ Finset.range 7, (0.8384 : ℝ) ^ i / (i.factorial : ℝ) ≤ Real.exp 0.8384 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 7
  have hsum : ∑ i ∈ Finset.range 7, (0.8384 : ℝ) ^ i / (i.factorial : ℝ) =
      1 + 0.8384 + 0.8384 ^ 2 / 2 + 0.8384 ^ 3 / 6 + 0.8384 ^ 4 / 24 + 0.8384 ^ 5 / 120 +
        0.8384 ^ 6 / 720 := by
    simp [Finset.sum_range_succ, Nat.factorial]

  rw [hsum] at htail
  have hexp : Real.exp (2 * 13.4192) = Real.exp 26 * Real.exp 0.8384 := by
    rw [← Real.exp_add]
    norm_num
  have hnum : (1894438.5122 / 17 : ℝ) ^ 2 * (17 * 13.4192 / (2 * 3.141592)) ≤
      (2.7182818283 : ℝ) ^ 26 * (1 + 0.8384 + 0.8384 ^ 2 / 2 + 0.8384 ^ 3 / 6 +
        0.8384 ^ 4 / 24 + 0.8384 ^ 5 / 120 + 0.8384 ^ 6 / 720) := by
    norm_num
  have hmain : (1894438.5122 / 17 : ℝ) ^ 2 * (17 * 13.4192 / ((2 + 3 * 0) * π)) ≤
      Real.exp (2 * 13.4192) := by
    rw [hexp]
    calc (1894438.5122 / 17 : ℝ) ^ 2 * (17 * 13.4192 / ((2 + 3 * 0) * π))
        ≤ (1894438.5122 / 17 : ℝ) ^ 2 * (17 * 13.4192 / (2 * 3.141592)) := hlhs
      _ ≤ (2.7182818283 : ℝ) ^ 26 * (1 + 0.8384 + 0.8384 ^ 2 / 2 + 0.8384 ^ 3 / 6 +
          0.8384 ^ 4 / 24 + 0.8384 ^ 5 / 120 + 0.8384 ^ 6 / 720) := hnum
      _ ≤ Real.exp 26 * Real.exp 0.8384 :=
          mul_le_mul h26 htail (by norm_num) (Real.exp_pos _).le
  have hlog := Real.log_le_log (by positivity) hmain
  rw [Real.log_exp, Real.log_mul (by positivity) hpos.ne', Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **`T₂ ≥ 1894438.5122`.** For `X ≥ 13.4192` and `v ≥ v₀`, the split height
`17 e^{vX}` is at least the finite-RH height (Schoenfeld p. 345, with `A` replaced by `1894438.5122`). -/
theorem split_height_ge {X v : ℝ} (hX : 13.4192 ≤ X) (hv : vj 0 X ≤ v) :
    (1894438.5122 : ℝ) ≤ 17 * Real.exp (v * X) := by
  have hXp : 0 < X := by linarith
  have hvX : vj 0 X * X ≤ v * X := mul_le_mul_of_nonneg_right hv hXp.le
  rw [vj0_mul X hXp] at hvX
  have hg := g_mono (by norm_num : (1 : ℝ) / 2 ≤ 13.4192) hX
  have hnum := g_at_13_4192
  have hlog : Real.log (1894438.5122 / 17) ≤ v * X := by linarith
  have := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by norm_num)] at this
  linarith

end TernaryGoldbach.RSBounds.SchoenfeldBalanceHeight
