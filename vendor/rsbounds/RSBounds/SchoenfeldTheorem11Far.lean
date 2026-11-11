import RSBounds.SchoenfeldQuadraticFar
import RSBounds.SchoenfeldTheorem11B23

/-!
# Schoenfeld (1976), Theorem 11 for `e^700 ≤ x < e^1737`, and hence for `x ≥ e^23`

Below `e^1737` the split height of `SchoenfeldTheorem11Analytic` would fall under the finite-RH
height. Here the zeros above `A = 1894438.5122` are all treated as far zeros
(`SchoenfeldQuadraticFar.psi_error_le_farEnvelope`), with `δ = ε₀(x)/2`. The far allowance is at
most `0.027 (c₀ s)³`, `s = √X e^{−X}`, checked on three ranges of `X` (`far_le_piece`), so the bound
is at most about `0.943 x ε₀(x)`.

Together with `SchoenfeldTheorem11B23` (the RS75 row `b = 23` on `[e^23, e^700]`) and
`SchoenfeldTheorem11Analytic` (`x ≥ e^1737`), this gives Theorem 11 for every `x ≥ e^23`.
-/

open Real

namespace TernaryGoldbach.RSBounds.SchoenfeldTheorem11Far

open SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldQuadraticEnvelope SchoenfeldQuadraticFar

/-- `11.55 ≤ log(1894438.5122/17) ≤ 11.63`. -/
theorem u_bounds : 11.55 ≤ Real.log (1894438.5122 / 17) ∧ Real.log (1894438.5122 / 17) ≤ 11.63 := by
  constructor
  · rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h11 : Real.exp 11 ≤ 2.7182818286 ^ 11 := by
      have : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le he.le 11
    have h055 : Real.exp 0.55 ≤ (1 / (1 - 0.06875)) ^ 8 := by
      have : Real.exp 0.55 = Real.exp 0.06875 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      exact pow_le_pow_left₀ (Real.exp_pos _).le
        (SchoenfeldTheorem11B23.exp_le_inv_one_sub (by norm_num)) 8
    have hsplit : Real.exp 11.55 = Real.exp 11 * Real.exp 0.55 := by
      rw [← Real.exp_add]
      norm_num
    rw [hsplit]
    calc Real.exp 11 * Real.exp 0.55 ≤ 2.7182818286 ^ 11 * (1 / (1 - 0.06875)) ^ 8 :=
          mul_le_mul h11 h055 (Real.exp_pos _).le (by positivity)
      _ ≤ 1894438.5122 / 17 := by norm_num
  · rw [Real.log_le_iff_le_exp (by norm_num)]
    have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
    have h11 : (2.7182818283 : ℝ) ^ 11 ≤ Real.exp 11 := by
      have : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      exact pow_le_pow_left₀ (by norm_num) he.le 11
    have h063 : 1 + 0.63 + 0.63 ^ 2 / 2 + 0.63 ^ 3 / 6 ≤ Real.exp 0.63 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.63) 4
      have hs : ∑ i ∈ Finset.range 4, (0.63 : ℝ) ^ i / (i.factorial : ℝ) =
          1 + 0.63 + 0.63 ^ 2 / 2 + 0.63 ^ 3 / 6 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      linarith
    have hsplit : Real.exp 11.63 = Real.exp 11 * Real.exp 0.63 := by
      rw [← Real.exp_add]
      norm_num
    rw [hsplit]
    calc (1894438.5122 / 17 : ℝ) ≤ 2.7182818283 ^ 11 * (1 + 0.63 + 0.63 ^ 2 / 2 + 0.63 ^ 3 / 6) := by
          norm_num
      _ ≤ Real.exp 11 * Real.exp 0.63 := mul_le_mul h11 h063 (by norm_num) (Real.exp_pos _).le

/-- `0 ≤ R(A) ≤ 10` for Rosser's `R(T) = 0.137 log T + 0.443 log log T + 1.588` at `A = 1894438.5122`. -/
theorem rosserR_A_bounds : 0 ≤ rosserR 1.588 1894438.5122 ∧ rosserR 1.588 1894438.5122 ≤ 10 := by
  unfold rosserR
  have he27 : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  have hl1 : 1 ≤ Real.log 1894438.5122 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [SchoenfeldBalanceVNumeric.exp_one_bounds.2]
  have hl15 : Real.log 1894438.5122 ≤ 15 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have : Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (1894438.5122 : ℝ) ≤ 2.7 ^ 15 := by norm_num
      _ ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) he27.le 15
  have hll0 : 0 ≤ Real.log (Real.log 1894438.5122) := Real.log_nonneg hl1
  have hll : Real.log (Real.log 1894438.5122) ≤ Real.log 1894438.5122 - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  constructor <;> nlinarith

/-- `√(8/(17π)) ≥ 0.386`. -/
theorem c0_ge : 0.386 ≤ Real.sqrt (8 / (17 * π)) := by
  rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
  have := Real.pi_lt_d2
  nlinarith

/-- **The far allowance on a range of `X`.** For `Xlo ≤ X ≤ Xhi ≤ 13.42`, the far allowance at
`U = 1894438.5122` is at most `0.027 (c₀ √X e^{−X})³`, given one numerical inequality. -/
theorem far_le_piece {X Xlo Xhi n En sXlo : ℝ} (hXlo1 : 1 ≤ Xlo) (hXlo : Xlo ≤ X)
    (hXhi : X ≤ Xhi) (hXhi2 : Xhi ≤ 13.42) (hn : 3 * Xhi - Xhi ^ 2 / 11.63 ≤ n)
    (hEn : Real.exp n ≤ En) (hsX : sXlo ≤ Real.sqrt Xlo) (hsX0 : 0 ≤ sXlo)
    (hnum : En * (0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) +
        20 / 1894438.5122 ^ 3) ≤ 0.027 * (0.386 ^ 3 * (Xlo * sXlo))) :
    farAllowance (X ^ 2) 1894438.5122 ≤
      0.027 * (Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X))) ^ 3 := by
  obtain ⟨hu0, hu1⟩ := u_bounds
  obtain ⟨hR0, hR1⟩ := rosserR_A_bounds
  obtain ⟨hq0, hqA⟩ := SchoenfeldBalanceTail.q_bounds (le_refl (1894438.5122 : ℝ))
  have hd0 := SchoenfeldBalanceVNumeric.d_nonneg
  have hd1 := SchoenfeldBalanceTail.d_le
  have hX0 : 0 < X := by linarith
  have hpi : 3.1415 < π := by have := Real.pi_gt_d4; linarith
  set u := Real.log (1894438.5122 / 17) with hu
  set a := X ^ 2 with ha
  have hu0' : 0 < u := by linarith
  have ha0 : 0 ≤ a := sq_nonneg X
  have haXhi : a ≤ Xhi ^ 2 := by rw [ha]; nlinarith
  have hden : 266.805 - Xhi ^ 2 ≤ 2 * u ^ 2 - a := by nlinarith
  have hden0 : 0 < 266.805 - Xhi ^ 2 := by nlinarith
  -- Closed form: `F = e^{−a/u} · W`.
  have hE2u : Real.exp (-(2 * u)) = 289 / 1894438.5122 ^ 2 := by
    have h1 : Real.exp u = 1894438.5122 / 17 := by rw [hu, Real.exp_log (by norm_num)]
    rw [show -(2 * u) = -(u + u) by ring, Real.exp_neg, Real.exp_add, h1]
    norm_num
  set E1 := Real.exp (-(a / u)) with hE1
  have hF : farAllowance a 1894438.5122 =
      E1 * ((1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
          ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3) := by
    unfold farAllowance farPrimitive Phi
    rw [← hu]
    have h1 : Real.exp (-(2 * u + a / u)) = Real.exp (-(2 * u)) * E1 := by
      rw [hE1, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-a / u) = E1 := by rw [hE1, neg_div]
    rw [h1, h2, hE2u]
    have hd : (2 : ℝ) * u ^ 2 - a ≠ 0 := by linarith
    field_simp
    ring
  -- `W ≤ W(Xhi)`.
  have hpi2 : 1 / (2 * π) + q 1894438.5122 ≤ 0.16 := by
    have : 1 / (2 * π) ≤ 1 / (2 * 3.1415) := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) (by linarith)
    have hq' : q 1894438.5122 ≤ 0.015 / 1894438.5122 := hqA
    norm_num at this hq' ⊢
    linarith
  have hW : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
        ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3 ≤
      0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3 := by
    have hnum1 : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 ≤
        0.16 * 13.126 * 135.26 := by
      have h1 : 0 ≤ 1 / (2 * π) + q 1894438.5122 := by positivity
      have h2 : u + SchoenfeldWeightedZeros.d + 1 / 2 ≤ 13.126 := by linarith
      have h3 : u ^ 2 ≤ 135.26 := by nlinarith
      have h4 : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 2 := by linarith
      exact mul_le_mul (mul_le_mul hpi2 h2 h4 (by norm_num)) h3 (sq_nonneg u) (by norm_num)

    have hfrac : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
        ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) ≤
        0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) := by
      apply div_le_div₀ (by norm_num) hnum1 (by positivity)
      exact mul_le_mul_of_nonneg_right hden (by norm_num)
    have hr : 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3 ≤ 20 / 1894438.5122 ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  -- `e^{−a/u} ≤ e^{−a/11.63} ≤ e^n e^{−3X}`.
  have hE1le : E1 ≤ Real.exp n * Real.exp (-(3 * X)) := by
    rw [hE1, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : a / 11.63 ≤ a / u := div_le_div_of_nonneg_left ha0 hu0' hu1
    have h2 : 3 * X - a / 11.63 ≤ 3 * Xhi - Xhi ^ 2 / 11.63 := by
      rw [ha]
      have hXX : 0 ≤ (Xhi - X) * (3 - (Xhi + X) / 11.63) :=
        mul_nonneg (by linarith) (by
          have : (Xhi + X) / 11.63 ≤ 26.84 / 11.63 :=
            div_le_div_of_nonneg_right (by linarith) (by norm_num)
          have : (26.84 : ℝ) / 11.63 ≤ 3 := by norm_num
          linarith)
      have key : 3 * Xhi - Xhi ^ 2 / 11.63 - (3 * X - X ^ 2 / 11.63) =
          (Xhi - X) * (3 - (Xhi + X) / 11.63) := by ring
      linarith
    linarith

  -- `(c₀ s)³ ≥ 0.386³ Xlo √Xlo e^{−3X}`.
  have hc0 := c0_ge
  have hsq : sXlo ≤ Real.sqrt X := le_trans hsX (Real.sqrt_le_sqrt hXlo)
  have hcube : 0.386 ^ 3 * (Xlo * sXlo) * Real.exp (-(3 * X)) ≤
      (Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X))) ^ 3 := by
    have he3 : Real.exp (-X) ^ 3 = Real.exp (-(3 * X)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hss : Real.sqrt X ^ 3 = X * Real.sqrt X := by
      rw [pow_succ, sq, Real.mul_self_sqrt hX0.le]
    rw [mul_pow, mul_pow, he3, hss]
    have h1 : 0.386 ^ 3 ≤ Real.sqrt (8 / (17 * π)) ^ 3 := pow_le_pow_left₀ (by norm_num) hc0 3
    have h2 : Xlo * sXlo ≤ X * Real.sqrt X := mul_le_mul hXlo hsq hsX0 (by linarith)
    have hE : 0 < Real.exp (-(3 * X)) := Real.exp_pos _
    have h3 : 0.386 ^ 3 * (Xlo * sXlo) ≤ Real.sqrt (8 / (17 * π)) ^ 3 * (X * Real.sqrt X) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    calc 0.386 ^ 3 * (Xlo * sXlo) * Real.exp (-(3 * X))
        ≤ Real.sqrt (8 / (17 * π)) ^ 3 * (X * Real.sqrt X) * Real.exp (-(3 * X)) :=
          mul_le_mul_of_nonneg_right h3 hE.le
      _ = Real.sqrt (8 / (17 * π)) ^ 3 * (X * Real.sqrt X * Real.exp (-(3 * X))) := by ring

  -- Combine.
  have hW0 : 0 ≤ 0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) +
      20 / 1894438.5122 ^ 3 := by positivity
  have hWa0 : 0 ≤ (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
        ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3 := by
    have : 0 < 2 * u ^ 2 - a := by linarith
    have : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 2 := by linarith
    positivity
  rw [hF]
  have hE3 : 0 < Real.exp (-(3 * X)) := Real.exp_pos _
  calc E1 * ((1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
          ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3)
      ≤ (Real.exp n * Real.exp (-(3 * X))) *
          (0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3) :=
        mul_le_mul hE1le hW hWa0 (by positivity)
    _ ≤ (En * Real.exp (-(3 * X))) *
          (0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3) := by
        apply mul_le_mul_of_nonneg_right _ hW0
        exact mul_le_mul_of_nonneg_right hEn hE3.le
    _ = (En * (0.16 * 13.126 * 135.26 / ((266.805 - Xhi ^ 2) * 1894438.5122 ^ 2) +
          20 / 1894438.5122 ^ 3)) * Real.exp (-(3 * X)) := by ring
    _ ≤ (0.027 * (0.386 ^ 3 * (Xlo * sXlo))) * Real.exp (-(3 * X)) :=
        mul_le_mul_of_nonneg_right hnum hE3.le
    _ = 0.027 * (0.386 ^ 3 * (Xlo * sXlo) * Real.exp (-(3 * X))) := by ring
    _ ≤ 0.027 * (Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X))) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by norm_num)

/-- `e^n ≤ 2.7182818286^n` for natural `n`. -/
theorem exp_nat_le (n : ℕ) : Real.exp n ≤ 2.7182818286 ^ n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le n

/-- The far allowance bound on `8.5 ≤ X ≤ 13.42`, by three ranges. -/
theorem far_le {X : ℝ} (hX1 : 8.5 ≤ X) (hX2 : X ≤ 13.42) :
    farAllowance (X ^ 2) 1894438.5122 ≤
      0.027 * (Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X))) ^ 3 := by
  have e23 := exp_nat_le 23
  have e25 := exp_nat_le 25
  push_cast at e23 e25
  rcases le_or_gt X 11 with h1 | h1
  · exact far_le_piece (Xlo := 8.5) (Xhi := 11) (n := 23) (En := 2.7182818286 ^ 23)
      (sXlo := 2.915) (by norm_num) hX1 h1 (by norm_num) (by norm_num) e23
      ((Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)) (by norm_num) (by norm_num)
  rcases le_or_gt X 12.5 with h2 | h2
  · exact far_le_piece (Xlo := 11) (Xhi := 12.5) (n := 25) (En := 2.7182818286 ^ 25)
      (sXlo := 3.316) (by norm_num) h1.le h2 (by norm_num) (by norm_num) e25
      ((Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)) (by norm_num) (by norm_num)
  · exact far_le_piece (Xlo := 12.5) (Xhi := 13.42) (n := 25) (En := 2.7182818286 ^ 25)
      (sXlo := 3.535) (by norm_num) h2.le hX2 (by norm_num) (by norm_num) e25
      ((Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)) (by norm_num) (by norm_num)

end TernaryGoldbach.RSBounds.SchoenfeldTheorem11Far
