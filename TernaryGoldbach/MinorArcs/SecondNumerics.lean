import Mathlib

/-!
# Numerical helpers for the second choice of parameters [B, §6.3.2]

We compare functions of `L = log T` (`T = x^{1/3} ≥ 6·10⁶`) and `s = log L` with powers of `L` by
expanding `exp` around a base point: `exp(s/2) ≥ exp(s₀/2)(1 + d/2 + d²/8)`, `d = s - s₀ ≥ 0`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

theorem exp_six_tenths_le : rexp 0.6 ≤ 1.8223 := by
  have h := Real.exp_bound' (x := 0.6) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_fifteen_six_le : rexp 15.6 ≤ 6e6 := by
  have h1 : rexp 15.6 = rexp 1 ^ 15 * rexp 0.6 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have h15 : rexp 1 ^ 15 ≤ 2.7182818286 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 15
  rw [h1]
  calc rexp 1 ^ 15 * rexp 0.6 ≤ 2.7182818286 ^ 15 * 1.8223 :=
        mul_le_mul h15 exp_six_tenths_le (Real.exp_pos _).le (by positivity)
    _ ≤ 6e6 := by norm_num

/-- `log T ≥ 15.6` for `T ≥ 6·10⁶`. -/
theorem fifteen_six_le_log {T : ℝ} (hT : 6e6 ≤ T) : 15.6 ≤ Real.log T := by
  rw [Real.le_log_iff_exp_le (by linarith)]; exact exp_fifteen_six_le.trans hT

theorem log_fifteen_six_le : Real.log 15.6 ≤ 2.75 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : rexp 2.75 = rexp 1 ^ 2 * rexp 0.75 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_gt_d9
  have h2 : (2.7182818283 : ℝ) ^ 2 ≤ rexp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) he.le 2
  have h3 := Real.sum_le_exp_of_nonneg (x := 0.75) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h3
  rw [h1]
  nlinarith [Real.exp_pos 0.75]

/-- `exp(s/2) ≥ exp(s₀/2)(1 + d/2 + d²/8)` for `d = s - s₀ ≥ 0`. -/
theorem exp_half_ge {s s₀ : ℝ} (h : s₀ ≤ s) :
    rexp (s₀ / 2) * (1 + (s - s₀) / 2 + (s - s₀) ^ 2 / 8) ≤ rexp (s / 2) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (x := (s - s₀) / 2) (by linarith)
  have e : rexp (s / 2) = rexp (s₀ / 2) * rexp ((s - s₀) / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq (by ring)) h1) (Real.exp_pos _).le

/-- `√L ≥ √15.6 (1 + d/2 + d²/8)` with `d = log L - log 15.6`, for `L ≥ 15.6`. -/
theorem sqrt_ge_of_log {L : ℝ} (hL : 15.6 ≤ L) :
    √15.6 * (1 + (Real.log L - Real.log 15.6) / 2 + (Real.log L - Real.log 15.6) ^ 2 / 8) ≤ √L := by
  have hL0 : 0 < L := by linarith
  have h := exp_half_ge (Real.log_le_log (by norm_num) hL)
  have e1 : ∀ z : ℝ, 0 < z → rexp (Real.log z / 2) = √z := fun z hz => by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz]; ring_nf
  rwa [e1 _ hL0, e1 _ (by norm_num)] at h

theorem sqrt_fifteen_six_ge : (3.9496 : ℝ) ≤ √15.6 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num

/-- `γ < 0.5812`, from `γ < H₁₂₈ - log 128` (Mathlib's `eulerMascheroniSeq'` bound). -/
theorem eulerMascheroni_lt : eulerMascheroniConstant < 0.5812 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have h1 : eulerMascheroniSeq' 128 = (harmonic 128 : ℝ) - Real.log 128 := by
    rw [eulerMascheroniSeq']; norm_num
  have hH : (harmonic 128 : ℝ) ≤ 5.4331471 := by
    have : harmonic 128 ≤ (54331471 / 10000000 : ℚ) := by
      simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]; norm_num
    have := (Rat.cast_le (K := ℝ)).2 this
    rw [Rat.cast_div] at this; norm_num at this ⊢
  have hl : Real.log 128 = 7 * Real.log 2 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  linarith

/-- `e^γ ≤ 1.7882`. -/
theorem exp_gamma_le_sharp : rexp eulerMascheroniConstant ≤ 1.7882 := by
  refine (Real.exp_le_exp.2 eulerMascheroni_lt.le).trans ?_
  have h := Real.exp_bound' (x := 0.5812) (by norm_num) (by norm_num) (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

end TernaryGoldbach.MinorArcs
