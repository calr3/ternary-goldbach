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

/-- Taylor polynomial of degree 6. -/
noncomputable def taylor6 (f : ℝ) : ℝ := 1 + f + f ^ 2 / 2 + f ^ 3 / 6 + f ^ 4 / 24 + f ^ 5 / 120 + f ^ 6 / 720

/-- `exp(n + f) ≤ e₊ⁿ (T₆(f) + f⁷/4410)` for `0 ≤ f ≤ 1`. -/
theorem exp_le_aux (n : ℕ) {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    rexp (n + f) ≤ 2.7182818286 ^ n * (taylor6 f + f ^ 7 / 4410) := by
  have h := Real.exp_bound' h0 h1 (n := 7) (by norm_num)
  have e : rexp (n + f) = rexp 1 ^ n * rexp f := by rw [Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  have he := Real.exp_one_lt_d9
  have hn : rexp 1 ^ n ≤ 2.7182818286 ^ n := pow_le_pow_left₀ (Real.exp_pos 1).le he.le n
  have hf : rexp f ≤ taylor6 f + f ^ 7 / 4410 := by
    refine h.trans (le_of_eq ?_)
    simp only [taylor6, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast; ring
  rw [e]
  exact mul_le_mul hn hf (Real.exp_pos _).le (by positivity)

/-- `e₋ⁿ T₆(f) ≤ exp(n + f)` for `0 ≤ f`. -/
theorem exp_ge_aux (n : ℕ) {f : ℝ} (h0 : 0 ≤ f) :
    2.7182818283 ^ n * taylor6 f ≤ rexp (n + f) := by
  have h := Real.sum_le_exp_of_nonneg h0 7
  have e : rexp (n + f) = rexp 1 ^ n * rexp f := by rw [Real.exp_add, ← Real.exp_nat_mul]; ring_nf
  have he := Real.exp_one_gt_d9
  have hn : 2.7182818283 ^ n ≤ rexp 1 ^ n := pow_le_pow_left₀ (by norm_num) he.le n
  have hf : taylor6 f ≤ rexp f := by
    refine le_trans (le_of_eq ?_) h
    simp only [taylor6, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast; ring
  rw [e]
  exact mul_le_mul hn hf (by unfold taylor6; positivity) (pow_nonneg (Real.exp_pos 1).le n)

/-- Numerical upper bound for a logarithm: `log z ≤ n + f` if `z ≤ e₋ⁿ T₆(f)`. -/
theorem log_le_num {z : ℝ} (n : ℕ) (f : ℝ) (hz : 0 < z) (h0 : 0 ≤ f)
    (h : z ≤ 2.7182818283 ^ n * taylor6 f) : Real.log z ≤ n + f := by
  rw [Real.log_le_iff_le_exp hz]; exact h.trans (exp_ge_aux n h0)

/-- Numerical lower bound for a logarithm: `n + f ≤ log z` if `e₊ⁿ (T₆(f) + f⁷/4410) ≤ z`. -/
theorem le_log_num {z : ℝ} (n : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : 2.7182818286 ^ n * (taylor6 f + f ^ 7 / 4410) ≤ z) : (n : ℝ) + f ≤ Real.log z := by
  have hz : 0 < z := lt_of_lt_of_le (by unfold taylor6; positivity) h
  rw [Real.le_log_iff_exp_le hz]; exact (exp_le_aux n h0 h1).trans h

end TernaryGoldbach.MinorArcs
