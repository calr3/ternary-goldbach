import TernaryGoldbach.MinorArcs.FirstChoiceMain
import TernaryGoldbach.MinorArcs.TypeITotal
import TernaryGoldbach.MinorArcs.TypeI2Large

/-!
# [H, §6.3.1]: the Type I terms at the first choice of parameters

Auxiliary bounds. The bound on `S_{I,1}` ((6.56)) is `typeI1_first` (`FirstChoiceTypeI1.lean`):
`|S_{I,1}| ≤ 3.8 · 2x/(δ₀φ(q)) + (log t + 2.96) · 2x/t + 0.014 x^{5/6}`.
-/

open Real

namespace TernaryGoldbach.MinorArcs

theorem sqrt_c₀_bounds : 5.6568 ≤ √c₀ ∧ √c₀ ≤ 5.6569 := by
  unfold c₀
  constructor
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_le_left (by norm_num)]; norm_num

theorem c₂_bounds : 0.6664 ≤ c₂ ∧ c₂ ≤ 0.6665 := by
  obtain ⟨h1, h2⟩ := sqrt_c₀_bounds
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  unfold c₂
  constructor
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith

/-- `log T ≤ 0.0298 √T` for `T ≥ 6·10⁶`. -/
theorem log_le_sqrt_mul {T : ℝ} (hT : 6e6 ≤ T) : Real.log T ≤ 0.0298 * √T := by
  obtain ⟨hr, hsT, hTr⟩ := fourth_root_facts hT
  set r := √(√T)
  have hr0 : 0 < r := by linarith
  have h1 : Real.log T = 4 * Real.log r := by rw [hTr, Real.log_pow]; push_cast; ring
  have h2 := log_le_div_exp hr0
  have h4 : (2.718 : ℝ) ≤ rexp 1 := by have := Real.exp_one_gt_d9; linarith
  have h5 : r / rexp 1 ≤ r / 2.718 := div_le_div_of_nonneg_left hr0.le (by norm_num) h4
  have h6 : r / 2.718 ≤ 0.36792 * r := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  rw [h1, hsT]
  nlinarith

theorem logPlus_eq_zero {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1) : logPlus y = 0 :=
  max_eq_right (Real.log_nonpos hy0 hy)

theorem logPlus_le_log {y : ℝ} (hy : 1 ≤ y) : logPlus y = Real.log y :=
  max_eq_left (Real.log_nonneg hy)

theorem eta2'L1_le : eta2'L1 ≤ 5.5452 := by
  unfold eta2'L1; have := Real.log_two_lt_d9; linarith

theorem log_le_of_le_exp_bound {y : ℝ} (hy : 0 < y) {a b : ℝ} (h : y ≤ a) (ha : 0 < a)
    (hb : Real.log a ≤ b) : Real.log y ≤ b := (Real.log_le_log hy h).trans hb

/-- `log 16 ≤ 2.7726`. -/
theorem log_sixteen_le : Real.log 16 ≤ 2.7726 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9; push_cast; linarith

/-- `log a ≤ 2.7726 + (a/16 - 1)` (tangent line at `16`). -/
theorem log_le_tangent16 {a : ℝ} (ha : 0 < a) : Real.log a ≤ 2.7726 + (a / 16 - 1) := by
  have := Real.log_le_sub_one_of_pos (show 0 < a / 16 by positivity)
  rw [Real.log_div ha.ne' (by norm_num)] at this
  have := log_sixteen_le
  linarith

set_option maxHeartbeats 4000000 in
/-- (4.41) at the parameters of (6.49): at most `0.0139 x^{5/6}`. -/
theorem bound_4_41_first {T U : ℝ} {q : ℕ} (hT : 6e6 ≤ T) (hq : 1 ≤ q) (hqT : (q : ℝ) ≤ T / 6)
    (hU1 : 0.1924 * (T * √T) ≤ U) (hU2 : U ≤ 0.0786 * T ^ 2) :
    bound_4_41 (T ^ 3) q U ≤ 0.0139 * (T ^ 2 * √T) := by
  have hT0 : 0 < T := by linarith
  set S := √T with hS
  have hS0 : 2449 ≤ S := sqrt_ge_2449 hT
  have hTS : T = S ^ 2 := (Real.sq_sqrt hT0.le).symm
  have hlogT := log_le_sqrt_mul hT
  rw [← hS] at hlogT
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hU0 : 0 < U := lt_of_lt_of_le (by positivity) hU1
  obtain ⟨hc2a, hc2b⟩ := c₂_bounds
  obtain ⟨hc0a, hc0b⟩ := sqrt_c₀_bounds
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hη := eta2'L1_le
  have hη0 := eta2'L1_pos
  have he := Real.exp_one_lt_d9
  have he' := Real.exp_one_gt_d9
  have hx : T ^ 3 = S ^ 6 := by rw [hTS]; ring
  have hTS3 : T * √T = S ^ 3 := by rw [← hS, hTS]; ring
  rw [hTS3] at hU1
  replace hU2 : U ≤ 0.0786 * S ^ 4 := by
    calc U ≤ 0.0786 * T ^ 2 := hU2
      _ = 0.0786 * S ^ 4 := by rw [hTS]; ring
  replace hqT : (q : ℝ) ≤ S ^ 2 / 6 := by rw [← hTS]; exact hqT
  have hS5 : T ^ 2 * √T = S ^ 5 := by rw [← hS, hTS]; ring
  rw [hS5]
  unfold bound_4_41
  simp only []
  rw [hx]
  have hlogT' : Real.log (S ^ 2) ≤ 0.0298 * S := by rw [← hTS]; exact hlogT
  have hlogS : Real.log S ≤ 0.0149 * S := by
    rw [Real.log_pow] at hlogT'; push_cast at hlogT'; linarith
  have hS0' : 0 < S := by linarith
  -- `c₁ ≤ 1.0000001`.
  set c₁ := 1 + eta2'L1 / (S ^ 6 / U) with hc₁
  have hc1 : 1 ≤ c₁ := by have : 0 ≤ eta2'L1 / (S ^ 6 / U) := by positivity
                          linarith
  have hc1' : c₁ ≤ 1.0000001 := by
    have : eta2'L1 / (S ^ 6 / U) ≤ 1e-7 := by
      rw [div_le_iff₀ (by positivity)]
      have : S ^ 6 / U ≥ 12.72 * S ^ 2 := by
        rw [ge_iff_le, le_div_iff₀ hU0]
        have : 12.72 * S ^ 2 * U ≤ 12.72 * S ^ 2 * (0.0786 * S ^ 4) := by gcongr
        nlinarith [pow_pos hS0' 6]
      nlinarith [pow_pos hS0' 2]
    linarith
  have hsq1 : √(c₀ * c₁) ≤ 5.657 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have : c₀ = √c₀ ^ 2 := (Real.sq_sqrt (by norm_num [c₀])).symm
    have : √c₀ ^ 2 ≤ 5.6569 ^ 2 := pow_le_pow_left₀ (by linarith) hc0b 2
    have hc00 : (0 : ℝ) < c₀ := by norm_num [c₀]
    nlinarith
  have hA : 2 * √(c₀ * c₁) / π ≤ 3.6015 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hA0 : 0 ≤ 2 * √(c₀ * c₁) / π := by positivity
  -- Term a.
  have ta : 2 * √(c₀ * c₁) / π * U * Real.log (rexp 1 * S ^ 6 / U) ≤ 0.01297 * S ^ 5 := by
    have hl : Real.log (rexp 1 * S ^ 6 / U) ≤ 2.66 + 0.0447 * S := by
      have h1 : rexp 1 * S ^ 6 / U ≤ 14.13 * S ^ 3 := by
        rw [div_le_iff₀ hU0]
        have : 14.13 * S ^ 3 * (0.1924 * S ^ 3) ≤ 14.13 * S ^ 3 * U := by gcongr
        nlinarith [pow_pos hS0' 6]
      have h2 : Real.log (14.13 * S ^ 3) ≤ 2.66 + 0.0447 * S := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        have := log_le_tangent16 (show (0 : ℝ) < 14.13 by norm_num)
        push_cast; nlinarith
      exact (Real.log_le_log (by positivity) h1).trans h2
    have hl0 : 0 ≤ Real.log (rexp 1 * S ^ 6 / U) := Real.log_nonneg (by
      rw [le_div_iff₀ hU0]
      have h1 : S ^ 4 ≤ S ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have h2 : S ^ 6 ≤ rexp 1 * S ^ 6 := le_mul_of_one_le_left (by positivity) (by linarith)
      have h3 : 0 ≤ S ^ 4 := by positivity
      linarith)
    calc 2 * √(c₀ * c₁) / π * U * Real.log (rexp 1 * S ^ 6 / U)
        ≤ 3.6015 * (0.0786 * S ^ 4) * (2.66 + 0.0447 * S) := by gcongr
      _ ≤ 0.01297 * S ^ 5 := by nlinarith [pow_pos hS0' 4]
  -- Term b vanishes.
  have tb : 3 * c₁ / 2 * (S ^ 6 / q) * logPlus (U / (c₂ * S ^ 6 / q)) * Real.log (q / c₂) = 0 := by
    rw [logPlus_eq_zero (by positivity)]
    · ring
    rw [div_le_one (by positivity), le_div_iff₀ (by positivity)]
    have : U * q ≤ 0.0786 * S ^ 4 * (S ^ 2 / 6) := mul_le_mul hU2 hqT (by positivity) (by positivity)
    nlinarith [pow_pos hS0' 6]
  -- Term c.
  have tc : (2 * eta2'L1 / π * max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * S ^ 6))) *
      Real.log (S ^ 6) + 2 * √(c₀ * c₁) / π * (√3 + 1 / 2 * logPlus (U / (q / 2))) *
        Real.log (q / c₂)) * q ≤ 0.00004 * S ^ 5 := by
    have hmax : max 1 (Real.log (c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * S ^ 6))) = 1 := by
      refine max_eq_left ?_
      have harg : c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * S ^ 6) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have he3 : rexp 3 ≤ 20.1 := by
          calc rexp 3 = rexp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
            _ ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
            _ ≤ 20.1 := by norm_num
        have hq2 : (q : ℝ) ^ 2 ≤ S ^ 4 := by nlinarith
        have : c₀ * rexp 3 * q ^ 2 ≤ 32 * 20.1 * S ^ 4 := by
          have : c₀ = 32 := rfl
          rw [this]; gcongr
        have : 2 * (4 * π * eta2'L1 * S ^ 6) ≥ 2 * (4 * 3.1415 * 5.5 * S ^ 6) := by
          have : (5.5 : ℝ) ≤ eta2'L1 := by unfold eta2'L1; have := Real.log_two_gt_d9; linarith
          gcongr
        nlinarith [pow_pos hS0' 4, pow_pos hS0' 6]
      have := Real.log_le_sub_one_of_pos (show 0 < c₀ * rexp 3 * q ^ 2 / (4 * π * eta2'L1 * S ^ 6) by
        have : (0 : ℝ) < c₀ := by norm_num [c₀]
        positivity)
      linarith
    rw [hmax]
    have hlx : Real.log (S ^ 6) ≤ 0.0894 * S := by rw [Real.log_pow]; push_cast; linarith
    have hlp : logPlus (U / (q / 2)) ≤ 0.0596 * S := by
      unfold logPlus
      refine max_le ?_ (by positivity)
      have h1 : U / (q / 2) ≤ S ^ 4 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [pow_pos hS0' 4]
      calc Real.log (U / (q / 2)) ≤ Real.log (S ^ 4) := Real.log_le_log (by positivity) h1
        _ ≤ 0.0596 * S := by rw [Real.log_pow]; push_cast; linarith
    have hlq : Real.log (q / c₂) ≤ 0.0298 * S := by
      have h1 : (q : ℝ) / c₂ ≤ S ^ 2 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      exact (Real.log_le_log (by positivity) h1).trans hlogT'
    have hlq0 : 0 ≤ Real.log (q / c₂) := Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]; linarith)
    have hη' : 2 * eta2'L1 / π ≤ 3.5304 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have hs3 : √3 ≤ 1.7321 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc (2 * eta2'L1 / π * 1 * Real.log (S ^ 6) + 2 * √(c₀ * c₁) / π *
          (√3 + 1 / 2 * logPlus (U / (q / 2))) * Real.log (q / c₂)) * q
        ≤ (3.5304 * 1 * (0.0894 * S) + 3.6015 * (1.7321 + 1 / 2 * (0.0596 * S)) * (0.0298 * S)) *
            (S ^ 2 / 6) := by
          have : 0 ≤ Real.log (S ^ 6) := Real.log_nonneg (one_le_pow₀ (by linarith))
          have : 0 ≤ logPlus (U / (q / 2)) := logPlus_nonneg _
          gcongr
      _ ≤ 0.00004 * S ^ 5 := by nlinarith [pow_pos hS0' 3, pow_pos hS0' 4, pow_pos hS0' 5]
  -- Term d.
  have td : 3 * c₁ / 2 * √(2 * S ^ 6 / c₂) * Real.log (2 * S ^ 6 / c₂) ≤ 0.0001 * S ^ 5 := by
    have h1 : √(2 * S ^ 6 / c₂) ≤ 1.7325 * S ^ 3 := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by linarith)]
      nlinarith [pow_pos hS0' 6]
    have h2 : Real.log (2 * S ^ 6 / c₂) ≤ 1.11 + 0.0894 * S := by
      have : 2 * S ^ 6 / c₂ ≤ 3.0013 * S ^ 6 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hS0' 6]
      refine (Real.log_le_log (by positivity) this).trans ?_
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have := log_le_div_exp (show (0 : ℝ) < 3.0013 by norm_num)
      have : 3.0013 / rexp 1 ≤ 3.0013 / 2.7182818283 := div_le_div_of_nonneg_left (by norm_num)
        (by norm_num) he'.le
      push_cast; nlinarith
    have h0 : 0 ≤ Real.log (2 * S ^ 6 / c₂) := Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]; nlinarith [pow_pos hS0' 6])
    calc 3 * c₁ / 2 * √(2 * S ^ 6 / c₂) * Real.log (2 * S ^ 6 / c₂)
        ≤ 3 * 1.0000001 / 2 * (1.7325 * S ^ 3) * (1.11 + 0.0894 * S) := by gcongr
      _ ≤ 0.0001 * S ^ 5 := by nlinarith [pow_pos hS0' 3, pow_pos hS0' 4]
  -- Term e.
  have te : 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) * √(2 * S ^ 6) *
      Real.log (2 * rexp 1 * S ^ 6 / c₂) ≤ 0.00062 * S ^ 5 := by
    have hc32 : c₂ ^ (3 / 2 : ℝ) ≤ 0.545 := by
      have hc0 : 0 ≤ c₂ := by linarith
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hc0 (by norm_num), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      have : √c₂ ≤ 0.8165 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
      nlinarith [Real.sqrt_nonneg c₂]
    have h1 : 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) ≤ 11.8 := by
      rw [div_le_iff₀ (by positivity)]
      have : c₀ = 32 := rfl
      rw [this]
      have : (0 : ℝ) ≤ c₂ ^ (3 / 2 : ℝ) := by positivity
      nlinarith
    have h2 : √(2 * S ^ 6) ≤ 1.4143 * S ^ 3 := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [pow_pos hS0' 6]
    have h3 : Real.log (2 * rexp 1 * S ^ 6 / c₂) ≤ 2.1 + 0.0894 * S := by
      have : 2 * rexp 1 * S ^ 6 / c₂ ≤ 8.16 * S ^ 6 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith [pow_pos hS0' 6]
      refine (Real.log_le_log (by positivity) this).trans ?_
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      have h8 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8.16 / 8 by norm_num)
      rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
        Real.log_pow] at h8
      have := Real.log_two_lt_d9
      push_cast at h8; push_cast; nlinarith
    have h0 : 0 ≤ Real.log (2 * rexp 1 * S ^ 6 / c₂) := Real.log_nonneg (by
      rw [le_div_iff₀ (by linarith)]; nlinarith [pow_pos hS0' 6])
    have : (0 : ℝ) ≤ 20 * c₀ * c₂ ^ (3 / 2 : ℝ) / (3 * π ^ 2) := by
      have : (0 : ℝ) < c₀ := by norm_num [c₀]
      positivity
    calc _ ≤ 11.8 * (1.4143 * S ^ 3) * (2.1 + 0.0894 * S) := by gcongr
      _ ≤ 0.00062 * S ^ 5 := by nlinarith [pow_pos hS0' 3, pow_pos hS0' 4]
  have := pow_pos hS0' 5
  linarith

end TernaryGoldbach.MinorArcs
