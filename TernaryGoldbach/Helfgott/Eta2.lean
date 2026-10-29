import TernaryGoldbach.Helfgott.Decay

/-!
# Explicit formulas for `η₂`

`η₂(t) = 4 log(4t)` on `[1/4, 1/2]`, `η₂(t) = -4 log t` on `[1/2, 1]`, and `|η₂|₁ = 1`
[B, (6.1)].

Proved, with no `sorry`.
-/

open Real MeasureTheory

namespace TernaryGoldbach.Helfgott

theorem eta2_eq_left {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 1 / 2) : eta2 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  have hl : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h4 : Real.log (4 * t) = Real.log 2 + Real.log (2 * t) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]; ring_nf
  have h40 : 0 ≤ Real.log (4 * t) := Real.log_nonneg (by linarith)
  unfold eta2
  rw [if_pos ht, abs_of_nonpos hl, max_eq_left (by linarith)]
  rw [h4]; ring

theorem eta2_eq_right {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 1) : eta2 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hl : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have h2t : Real.log (2 * t) = Real.log 2 + Real.log t := Real.log_mul (by norm_num) (by linarith)
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le h2
  unfold eta2
  rw [if_pos ht, abs_of_nonneg hl, max_eq_left (by linarith)]
  rw [h2t]; ring

theorem continuousOn_eta2 : ContinuousOn eta2 (Set.Icc (1 / 4) 1) := by
  have hc : ContinuousOn (fun t : ℝ => 4 * max (Real.log 2 - |Real.log (2 * t)|) 0)
      (Set.Icc (1 / 4) 1) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.sup ?_ continuousOn_const)
    refine continuousOn_const.sub (ContinuousOn.abs ?_)
    exact (continuousOn_const.mul continuousOn_id).log fun t ht => by
      simp only [Set.mem_Icc, id] at ht ⊢; nlinarith [ht.1]
  refine hc.congr fun t ht => ?_
  simp only [Set.mem_Icc] at ht
  simp only [eta2, if_pos (show (0:ℝ) < t by linarith)]

/-- `|η₂|₁ = 1`. -/
theorem integral_abs_eta2 : ∫ t, |eta2 t| = 1 := by
  have habs : (fun t => |eta2 t|) = (Set.Icc (1 / 4 : ℝ) 1).indicator eta2 := by
    funext t
    by_cases ht : t ∈ Set.Icc (1 / 4 : ℝ) 1
    · rw [Set.indicator_of_mem ht, abs_of_nonneg (eta2_nonneg t)]
    · rw [Set.indicator_of_not_mem ht, eta2_eq_zero (fun h => ht (Set.Ioo_subset_Icc_self h)),
        abs_zero]
  rw [habs, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hii : ∀ a b, 1 / 4 ≤ a → b ≤ 1 → a ≤ b → IntervalIntegrable eta2 volume a b := by
    intro a b ha hb hab
    refine (continuousOn_eta2.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab]; exact Set.Icc_subset_Icc ha hb
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hii _ _ le_rfl (by norm_num) (by norm_num)) (hii _ _ (by norm_num) le_rfl (by norm_num))]
  have hL : ∫ t in (1 / 4 : ℝ)..1 / 2, eta2 t = 2 * Real.log 2 - 1 := by
    rw [intervalIntegral.integral_congr (g := fun t => 4 * Real.log (4 * t)) fun t ht => by
      rw [Set.uIcc_of_le (by norm_num)] at ht; exact eta2_eq_left ht.1 ht.2]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t => Real.log t) (by norm_num : (4:ℝ) ≠ 0),
      integral_log (by rw [Set.uIcc_of_le (by norm_num)]; norm_num)]
    norm_num
    ring
  have hR : ∫ t in (1 / 2 : ℝ)..1, eta2 t = 2 - 2 * Real.log 2 := by
    rw [intervalIntegral.integral_congr (g := fun t => -4 * Real.log t) fun t ht => by
      rw [Set.uIcc_of_le (by norm_num)] at ht; exact eta2_eq_right ht.1 ht.2]
    rw [intervalIntegral.integral_const_mul,
      integral_log (by rw [Set.uIcc_of_le (by norm_num)]; norm_num)]
    simp only [Real.log_one, one_div, Real.log_inv]
    ring
  rw [hL, hR]; ring

end TernaryGoldbach.Helfgott
