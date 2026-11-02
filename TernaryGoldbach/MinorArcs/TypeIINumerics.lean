import Mathlib

/-!
# Numerical facts for [H, Lemma 5.2.3, (5.51)]
-/

open Real

namespace TernaryGoldbach.MinorArcs

/-- `e^{0.50136} ≥ 1.65096` (so `σ₀ = 0.30286 ≥ e^{-2·0.25068}/2`). -/
theorem exp_50136_ge : (1.65096 : ℝ) ≤ Real.exp 0.50136 := by
  have h1 : (1.648721 : ℝ) ≤ Real.exp (1 / 2) := by
    have he := Real.exp_one_gt_d9
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have h2 : (1.00136 : ℝ) ≤ Real.exp 0.00136 := by
    have := Real.add_one_le_exp (0.00136 : ℝ); linarith
  have : Real.exp 0.50136 = Real.exp (1 / 2) * Real.exp 0.00136 := by
    rw [← Real.exp_add]; norm_num
  rw [this]
  nlinarith

/-- `2 log z ≤ z - 1/z` for `z ≥ 1`. -/
theorem two_log_le_sub_inv {z : ℝ} (hz : 1 ≤ z) : 2 * Real.log z ≤ z - 1 / z := by
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => t - 1 / t - 2 * Real.log t)
      (1 + 1 / t ^ 2 - 2 / t) t := by
    intro t ht
    have h := ((hasDerivAt_id' t).sub ((hasDerivAt_inv ht.ne').const_mul 1)).sub
      ((Real.hasDerivAt_log ht.ne').const_mul 2)
    convert h using 1
    · funext s; simp [div_eq_mul_inv]
    · field_simp; ring
  have hmono := monotoneOn_of_deriv_nonneg (f := fun t => t - 1 / t - 2 * Real.log t)
    (convex_Ici 1)
    (fun u hu => (hderiv u (by linarith [Set.mem_Ici.1 hu])).continuousAt.continuousWithinAt)
    (fun u hu => by
      rw [interior_Ici] at hu
      exact (hderiv u (by linarith [Set.mem_Ioi.1 hu])).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [interior_Ici] at hu
      have hu1 : (1 : ℝ) < u := hu
      rw [(hderiv u (by linarith)).deriv]
      have : 1 + 1 / u ^ 2 - 2 / u = (1 - 1 / u) ^ 2 := by field_simp; ring
      rw [this]; positivity)
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hz) hz
  simp only [div_one, Real.log_one, mul_zero, sub_zero, sub_self] at this
  linarith

/-- `T(z) = (z² - 2/7)/(A(z² - 2/7) + 3/2) + (z²/2 - 2/7)/(A(z²/2 - 2/7) + 3/2)`. -/
noncomputable def Tz (A z : ℝ) : ℝ :=
  (z ^ 2 - 2 / 7) / (A * (z ^ 2 - 2 / 7) + 3 / 2) + (z ^ 2 / 2 - 2 / 7) / (A * (z ^ 2 / 2 - 2 / 7) + 3 / 2)

theorem frac_mono {A v v' : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ v) (hvv : v ≤ v') :
    v / (A * v + 3 / 2) ≤ v' / (A * v' + 3 / 2) := by
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]; nlinarith

theorem frac_anti {A A' v : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hv : 0 ≤ v) :
    v / (A' * v + 3 / 2) ≤ v / (A * v + 3 / 2) := by
  apply div_le_div_of_nonneg_left hv (by positivity); nlinarith

theorem Tz_mono {A A' z z' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hz : 1 ≤ z) (hzz : z ≤ z') :
    Tz A' z ≤ Tz A z' := by
  unfold Tz
  have h1 : z ^ 2 ≤ z' ^ 2 := by nlinarith
  have hz2 : 1 ≤ z ^ 2 := by nlinarith
  refine add_le_add ((frac_anti hA hAA (by linarith)).trans (frac_mono hA (by linarith) (by linarith)))
    ((frac_anti hA hAA (by linarith)).trans (frac_mono hA (by linarith) (by linarith)))

/-- `z - 1/z ≤ T(z)` for `1 ≤ z ≤ 13/5`, `1/2 ≤ A ≤ 1/2 + 10⁻⁴` (checked on a grid). -/
theorem sub_inv_le_Tz {A z : ℝ} (hA : 1 / 2 ≤ A) (hA2 : A ≤ 1 / 2 + 1 / 10000) (hz : 1 ≤ z)
    (hz2 : z ≤ 13 / 5) : z - 1 / z ≤ Tz A z := by
  have hmono : ∀ z₀ z₁ : ℝ, 1 ≤ z₀ → z₀ ≤ z → z ≤ z₁ →
      z₁ - 1 / z₁ ≤ Tz (1 / 2 + 1 / 10000) z₀ → z - 1 / z ≤ Tz A z := by
    intro z₀ z₁ h0 h1 h2 h3
    have hz0 : 0 < z := by linarith
    have : z - 1 / z ≤ z₁ - 1 / z₁ := by
      have : 1 / z₁ ≤ 1 / z := one_div_le_one_div_of_le hz0 h2
      linarith
    linarith [Tz_mono (by linarith : (0 : ℝ) ≤ A) hA2 h0 h1]
  rcases le_or_gt z (5 / 4) with h | h
  · exact hmono 1 (5 / 4) le_rfl hz h (by unfold Tz; norm_num)
  rcases le_or_gt z (3 / 2) with h' | h'
  · exact hmono (5 / 4) (3 / 2) (by norm_num) h.le h' (by unfold Tz; norm_num)
  rcases le_or_gt z (7 / 4) with h | h
  · exact hmono (3 / 2) (7 / 4) (by norm_num) h'.le h (by unfold Tz; norm_num)
  rcases le_or_gt z 2 with h' | h'
  · exact hmono (7 / 4) 2 (by norm_num) h.le h' (by unfold Tz; norm_num)
  rcases le_or_gt z (9 / 4) with h | h
  · exact hmono 2 (9 / 4) (by norm_num) h'.le h (by unfold Tz; norm_num)
  rcases le_or_gt z (19 / 8) with h' | h'
  · exact hmono (9 / 4) (19 / 8) (by norm_num) h.le h' (by unfold Tz; norm_num)
  rcases le_or_gt z (5 / 2) with h | h
  · exact hmono (19 / 8) (5 / 2) (by norm_num) h'.le h (by unfold Tz; norm_num)
  · exact hmono (5 / 2) (13 / 5) (by norm_num) h.le hz2 (by unfold Tz; norm_num)

end TernaryGoldbach.MinorArcs
