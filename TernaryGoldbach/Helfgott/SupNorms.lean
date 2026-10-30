import TernaryGoldbach.Helfgott.Decay

/-!
# Crude sup-norm bounds for `η₊` and `η_*`

Helfgott proves `|η₊|_∞ ≤ 1.079955` and `|η_*|_∞ ≤ 1.414` [H, (7.3), (7.19)].  The final
inequality of [H, §7.4] has so much room that much cruder bounds suffice, and these are easy:

* `|η₊(t)| ≤ 400`, from `|h₂₀₀| ≤ 2000/π` and `t e^{-t²/2} ≤ e^{-1/2}`;
* `|η_*(t)| ≤ 6.2`, from `η₂ ≤ 4 log 2`, `φ ≤ 2/e` and `supp η₂ ⊆ [1/4, 1]`.

Proved, with no `sorry`.
-/

open MeasureTheory

namespace TernaryGoldbach.Helfgott

/-- `t e^{-t²/2} ≤ 1/1.625` (the true maximum is `e^{-1/2} ≈ 0.6065`). -/
theorem mul_exp_neg_sq_half_le (t : ℝ) : t * Real.exp (-(1 / 2) * t ^ 2) ≤ 1 / 1.625 := by
  have h1 := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
  have h2 := Real.add_one_le_exp ((t ^ 2 - 1) / 2)
  have hsplit : Real.exp (t ^ 2 / 2) = Real.exp (1 / 2) * Real.exp ((t ^ 2 - 1) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hge : 1.625 * t ≤ Real.exp (t ^ 2 / 2) := by
    rw [hsplit]
    have hpos : 0 ≤ (t ^ 2 - 1) / 2 + 1 := by nlinarith
    calc 1.625 * t ≤ 1.625 * ((t ^ 2 - 1) / 2 + 1) := by nlinarith [sq_nonneg (t - 1)]
      _ ≤ Real.exp (1 / 2) * Real.exp ((t ^ 2 - 1) / 2) := by
          apply mul_le_mul (by linarith) h2 hpos (Real.exp_pos _).le
  have hexp : Real.exp (-(1 / 2) * t ^ 2) = (Real.exp (t ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hexp, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem abs_etaPlus_le_400 {t : ℝ} (ht : 0 ≤ t) : |etaPlus t| ≤ 400 := by
  have h := abs_etaPlus_le ht
  rw [pow_one, mul_assoc] at h
  have h2 := mul_exp_neg_sq_half_le t
  have hpi := Real.pi_gt_d2
  have hC : 10 * 200 / Real.pi ≤ 2000 / 3.14 := by
    rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]; nlinarith
  calc |etaPlus t| ≤ 10 * 200 / Real.pi * (t * Real.exp (-(1 / 2) * t ^ 2)) := h
    _ ≤ 2000 / 3.14 * (1 / 1.625) := by
        apply mul_le_mul hC h2 (by positivity) (by norm_num)
    _ ≤ 400 := by norm_num

theorem eta2_le_four_log_two (r : ℝ) : eta2 r ≤ 4 * 0.6931471808 := by
  unfold eta2
  have := Real.log_two_lt_d9
  split_ifs
  · have : max (Real.log 2 - |Real.log (2 * r)|) 0 ≤ Real.log 2 :=
      max_le (by linarith [abs_nonneg (Real.log (2 * r))]) (Real.log_nonneg (by norm_num))
    linarith
  · norm_num

/-- `φ(s) = s² e^{-s²/2} ≤ 2/e ≤ 0.7358`. -/
theorem phi_le_two_div_e (s : ℝ) : phi s ≤ 0.7358 := by
  unfold phi
  have hw := Real.add_one_le_exp (s ^ 2 / 2 - 1)
  have he : Real.exp (-1) ≤ 0.3679 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_gt_d9]
  have hprod : Real.exp (s ^ 2 / 2 - 1) * Real.exp (-s ^ 2 / 2) = Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := (Real.exp_pos (-s ^ 2 / 2)).le
  calc s ^ 2 * Real.exp (-s ^ 2 / 2) = 2 * ((s ^ 2 / 2) * Real.exp (-s ^ 2 / 2)) := by ring
    _ ≤ 2 * (Real.exp (s ^ 2 / 2 - 1) * Real.exp (-s ^ 2 / 2)) := by
        gcongr; linarith
    _ = 2 * Real.exp (-1) := by rw [hprod]
    _ ≤ 0.7358 := by linarith

theorem abs_mellinConv_eta2_phi_le_const (u : ℝ) : |mellinConv eta2 phi u| ≤ 6.2 := by
  set K : ℝ := 4 * 0.6931471808 * 0.7358 * 4
  have hK : 0 ≤ K := by norm_num
  set g := (Set.Ioo (1/4 : ℝ) 1).indicator fun _ => K
  have hgint : Integrable g := by
    refine (integrable_indicator_iff measurableSet_Ioo).2 ?_
    exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hbound : ∀ r, ‖eta2 r * phi (u / r) / r‖ ≤ g r := by
    intro r
    by_cases hr : r ∈ Set.Ioo (1/4 : ℝ) 1
    · simp only [g, Set.indicator_of_mem hr]
      obtain ⟨h1, h2⟩ := hr
      have hr0 : 0 < r := by linarith
      have hphi0 : 0 ≤ phi (u / r) := by unfold phi; positivity
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (eta2_nonneg r),
        abs_of_nonneg hphi0, abs_of_pos hr0, div_le_iff₀ hr0]
      calc eta2 r * phi (u / r) ≤ 4 * 0.6931471808 * 0.7358 :=
            mul_le_mul (eta2_le_four_log_two r) (phi_le_two_div_e _) hphi0 (by norm_num)
        _ ≤ K * r := by simp only [K]; nlinarith
    · rw [eta2_eq_zero hr, zero_mul, zero_div, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hK) r
  have := norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi 0)) hgint.integrableOn
    (Filter.Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at this
  refine (this.trans (setIntegral_le_integral hgint
    (Filter.Eventually.of_forall fun r => Set.indicator_nonneg (fun _ _ => hK) r))).trans ?_
  rw [integral_indicator measurableSet_Ioo, setIntegral_const,
    Real.volume_real_Ioo_of_le (by norm_num), smul_eq_mul]
  simp only [K]
  norm_num

theorem abs_etaStar_le_const (t : ℝ) : |etaStar t| ≤ 6.2 :=
  abs_mellinConv_eta2_phi_le_const _

end TernaryGoldbach.Helfgott
