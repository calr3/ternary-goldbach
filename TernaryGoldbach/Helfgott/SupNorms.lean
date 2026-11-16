import TernaryGoldbach.Helfgott.Decay
import TernaryGoldbach.Helfgott.Eta2

/-!
# Sup-norm bounds for `η_*`

* `|η_*(t)| ≤ 1.414`, [H, (14.21)]: `|φ|_∞ ≤ 2/e` and `∫₀^∞ η₂(r) dr/r = 4 (log 2)²`
  (`abs_etaStar_le_1414`). The non-prime terms (14.51) use it.
* `|η_*(t)| ≤ 6.2`, cruder, from `η₂ ≤ 4 log 2`, `φ ≤ 2/e` and `supp η₂ ⊆ [1/4, 1]`
  (`abs_mellinConv_eta2_phi_le_const`). The base gap of the minor arcs uses it.

For `η₊`, `HHBound.lean` proves `|η₊(t)| ≤ 1.94` against [H, (14.3)]'s `1.079955`.

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

theorem continuousOn_eta2_div : ContinuousOn (fun r => eta2 r / r) (Set.Icc (1 / 4) 1) :=
  continuous_eta2.continuousOn.div continuousOn_id fun r hr => by
    show r ≠ 0; exact ne_of_gt (by linarith [hr.1])

/-- `∫₀^∞ η₂(r) dr/r = (∫ η₁(r) dr/r)² = 4 (log 2)²`. -/
theorem integral_eta2_div : ∫ r in Set.Ioi (0 : ℝ), eta2 r / r = 4 * Real.log 2 ^ 2 := by
  have hzero : ∀ r ∈ Set.Ioi (0 : ℝ) \ Set.Ioc (1 / 4) 1, eta2 r / r = 0 := by
    intro r hr
    have : r ∉ Set.Ioo (1 / 4 : ℝ) 1 := fun h => hr.2 ⟨h.1, h.2.le⟩
    rw [eta2_eq_zero this, zero_div]
  have hsub : Set.Ioc (1 / 4 : ℝ) 1 ⊆ Set.Ioi 0 := fun r hr =>
    show (0 : ℝ) < r by linarith [hr.1]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub hzero,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hint : IntervalIntegrable (fun r => eta2 r / r) volume (1 / 4) 1 :=
    (continuousOn_eta2_div.mono (by rw [Set.uIcc_of_le (by norm_num)])).intervalIntegrable
  have hint1 : IntervalIntegrable (fun r => eta2 r / r) volume (1 / 4) (1 / 2) := by
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc le_rfl (by norm_num)
  have hint2 : IntervalIntegrable (fun r => eta2 r / r) volume (1 / 2) 1 := by
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  -- `[1/4, 1/2]`: antiderivative `2 (log 4r)²`.
  have hL : ∫ r in (1 / 4 : ℝ)..(1 / 2), eta2 r / r = 2 * Real.log 2 ^ 2 := by
    have hcongr : Set.EqOn (fun r => eta2 r / r) (fun r => 4 * Real.log (4 * r) / r)
        (Set.uIcc (1 / 4) (1 / 2)) := by
      intro r hr
      rw [Set.uIcc_of_le (by norm_num)] at hr
      simp only [eta2_eq_left hr.1 hr.2]
    rw [intervalIntegral.integral_congr hcongr]
    have hderiv : ∀ r ∈ Set.uIcc (1 / 4 : ℝ) (1 / 2),
        HasDerivAt (fun r => 2 * Real.log (4 * r) ^ 2) (4 * Real.log (4 * r) / r) r := by
      intro r hr
      rw [Set.uIcc_of_le (by norm_num)] at hr
      have hr0 : r ≠ 0 := ne_of_gt (by linarith [hr.1])
      have h4 : (4 : ℝ) * r ≠ 0 := ne_of_gt (by linarith [hr.1])
      have hl : HasDerivAt (fun y : ℝ => Real.log (4 * y)) (4 / (4 * r)) r := by
        have := ((hasDerivAt_id' r).const_mul 4).log h4
        simpa using this
      have := (hl.fun_pow 2).const_mul 2
      convert this using 1
      field_simp
      ring
    have hcont : ContinuousOn (fun r => 4 * Real.log (4 * r) / r) (Set.uIcc (1 / 4) (1 / 2)) := by
      rw [Set.uIcc_of_le (by norm_num)]
      have hlog : ContinuousOn (fun r : ℝ => Real.log (4 * r)) (Set.Icc (1 / 4) (1 / 2)) :=
        ContinuousOn.log (by fun_prop) fun r hr => by
          show (4 : ℝ) * r ≠ 0; exact ne_of_gt (by linarith [hr.1])
      exact (continuousOn_const.mul hlog).div continuousOn_id fun r hr => by
        show r ≠ 0; exact ne_of_gt (by linarith [hr.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    norm_num
  -- `[1/2, 1]`: antiderivative `-2 (log r)²`.
  have hR : ∫ r in (1 / 2 : ℝ)..1, eta2 r / r = 2 * Real.log 2 ^ 2 := by
    have hcongr : Set.EqOn (fun r => eta2 r / r) (fun r => -4 * Real.log r / r)
        (Set.uIcc (1 / 2) 1) := by
      intro r hr
      rw [Set.uIcc_of_le (by norm_num)] at hr
      simp only [eta2_eq_right hr.1 hr.2]
    rw [intervalIntegral.integral_congr hcongr]
    have hderiv : ∀ r ∈ Set.uIcc (1 / 2 : ℝ) 1,
        HasDerivAt (fun r => -2 * Real.log r ^ 2) (-4 * Real.log r / r) r := by
      intro r hr
      rw [Set.uIcc_of_le (by norm_num)] at hr
      have hr0 : r ≠ 0 := ne_of_gt (by linarith [hr.1])
      have := ((Real.hasDerivAt_log hr0).fun_pow 2).const_mul (-2)
      convert this using 1
      field_simp
      ring
    have hcont : ContinuousOn (fun r => -4 * Real.log r / r) (Set.uIcc (1 / 2) 1) := by
      rw [Set.uIcc_of_le (by norm_num)]
      have hlog : ContinuousOn (fun r : ℝ => Real.log r) (Set.Icc (1 / 2) 1) :=
        ContinuousOn.log continuousOn_id fun r hr => by
          show r ≠ 0; exact ne_of_gt (by linarith [hr.1])
      exact (continuousOn_const.mul hlog).div continuousOn_id fun r hr => by
        show r ≠ 0; exact ne_of_gt (by linarith [hr.1])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
    have : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [this]
    norm_num
  rw [hL, hR]
  ring

theorem integrableOn_eta2_div : IntegrableOn (fun r => eta2 r / r) (Set.Ioi 0) := by
  refine IntegrableOn.of_forall_sdiff_eq_zero
    ((continuousOn_eta2_div.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
    measurableSet_Ioi ?_
  intro r hr
  have : r ∉ Set.Ioo (1 / 4 : ℝ) 1 := fun h => hr.2 ⟨h.1, h.2.le⟩
  rw [eta2_eq_zero this, zero_div]

/-- `φ(s) = s² e^{-s²/2} ≤ 2/e ≤ 0.73576`. -/
theorem phi_le_073576 (s : ℝ) : phi s ≤ 0.73576 := by
  unfold phi
  have hw := Real.add_one_le_exp (s ^ 2 / 2 - 1)
  have he : Real.exp (-1) ≤ 0.36788 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_gt_d9]
  have hprod : Real.exp (s ^ 2 / 2 - 1) * Real.exp (-s ^ 2 / 2) = Real.exp (-1) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := (Real.exp_pos (-s ^ 2 / 2)).le
  calc s ^ 2 * Real.exp (-s ^ 2 / 2) = 2 * ((s ^ 2 / 2) * Real.exp (-s ^ 2 / 2)) := by ring
    _ ≤ 2 * (Real.exp (s ^ 2 / 2 - 1) * Real.exp (-s ^ 2 / 2)) := by
        gcongr; linarith
    _ = 2 * Real.exp (-1) := by rw [hprod]
    _ ≤ 0.73576 := by linarith

/-- [H, (14.21)]: `|η_*|_∞ ≤ 1.414`, from `|φ|_∞ ≤ 2/e` and `∫ η₂(r) dr/r = 4 (log 2)²`. -/
theorem abs_mellinConv_eta2_phi_le_1414 (u : ℝ) : |mellinConv eta2 phi u| ≤ 1.414 := by
  have hbound : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ‖eta2 r * phi (u / r) / r‖ ≤ 0.73576 * (eta2 r / r) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun r (hr : 0 < r) => ?_
    have hphi0 : 0 ≤ phi (u / r) := by unfold phi; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := eta2_nonneg r; positivity)]
    rw [mul_div_assoc', mul_comm (0.73576 : ℝ), mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (phi_le_073576 _) hr.le)
      (eta2_nonneg r) |>.trans_eq (by ring)
  have h := norm_integral_le_of_norm_le (integrableOn_eta2_div.const_mul 0.73576) hbound
  rw [Real.norm_eq_abs, integral_const_mul, integral_eta2_div] at h
  unfold mellinConv
  refine h.trans ?_
  have := Real.log_two_lt_d9
  have := Real.log_two_gt_d9
  nlinarith

theorem abs_etaStar_le_1414 (t : ℝ) : |etaStar t| ≤ 1.414 :=
  abs_mellinConv_eta2_phi_le_1414 _

end TernaryGoldbach.Helfgott
