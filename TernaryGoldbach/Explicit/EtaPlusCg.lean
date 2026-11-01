import TernaryGoldbach.Explicit.EtaPlusMellin

/-!
# `C_g = ∫|g| = 92 e^{−1/2} − 12 e^{3/2} ≤ 2.03`

`g(u) = h(e^u)`, `h(t) = t²(2−t)³ e^{t−1/2}` on `[0, 2]`, so `∫|g| = ∫₀² t(2−t)³ e^{t−1/2} dt`, with
antiderivative `(−t⁴ + 10t³ − 42t² + 92t − 92) e^{t−1/2}`.
-/

open Complex MeasureTheory Set

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.MajorArcs (gC gL)
open TernaryGoldbach.Helfgott (hBase)

theorem hBase_nonneg (t : ℝ) : 0 ≤ hBase t := by
  unfold hBase
  split_ifs with h
  · have : 0 ≤ 2 - t := by linarith [h.2]
    have : 0 ≤ t := h.1
    positivity
  · exact le_rfl

theorem Cg_eq_integral : Cg = ∫ t in (0:ℝ)..2, t * (2 - t) ^ 3 * Real.exp (t - 1 / 2) := by
  have e1 : ∀ u, ‖gC u‖ = Real.exp u • (hBase (Real.exp u) / Real.exp u) := by
    intro u
    rw [gC, Complex.norm_real, Real.norm_eq_abs, gL, abs_of_nonneg (hBase_nonneg _), smul_eq_mul]
    field_simp
  rw [Cg]
  simp_rw [e1]
  rw [MeasureTheory.integral_comp_exp (fun y => hBase y / y)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t (ht : 0 < t) => MajorArcs.hBase_div_eq ht),
    setIntegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by norm_num)]
  have hs : Ioi (0:ℝ) ∩ Icc 0 2 = Ioc 0 2 := by
    ext t
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, (le_of_lt h1), h3⟩
  rw [hs]

theorem Cg_eq : Cg = 92 * Real.exp (-(1 / 2)) - 12 * Real.exp (3 / 2) := by
  rw [Cg_eq_integral]
  set F : ℝ → ℝ := fun t => (-t ^ 4 + 10 * t ^ 3 - 42 * t ^ 2 + 92 * t - 92) * Real.exp (t - 1 / 2)
  have hF : ∀ t, HasDerivAt F (t * (2 - t) ^ 3 * Real.exp (t - 1 / 2)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -t ^ 4 + 10 * t ^ 3 - 42 * t ^ 2 + 92 * t - 92)
        (-(4 * t ^ 3) + 10 * (3 * t ^ 2) - 42 * (2 * t) + 92) t := by
      have h4 := hasDerivAt_pow 4 t
      have h3 := (hasDerivAt_pow 3 t).const_mul (10:ℝ)
      have h2 := (hasDerivAt_pow 2 t).const_mul (42:ℝ)
      have h1 := (hasDerivAt_id t).const_mul (92:ℝ)
      have := (((h4.neg.add h3).sub h2).add h1).sub_const (92:ℝ)
      convert this using 1
      · ext u; simp
      · simp
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (t - 1 / 2)) (Real.exp (t - 1 / 2)) t := by
      have := ((hasDerivAt_id t).sub_const (1 / 2 : ℝ)).exp
      simpa using this
    convert h1.mul h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
    ((by fun_prop : Continuous fun t : ℝ => t * (2 - t) ^ 3 * Real.exp (t - 1 / 2)).intervalIntegrable _ _)]
  simp only [F]
  norm_num
  ring

theorem Cg_le : Cg ≤ 2.03 := by
  rw [Cg_eq]
  have hs : (1.648721 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 / 2 by norm_num) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at this ⊢; linarith
  have he := Real.exp_one_gt_d9
  have h32 : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have hm : Real.exp (-(1 / 2)) = (Real.exp (1 / 2))⁻¹ := Real.exp_neg _
  rw [h32, hm]
  have hpos : 0 < Real.exp (1 / 2) := Real.exp_pos _
  have hinv : (Real.exp (1 / 2))⁻¹ ≤ 1 / 1.648721 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs
  nlinarith

theorem two_aH_le : 2 * aH ≤ 63.662 := by
  have h := two_pi_aH
  have hpi := Real.pi_gt_d6
  have ha := aH_pos
  nlinarith

theorem cA_le : Cg * (2 * aH) ≤ 129.24 := by
  have := Cg_le; have := two_aH_le; have := Cg_nonneg; have := aH_pos
  nlinarith

theorem cA_nonneg : 0 ≤ Cg * (2 * aH) := by
  have := Cg_nonneg; have := aH_pos; positivity

theorem cA_sq_le : (Cg * (2 * aH)) ^ 2 ≤ 16703 := by
  have := cA_le; have := cA_nonneg; nlinarith

end TernaryGoldbach.Explicit
