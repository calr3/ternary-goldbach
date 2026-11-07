import TernaryGoldbach.Explicit.PsiRange

/-!
# `|ψ(x) − x| ≤ 4.91·10⁻⁷ x + 1145 √x + 4.2·10¹⁰` for `x ≥ 10¹⁷`, with RH up to `10⁸`

From `rh_upto_1e8` (`PlattGRH` at `q = 1`) through
`tsum_gsm_leH` at `H = 10⁸`: `δ = 7/H`, `K₀ = 7`, `y₀ = 10¹⁰`.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

theorem LineB2H_plateau8_le {a x : ℝ} (ha : |a| ≤ 49 / 1e8) (hx : 1e17 ≤ x) :
    LineB2H a (Real.log (1e10 / x)) (7 / 1e8) 1e8 ≤ 1143 := by
  unfold LineB2H
  have he1 : Real.exp ((7 / 1e8 : ℝ) ^ 2 / 2) ≤ 1.000001 := by
    have h := exp_small_le (t := (7 / 1e8 : ℝ) ^ 2 / 2) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he2 : Real.exp (a / 2) ≤ 1.000001 := by
    have h1 : a / 2 ≤ |a| := by cases abs_cases a <;> linarith
    have h := exp_small_le (t := |a|) (abs_nonneg a) (by norm_num at ha ⊢; linarith)
    have := Real.exp_le_exp.2 h1
    norm_num at ha h ⊢; linarith
  have he3 := exp_half_log_le hx
  have hsub : Finset.range (JlH 6 1e8) ⊆ Finset.range (JlH 6 3e10) := by
    refine Finset.range_mono ?_
    unfold JlH
    exact Nat.add_le_add_right (Nat.floor_mono (by norm_num)) 1
  have hS : ∑ m ∈ Finset.range (JlH 6 1e8), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))) ≤ 571 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => mul_nonneg
      (div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le)
      (one_div_nonneg.2 (le_trans (by norm_num) (le_max_left _ _)))) window_sum_le
  have hS0 : 0 ≤ ∑ m ∈ Finset.range (JlH 6 1e8), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))) :=
    Finset.sum_nonneg fun m _ => mul_nonneg
      (div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le)
      (one_div_nonneg.2 (le_trans (by norm_num) (le_max_left _ _)))
  calc (Real.exp ((7 / 1e8 : ℝ) ^ 2 / 2) * (Real.exp (a / 2) + Real.exp (Real.log (1e10 / x) / 2))) *
        (2 * ∑ m ∈ Finset.range (JlH 6 1e8), Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
          Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))))
      ≤ (1.000001 * (1.000001 + 3.17e-4)) * (2 * 571) := by gcongr
    _ ≤ 1143 := by norm_num

theorem Vg_plateau8_le {a x : ℝ} (ha : |a| ≤ 49 / 1e8) (hx : 1e17 ≤ x) :
    x ^ (-(1 / 2) : ℝ) * Vg a (Real.log (1e10 / x)) (7 / 1e8) / (2 * π) ≤ 3.7e4 := by
  have hx0 : 0 < x := by linarith
  have hsx : x ^ (-(1 / 2) : ℝ) = 1 / √x := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
  have hb : Real.exp (-(Real.log (1e10 / x) / 2)) = √x / 1e5 := by
    have h1 : Real.exp (-(Real.log (1e10 / x) / 2)) = √(x / 1e10) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
      congr 1
      rw [show x / 1e10 = (1e10 / x)⁻¹ by field_simp, Real.log_inv]; ring
    rw [h1, Real.sqrt_div' _ (by norm_num), show (1e10 : ℝ) = (1e5) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hS : 3.16e8 ≤ √x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; norm_num; linarith
  have hS0 : 0 < √x := by linarith
  have hc1 : 2 / Real.log 2 + 4.8 ≤ 7.6856 := by
    have := Real.log_two_gt_d9
    have : 2 / Real.log 2 ≤ 2 / 0.6931 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    have : (2 : ℝ) / 0.6931 ≤ 2.8856 := by norm_num
    linarith
  have hc10 : 0 ≤ 2 / Real.log 2 + 4.8 := by have := Real.log_pos (by norm_num : (1:ℝ) < 2); positivity
  have hδe : Real.exp ((7 / 1e8 : ℝ) ^ 2 / 8) ≤ 1.000001 := by
    have h := exp_small_le (t := (7 / 1e8 : ℝ) ^ 2 / 8) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have hae : Real.exp (-(a / 2)) ≤ 1.000001 := by
    have h1 : -(a / 2) ≤ |a| := by cases abs_cases a <;> linarith
    have h := exp_small_le (t := |a|) (abs_nonneg a) (by norm_num at ha ⊢; linarith)
    have := Real.exp_le_exp.2 h1
    norm_num at ha h ⊢; linarith
  have hpi : 2.5066 ≤ √(2 * π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have := Real.pi_gt_d6; nlinarith
  unfold Vg
  rw [hsx, hb]
  set c₁ := 2 / Real.log 2 + 4.8
  set E := Real.exp ((7 / 1e8 : ℝ) ^ 2 / 8)
  set A := Real.exp (-(a / 2))
  set P := √(2 * π) with hP
  have hP2 : P * P = 2 * π := Real.mul_self_sqrt (by positivity)
  have e : 1 / √x * (c₁ * 82.6 * E * (A + √x / 1e5) * (P / (7 / 1e8))) / (2 * π) =
      (c₁ * 82.6 * E * (1e8 / 7)) * (1 / P) * (A / √x + 1e-5) := by
    rw [← hP2]
    field_simp
    ring
  rw [e]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have h1 : c₁ * 82.6 * E * (1e8 / 7) ≤ 7.6856 * 82.6 * 1.000001 * (1e8 / 7) := by gcongr
  have h2 : 1 / √(2 * π) ≤ 1 / 2.5066 := one_div_le_one_div_of_le (by norm_num) hpi
  have h3 : A / √x + 1e-5 ≤ 1.000001 / 3.16e8 + 1e-5 := by
    have : A / √x ≤ 1.000001 / 3.16e8 := div_le_div₀ (by norm_num) hae (by norm_num) hS
    linarith
  calc (c₁ * 82.6 * E * (1e8 / 7)) * (1 / √(2 * π)) * (A / √x + 1e-5)
      ≤ (7.6856 * 82.6 * 1.000001 * (1e8 / 7)) * (1 / 2.5066) * (1.000001 / 3.16e8 + 1e-5) := by
        gcongr
    _ ≤ 3.7e4 := by norm_num

theorem ErrGH_plateau8_le {a x : ℝ} (ha : |a| ≤ 49 / 1e8) (hx : 1e17 ≤ x) :
    ErrGH a (Real.log (1e10 / x)) (7 / 1e8) 1e8 x ≤ 1143 * √x + 2.48e-10 * x + 3.7e4 := by
  unfold ErrGH
  have h1 := LineB2H_plateau8_le ha hx
  have h2 : TailBH a (7 / 1e8) 1e8 ≤ 2.48e-10 := by
    refine (TailBH_1e8_le (by norm_num at ha ⊢; linarith) (by norm_num) (by norm_num)).trans ?_
    rw [show -((7 / 1e8 : ℝ) ^ 2 * (1e8 : ℝ) ^ 2 / 2) = -24.5 by norm_num]
    have := exp_neg245_le; linarith
  have h3 := Vg_plateau8_le ha hx
  have hx0 : 0 ≤ x := by linarith
  have := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg x)
  have := mul_le_mul_of_nonneg_left h2 hx0
  nlinarith

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **`|ψ(x) − x| ≤ 4.91·10⁻⁷ x + 1145 √x + 4.2·10¹⁰`** for `x ≥ 10¹⁷`, with RH up to `10⁸`. -/
theorem psi_plateau8 {x : ℝ} (hx : 1e17 ≤ x) : |psiR x - x| ≤ 4.91e-7 * x + 1145 * √x + 4.2e10 := by
  have hx0 : 0 < x := by linarith
  set δ : ℝ := 7 / 1e8 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; norm_num
  have hKd : (7 : ℝ) * δ = 49 / 1e8 := by rw [hδ]; norm_num
  have hK2 : -((7 : ℝ) ^ 2 / 2) = -24.5 := by norm_num
  have he32 := exp_neg245_le
  have he32' : 0 < Real.exp (-24.5) := Real.exp_pos _
  have hsx := Real.sqrt_nonneg x
  -- upper
  have hK1 : 2 * Real.exp (-((7 : ℝ) ^ 2 / 2)) < 1 := by rw [hK2]; linarith
  have hYx : 1e10 * Real.exp (7 * δ) ≤ x := by
    rw [hKd]
    have := exp_small_le (t := (49 / 1e8 : ℝ)) (by norm_num) (by norm_num)
    nlinarith
  have hb0 : Real.log (1e10 / x) ≤ 0 := Real.log_nonpos (by positivity)
    ((div_le_one hx0).2 (by linarith))
  have hU := psi_upper_of_err hδ0 (by norm_num : (0 : ℝ) ≤ 7) hK1 (by norm_num : (0 : ℝ) < 1e10)
    (by linarith) hYx (tsum_gsm_leH (by norm_num) rh_upto_1e8 hδ0 (hb0.trans (by positivity)) hb0
      (by linarith))
  rw [hK2, hKd] at hU
  have hEu := ErrGH_plateau8_le (a := 49 / 1e8) (by rw [abs_of_pos (by norm_num)]) hx
  rw [← hKd] at hEu
  rw [hKd] at hEu
  have hexp1 : Real.exp (δ ^ 2 / 2 + 49 / 1e8) ≤ 1 + 4.9001e-7 := by
    have h := exp_small_le2 (t := δ ^ 2 / 2 + 49 / 1e8) (by positivity) (by rw [hδ]; norm_num)
    rw [hδ] at h ⊢; norm_num at h ⊢; linarith
  have hexp2 : Real.exp (49 / 1e8) ≤ 1.000001 := by
    have := exp_small_le (t := (49 / 1e8 : ℝ)) (by norm_num) (by norm_num); norm_num at this ⊢; linarith
  have hden : 1 / (1 - 2 * Real.exp (-24.5)) ≤ 1 + 4.7e-11 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hup : psiR x ≤ x + 4.91e-7 * x + 1145 * √x + 4.2e10 := by
    have hnum : Real.exp (δ ^ 2 / 2 + 49 / 1e8) * x + ErrGH (49 / 1e8) (Real.log (1e10 / x)) δ 1e8 x ≤
        (1 + 4.9001e-7) * x + (1143 * √x + 2.48e-10 * x + 3.7e4) := by
      have := mul_le_mul_of_nonneg_right hexp1 hx0.le; linarith
    have hnum0 : 0 ≤ (1 + 4.9001e-7) * x + (1143 * √x + 2.48e-10 * x + 3.7e4) := by positivity
    have hd0 : 0 < 1 - 2 * Real.exp (-24.5) := by linarith
    have hq : (Real.exp (δ ^ 2 / 2 + 49 / 1e8) * x + ErrGH (49 / 1e8) (Real.log (1e10 / x)) δ 1e8 x) /
        (1 - 2 * Real.exp (-24.5)) ≤
          ((1 + 4.9001e-7) * x + (1143 * √x + 2.48e-10 * x + 3.7e4)) * (1 + 4.7e-11) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul hnum hden (by positivity) hnum0
    have h4 : 4 * (1e10 * Real.exp (49 / 1e8)) ≤ 4.0001e10 := by nlinarith
    nlinarith
  -- lower
  have hb : Real.log (1e10 / x) ≤ -(7 * δ) := by
    rw [hKd]
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1e10 / x by positivity)
    have : 1e10 / x ≤ 1e-7 := by rw [div_le_iff₀ hx0]; linarith
    linarith
  have hL := psi_lower_of_err hδ0 (by rw [hδ]; norm_num) (by rw [hδ]; norm_num) (by norm_num : (0 : ℝ) < 1e10)
    (by linarith) hb (tsum_gsm_leH (by norm_num) rh_upto_1e8 hδ0 hb (hb.trans (by rw [hKd]; norm_num))
      (by linarith))
  rw [hK2, hKd] at hL
  have hEl := ErrGH_plateau8_le (a := -(49 / 1e8)) (by rw [abs_neg, abs_of_pos (by norm_num)]) hx
  have hexp3 : 1 - 49 / 1e8 ≤ Real.exp (-(49 / 1e8)) := by
    have := Real.add_one_le_exp (-(49 / 1e8 : ℝ)); linarith
  have hlo : x - 4.91e-7 * x - 1145 * √x - 4.2e10 ≤ psiR x := by
    have := mul_le_mul_of_nonneg_right hexp3 hx0.le
    have : 4 * x * Real.exp (-24.5) ≤ 4 * x * 2.31e-11 := by
      have := mul_le_mul_of_nonneg_left he32 (by positivity : (0:ℝ) ≤ 4 * x); linarith
    nlinarith
  rw [abs_le]; constructor <;> linarith

end TernaryGoldbach.Explicit
