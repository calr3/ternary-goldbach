import TernaryGoldbach.Explicit.ZeroSumBound

/-!
# `|G_δ(s)| ≤ 300 e^{−θ_δ|ℑs|}` on `−3/2 ≤ ℜs ≤ 1`

As `norm_G_uniform`, with `r^p ≤ r^{−1/2} + r²` (`−1/2 ≤ p ≤ 2`) and `br ≤ b²/c + (c/4)r²`, so the Gaussian
integral is at most `e^{b²/c} ((c/4)^{−1/4} Γ(1/4)/2 + (c/4)^{−3/2} Γ(3/2)/2)`. Needed for `G_δ(s − 1)` on
`ℜs = −1/2` (the smoothing `η₊`).
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace TernaryGoldbach.Explicit

theorem integral_rpow_exp_quad_le_ext {p c b : ℝ} (hp : -1 / 2 ≤ p) (hp2 : p ≤ 2) (hc : 0 < c) :
    ∫ r in Ioi (0:ℝ), r ^ p * Real.exp (-(c / 2) * r ^ 2 + b * r) ≤
      Real.exp (b ^ 2 / c) * ((c / 4) ^ (-(1 / 4 : ℝ)) * (1 / 2) * Real.Gamma (1 / 4) +
        (c / 4) ^ (-(3 / 2 : ℝ)) * (1 / 2) * Real.Gamma (3 / 2)) := by
  have hc4 : 0 < c / 4 := by positivity
  have i1 := integrableOn_rpow_mul_exp_neg_rpow (p := 2) (s := -1 / 2) (by norm_num) (by norm_num)
  have j1 : IntegrableOn (fun r : ℝ => r ^ (-1 / 2 : ℝ) * Real.exp (-(c / 4) * r ^ (2:ℝ))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_quad (p := -1 / 2) (a := c / 4) (b := 0) (by norm_num) hc4
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp [Real.rpow_two]
  have j2 : IntegrableOn (fun r : ℝ => r ^ (2 : ℝ) * Real.exp (-(c / 4) * r ^ (2:ℝ))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_quad (p := 2) (a := c / 4) (b := 0) (by norm_num) hc4
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
    simp [Real.rpow_two]
  have hL := integrableOn_rpow_mul_exp_quad (p := p) (a := c / 2) (b := b) (by linarith) (half_pos hc)
  set R : ℝ → ℝ := fun r => Real.exp (b ^ 2 / c) * (r ^ (-1 / 2 : ℝ) * Real.exp (-(c / 4) * r ^ (2:ℝ)) +
    r ^ (2 : ℝ) * Real.exp (-(c / 4) * r ^ (2:ℝ))) with hR
  have iR : IntegrableOn R (Ioi 0) := (j1.add j2).const_mul _
  have hpt : ∀ r ∈ Ioi (0:ℝ), r ^ p * Real.exp (-(c / 2) * r ^ 2 + b * r) ≤ R r := by
    intro r (hr : 0 < r)
    have hrp : r ^ p ≤ r ^ (-1 / 2 : ℝ) + r ^ (2 : ℝ) := by
      rcases le_total r 1 with h | h
      · have := Real.rpow_le_rpow_of_exponent_ge hr h hp
        have := Real.rpow_nonneg hr.le (2:ℝ); linarith
      · have := Real.rpow_le_rpow_of_exponent_le h hp2
        have := Real.rpow_nonneg hr.le (-1 / 2 : ℝ); linarith
    have hex : Real.exp (-(c / 2) * r ^ 2 + b * r) ≤ Real.exp (b ^ 2 / c) * Real.exp (-(c / 4) * r ^ (2:ℝ)) := by
      rw [← Real.exp_add, Real.rpow_two]
      apply Real.exp_le_exp.2
      have h0 : 0 ≤ (c / 2 * r - b) ^ 2 / c := by positivity
      have e : (c / 2 * r - b) ^ 2 / c = c / 4 * r ^ 2 - b * r + b ^ 2 / c := by
        field_simp; ring
      linarith
    simp only [hR]
    calc r ^ p * Real.exp (-(c / 2) * r ^ 2 + b * r)
        ≤ (r ^ (-1 / 2 : ℝ) + r ^ (2 : ℝ)) * (Real.exp (b ^ 2 / c) * Real.exp (-(c / 4) * r ^ (2:ℝ))) :=
          mul_le_mul hrp hex (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  refine (setIntegral_mono_on hL iR measurableSet_Ioi hpt).trans (le_of_eq ?_)
  simp only [hR]
  rw [integral_const_mul, integral_add j1 j2,
    _root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hc4,
    _root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hc4]
  norm_num

theorem exp_36533_le : Real.exp 3.6533 ≤ 38.7 := by
  have h := Real.exp_bound' (x := 0.6533) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have he := Real.exp_one_lt_d9
  have e : Real.exp 3.6533 = Real.exp 1 ^ 3 * Real.exp 0.6533 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  rw [e]
  have h3 : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 3
  have h0 := Real.exp_pos 0.6533
  nlinarith [pow_pos (Real.exp_pos 1) 3]

/-- **Uniform bound on `−3/2 ≤ ℜs ≤ 1`**: `|G_δ(s)| ≤ 300 e^{−θ_δ|ℑs|}`. -/
theorem norm_G_uniform_ext (s : ℂ) (δ : ℝ) (hs0 : -3 / 2 ≤ s.re) (hs1 : s.re ≤ 1) :
    ‖Gr s δ 0‖ ≤ 300 * Real.exp (-(thetaD δ * |s.im|)) := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  set θ0 := thetaD δ with hθdef
  have hθ0 : 0 < θ0 := thetaD_pos δ
  have hθ1 : θ0 ≤ 0.28 := thetaD_le δ
  have hδθ : |δ| * θ0 ≤ 0.28 := abs_mul_thetaD_le δ
  set θ : ℝ := if 0 ≤ s.im then θ0 else -θ0 with hθ
  have habs : |θ| = θ0 := by rw [hθ]; split_ifs <;> simp [abs_of_pos hθ0]
  have hsg : 0 ≤ θ * s.im := by
    rw [hθ]; split_ifs with h
    · exact mul_nonneg hθ0.le h
    · push Not at h; nlinarith
  have hcos2 : Real.cos (2 * θ) = Real.cos (2 * θ0) := by
    rw [hθ]; split_ifs
    · rfl
    · rw [show 2 * -θ0 = -(2 * θ0) by ring, Real.cos_neg]
  have hsin2 : |Real.sin θ| = Real.sin θ0 := by
    have hS0 : 0 ≤ Real.sin θ0 := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
    rw [hθ]; split_ifs
    · exact abs_of_nonneg hS0
    · rw [Real.sin_neg, abs_neg, abs_of_nonneg hS0]
  have h := norm_Gr_le s δ (θ := θ) (by rw [habs]; linarith) (by linarith) hsg
  rw [habs, hcos2, hsin2] at h
  have hS0 : 0 ≤ Real.sin θ0 := Real.sin_nonneg_of_nonneg_of_le_pi hθ0.le (by linarith)
  have hSθ : Real.sin θ0 ≤ θ0 := Real.sin_le hθ0.le
  have hSS : Real.sin θ0 ≤ Real.sin 0.28 :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hθ1
  have hS28 := sin_028_le
  have hc := cos_two_mul_eq θ0
  set S := Real.sin θ0
  set c := Real.cos (2 * θ0)
  have hS2 : S ^ 2 ≤ 0.0763741 := by nlinarith
  have hc1 : 0.847251 ≤ c := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  have hb : 2 * π * |δ| * S ≤ 1.75931 := by
    have : |δ| * S ≤ 0.28 := le_trans (mul_le_mul_of_nonneg_left hSθ (abs_nonneg δ)) hδθ
    have h6 := Real.pi_lt_d6
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 2 * π)]
  have hb0 : 0 ≤ 2 * π * |δ| * S := by positivity
  have hI := integral_rpow_exp_quad_le_ext (p := s.re + 1) (c := c) (b := 2 * π * |δ| * S)
    (by linarith) (by linarith) hc0
  -- numerics
  have he : Real.exp ((2 * π * |δ| * S) ^ 2 / c) ≤ 38.7 := by
    refine (Real.exp_le_exp.2 ?_).trans exp_36533_le
    rw [div_le_iff₀ hc0]
    nlinarith [mul_le_mul hb hb hb0 (by norm_num)]
  have hc4 : 0.2118 ≤ c / 4 := by linarith
  have hr1 : (c / 4) ^ (-(1 / 4 : ℝ)) ≤ 1.48 := by
    rw [Real.rpow_neg (by linarith), inv_le_comm₀ (by positivity) (by norm_num)]
    have h1 : (1 / 1.48 : ℝ) = ((1 / 1.48 : ℝ) ^ (4:ℝ)) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num)]; norm_num
    have h2 : (1 / 1.48 : ℝ) ^ (4:ℝ) ≤ c / 4 := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num; linarith
    calc (1.48 : ℝ)⁻¹ = 1 / 1.48 := by norm_num
      _ = ((1 / 1.48 : ℝ) ^ (4:ℝ)) ^ (1 / 4 : ℝ) := h1
      _ ≤ (c / 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  have hr2 : (c / 4) ^ (-(3 / 2 : ℝ)) ≤ 10.27 := by
    rw [Real.rpow_neg (by linarith), inv_le_comm₀ (by positivity) (by norm_num)]
    have hsq : (c / 4) ^ (3 / 2 : ℝ) = (c / 4) * √(c / 4) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hsq]
    have hs : 0.46 ≤ √(c / 4) := Real.le_sqrt_of_sq_le (by nlinarith)
    have := mul_le_mul hc4 hs (by norm_num) (by linarith)
    norm_num at this ⊢; linarith
  have hG14 : Real.Gamma (1 / 4) ≤ 4 := by
    have e := Real.Gamma_add_one (s := 1 / 4) (by norm_num)
    have h := Gamma_le_one_of_mem (x := 1 / 4 + 1) (by norm_num) (by norm_num)
    rw [e] at h
    nlinarith
  have hG32 : Real.Gamma (3 / 2) ≤ 0.8863 := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    have := Real.pi_lt_d4
    have : √π ≤ 1.7725 := by rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    linarith
  have hG14' := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1 / 4)).le
  have hG32' := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3 / 2)).le
  have hbr : (c / 4) ^ (-(1 / 4 : ℝ)) * (1 / 2) * Real.Gamma (1 / 4) +
      (c / 4) ^ (-(3 / 2 : ℝ)) * (1 / 2) * Real.Gamma (3 / 2) ≤ 7.52 := by
    have a1 := mul_le_mul hr1 hG14 hG14' (by norm_num)
    have a2 := mul_le_mul hr2 hG32 hG32' (by norm_num)
    have e : (c / 4) ^ (-(1 / 4 : ℝ)) * (1 / 2) * Real.Gamma (1 / 4) +
        (c / 4) ^ (-(3 / 2 : ℝ)) * (1 / 2) * Real.Gamma (3 / 2) =
        (1 / 2) * ((c / 4) ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4)) +
          (1 / 2) * ((c / 4) ^ (-(3 / 2 : ℝ)) * Real.Gamma (3 / 2)) := by ring
    rw [e]
    linarith
  have hbr0 : 0 ≤ (c / 4) ^ (-(1 / 4 : ℝ)) * (1 / 2) * Real.Gamma (1 / 4) +
      (c / 4) ^ (-(3 / 2 : ℝ)) * (1 / 2) * Real.Gamma (3 / 2) := by
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ c / 4) (-(1 / 4 : ℝ))
    have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ c / 4) (-(3 / 2 : ℝ))
    positivity
  refine h.trans ?_
  rw [mul_comm (300 : ℝ)]
  refine mul_le_mul_of_nonneg_left (hI.trans ?_) (Real.exp_pos _).le
  calc Real.exp ((2 * π * |δ| * S) ^ 2 / c) * ((c / 4) ^ (-(1 / 4 : ℝ)) * (1 / 2) * Real.Gamma (1 / 4) +
        (c / 4) ^ (-(3 / 2 : ℝ)) * (1 / 2) * Real.Gamma (3 / 2))
      ≤ 38.7 * 7.52 := mul_le_mul he hbr hbr0 (by norm_num)
    _ ≤ 300 := by norm_num

end TernaryGoldbach.Explicit
