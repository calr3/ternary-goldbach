import RSBounds.SchoenfeldSexticKernel
import RSBounds.PolynomialRemainderIntegral
import RSBounds.PolynomialLeftRemainder

/-!
# The sextic left remainder

The order-6 analogue of `PolynomialRemainderIntegral` and `PolynomialRemainderGeneral`.

First, the sixth finite difference is taken inside the convergent left-line integral
(`leftRemainder_eq_integral`). Then the integrand is bounded, for every `0 < δ ≤ 0.01` and
`1 − 6δ ≤ y ≤ 1`, by `x^{−1/2} · gMajorant (1/δ⁶) t` with

    gMajorant c t = 385 c                         for |t| ≤ 1,
                  = 91 c (340 + 80|t|)/|t|⁷       for |t| > 1,

from `SchoenfeldSexticKernel.norm_zeroCoefficient_left`, `‖s(s+1)⋯(s+6)‖ ≥ max(81, |t|⁷)` and
the logarithmic bound `PolynomialLeftRemainder.norm_logDeriv_zeta_left_log` for `ζ'/ζ` on
`Re s = −1/2` (with `log|t| ≤ |t|`). Its integral over the real line is `41986 c/3`, so

    ‖leftRemainder (x y) (δ x)‖ ≤ x^{−1/2}/(2π) · 41986/(3δ⁶) ≤ 2300/(δ⁶ √x).

No RH or zero-count estimate is assumed.
-/

open Complex Set MeasureTheory
open scoped Real

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticRemainder

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroKernel
open SchoenfeldSexticMellin SchoenfeldSexticExplicit SchoenfeldSexticAveraged
open PolynomialRemainderIntegral (leftLine leftLine_re leftLine_ne_one zeta_leftLine_ne_zero)
open PolynomialLeftRemainder (norm_logDeriv_zeta_left_log)

/-! ## The averaged left remainder as an integral -/

theorem integrable_zeta_contour_left {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => contourIntegrand riemannZeta kernel x (leftLine t)) := by
  have hF := integrable_contour_left ldatum_zeta decayFive_kernel hx
  have h1 := integrable_contour_left ldatum_sub_one decayFive_kernel hx
  convert hF.sub h1 using 1
  funext t
  dsimp only [Pi.sub_apply, contourIntegrand]
  change logDeriv riemannZeta (leftLine t) * (kernel (leftLine t) * (x : ℂ) ^ leftLine t) =
    logDeriv zetaF (leftLine t) * (kernel (leftLine t) * (x : ℂ) ^ leftLine t) -
    logDeriv (fun s : ℂ => s - 1) (leftLine t) * (kernel (leftLine t) * (x : ℂ) ^ leftLine t)
  rw [logDeriv_zetaF_eq (leftLine_ne_one t) (zeta_leftLine_ne_zero t),
    logDeriv_sub_one]
  ring

noncomputable def primitiveIntegrand (x t : ℝ) : ℂ :=
  logDeriv riemannZeta (leftLine t) * antiderivative (leftLine t) 6 x

theorem primitiveIntegrand_eq {x : ℝ} (hx : 0 < x) (t : ℝ) :
    primitiveIntegrand x t = (x : ℂ) ^ 6 *
      contourIntegrand riemannZeta kernel x (leftLine t) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  unfold primitiveIntegrand antiderivative contourIntegrand kernel
  norm_num only [rising, Nat.cast_ofNat]
  rw [Complex.cpow_add _ _ hx0, Complex.cpow_ofNat]
  ring

theorem integrable_primitiveIntegrand {x : ℝ} (hx : 0 < x) :
    Integrable (primitiveIntegrand x) := by
  change Integrable (fun t => primitiveIntegrand x t)
  simpa only [primitiveIntegrand_eq hx] using
    (integrable_zeta_contour_left hx).const_mul ((x : ℂ) ^ 6)

theorem psi6LeftRemainder_eq_integral {x : ℝ} (hx : 0 < x) :
    psi6LeftRemainder x = (1 / (2 * π) : ℂ) * ∫ t : ℝ, primitiveIntegrand x t := by
  simp_rw [primitiveIntegrand_eq hx]
  rw [integral_const_mul]
  unfold psi6LeftRemainder leftLine
  ring

theorem leftRemainder_eq_integral {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    leftRemainder x h = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
        zeroCoefficient x h (leftLine t) := by
  have h0 := integrable_primitiveIntegrand hx
  have h1 := integrable_primitiveIntegrand (show 0 < x + h by linarith)
  have h2 := integrable_primitiveIntegrand (show 0 < x + 2 * h by linarith)
  have h3 := integrable_primitiveIntegrand (show 0 < x + 3 * h by linarith)
  have h4 := integrable_primitiveIntegrand (show 0 < x + 4 * h by linarith)
  have h5 := integrable_primitiveIntegrand (show 0 < x + 5 * h by linarith)
  have h6 := integrable_primitiveIntegrand (show 0 < x + 6 * h by linarith)
  have he (t : ℝ) : logDeriv riemannZeta (leftLine t) * zeroCoefficient x h (leftLine t) =
      (primitiveIntegrand (x + 6 * h) t - 6 * primitiveIntegrand (x + 5 * h) t +
        15 * primitiveIntegrand (x + 4 * h) t - 20 * primitiveIntegrand (x + 3 * h) t +
        15 * primitiveIntegrand (x + 2 * h) t - 6 * primitiveIntegrand (x + h) t +
          primitiveIntegrand x t) / (h : ℂ) ^ 6 := by
    unfold zeroCoefficient primitiveIntegrand
    rw [forwardDiff_six]
    ring
  simp_rw [he]
  have i1 := h6.sub (h5.const_mul 6)
  have i2 := i1.add (h4.const_mul 15)
  have i3 := i2.sub (h3.const_mul 20)
  have i4 := i3.add (h2.const_mul 15)
  have i5 := i4.sub (h1.const_mul 6)
  have e1 := integral_sub h6 (h5.const_mul 6)
  have e2 := integral_add i1 (h4.const_mul 15)
  have e3 := integral_sub i2 (h3.const_mul 20)
  have e4 := integral_add i3 (h2.const_mul 15)
  have e5 := integral_sub i4 (h1.const_mul 6)
  have e6 := integral_add i5 h0
  simp only [Pi.add_apply, Pi.sub_apply, integral_const_mul] at e1 e2 e3 e4 e5 e6
  rw [integral_div, e6, e5, e4, e3, e2, e1]
  unfold leftRemainder
  rw [forwardDiff_six, psi6LeftRemainder_eq_integral hx,
    psi6LeftRemainder_eq_integral (show 0 < x + h by linarith),
    psi6LeftRemainder_eq_integral (show 0 < x + 2 * h by linarith),
    psi6LeftRemainder_eq_integral (show 0 < x + 3 * h by linarith),
    psi6LeftRemainder_eq_integral (show 0 < x + 4 * h by linarith),
    psi6LeftRemainder_eq_integral (show 0 < x + 5 * h by linarith),
    psi6LeftRemainder_eq_integral (show 0 < x + 6 * h by linarith)]
  ring

theorem integrable_averagedIntegrand {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    Integrable (fun t : ℝ => logDeriv riemannZeta (leftLine t) *
      zeroCoefficient x h (leftLine t)) := by
  have h0 := integrable_primitiveIntegrand hx
  have h1 := integrable_primitiveIntegrand (show 0 < x + h by linarith)
  have h2 := integrable_primitiveIntegrand (show 0 < x + 2 * h by linarith)
  have h3 := integrable_primitiveIntegrand (show 0 < x + 3 * h by linarith)
  have h4 := integrable_primitiveIntegrand (show 0 < x + 4 * h by linarith)
  have h5 := integrable_primitiveIntegrand (show 0 < x + 5 * h by linarith)
  have h6 := integrable_primitiveIntegrand (show 0 < x + 6 * h by linarith)
  convert ((((((h6.sub (h5.const_mul 6)).add (h4.const_mul 15)).sub (h3.const_mul 20)).add
    (h2.const_mul 15)).sub (h1.const_mul 6)).add h0).div_const ((h : ℂ) ^ 6) using 1
  funext t
  dsimp only [Pi.add_apply, Pi.sub_apply]
  unfold zeroCoefficient primitiveIntegrand
  rw [forwardDiff_six]
  ring

/-! ## The majorant -/

/-- The tail of the majorant; the step enters through `c = 1/δ⁶`. -/
noncomputable def gTail (c t : ℝ) : ℝ := 91 * c * (340 + 80 * t) / t ^ 7

/-- The majorant on `t > 0`. -/
noncomputable def gPositive (c t : ℝ) : ℝ := if t ≤ 1 then 385 * c else gTail c t

/-- The majorant on the real line. -/
noncomputable def gMajorant (c t : ℝ) : ℝ := gPositive c |t|

private theorem gTail_eq_powers (c t : ℝ) (ht : 0 < t) :
    gTail c t = (91 * c * 340) * (t ^ 7)⁻¹ + (91 * c * 80) * (t ^ 6)⁻¹ := by
  unfold gTail
  field_simp

private theorem integrableOn_inv_pow_one (n : ℕ) (hn : 2 ≤ n) :
    IntegrableOn (fun t : ℝ => (t ^ n)⁻¹) (Ioi 1) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := -(n : ℝ))
    (by
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith) (by norm_num : (0 : ℝ) < 1)
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  change t ^ (-(n : ℝ)) = (t ^ n)⁻¹
  have ht0 : (0 : ℝ) ≤ t := zero_le_one.trans (le_of_lt ht)
  rw [Real.rpow_neg ht0, Real.rpow_natCast]

private theorem integral_inv_pow_one (n : ℕ) (hn : 2 ≤ n) :
    (∫ t : ℝ in Ioi 1, (t ^ n)⁻¹) = 1 / ((n : ℝ) - 1) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have h := integral_Ioi_rpow_of_lt (a := -(n : ℝ)) (by linarith) (by norm_num : (0 : ℝ) < 1)
  rw [Real.one_rpow] at h
  have heq : (fun t : ℝ => t ^ (-(n : ℝ))) =ᵐ[volume.restrict (Ioi 1)]
      fun t : ℝ => (t ^ n)⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := zero_le_one.trans (le_of_lt ht)
    rw [Real.rpow_neg ht0, Real.rpow_natCast]
  rw [integral_congr_ae heq] at h
  rw [h, div_eq_div_iff (by linarith) (by linarith)]
  ring

private theorem integrableOn_gTail (c : ℝ) : IntegrableOn (gTail c) (Ioi 1) := by
  have hi : IntegrableOn (fun t : ℝ =>
      (91 * c * 340) * (t ^ 7)⁻¹ + (91 * c * 80) * (t ^ 6)⁻¹) (Ioi 1) :=
    ((integrableOn_inv_pow_one 7 (by omega)).const_mul _).add
      ((integrableOn_inv_pow_one 6 (by omega)).const_mul _)
  exact hi.congr_fun (fun t ht => (gTail_eq_powers c t (zero_lt_one.trans ht)).symm)
    measurableSet_Ioi

private theorem integral_gTail (c : ℝ) :
    (∫ t : ℝ in Ioi 1, gTail c t) = 19838 * c / 3 := by
  calc
    (∫ t : ℝ in Ioi 1, gTail c t) =
        ∫ t : ℝ in Ioi 1, (91 * c * 340) * (t ^ 7)⁻¹ + (91 * c * 80) * (t ^ 6)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact gTail_eq_powers c t (zero_lt_one.trans ht)
    _ = _ := by
      rw [integral_add ((integrableOn_inv_pow_one 7 (by omega)).const_mul _)
          ((integrableOn_inv_pow_one 6 (by omega)).const_mul _),
        integral_const_mul, integral_const_mul,
        integral_inv_pow_one 7 (by omega), integral_inv_pow_one 6 (by omega)]
      norm_num
      ring

private theorem integrableOn_gPositive_low (c : ℝ) :
    IntegrableOn (gPositive c) (Ioc (0 : ℝ) 1) := by
  refine (integrableOn_const (C := (385 * c : ℝ)) (hs := by simp)).congr_fun
    (fun t ht => ?_) measurableSet_Ioc
  simp [gPositive, ht.2]

private theorem integrableOn_gPositive_high (c : ℝ) :
    IntegrableOn (gPositive c) (Ioi (1 : ℝ)) := by
  refine (integrableOn_gTail c).congr_fun (fun t ht => ?_) measurableSet_Ioi
  change 1 < t at ht
  simp [gPositive, not_le.mpr ht]

theorem integrableOn_gPositive (c : ℝ) : IntegrableOn (gPositive c) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (integrableOn_gPositive_low c).union (integrableOn_gPositive_high c)

theorem integral_gPositive (c : ℝ) :
    (∫ t : ℝ in Ioi (0 : ℝ), gPositive c t) = 385 * c + 19838 * c / 3 := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (by exact Set.disjoint_left.mpr (fun t h1 h2 => not_lt_of_ge h1.2 h2))
      measurableSet_Ioi (integrableOn_gPositive_low c) (integrableOn_gPositive_high c)]
  have hlow : (∫ t : ℝ in Ioc (0 : ℝ) 1, gPositive c t) = 385 * c := by
    calc
      _ = ∫ t : ℝ in Ioc (0 : ℝ) 1, (385 * c : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        simp [gPositive, ht.2]
      _ = _ := by simp
  have hhigh : (∫ t : ℝ in Ioi (1 : ℝ), gPositive c t) = 19838 * c / 3 := by
    rw [← integral_gTail c]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 1 < t at ht
    simp [gPositive, not_le.mpr ht]
  rw [hlow, hhigh]

theorem integrable_gMajorant (c : ℝ) : Integrable (gMajorant c) := by
  change Integrable (fun t : ℝ => gPositive c |t|)
  have hpos : IntegrableOn (fun t : ℝ => gPositive c |t|) (Ioi 0) := by
    refine (integrableOn_gPositive c).congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]
  have hneg : IntegrableOn (fun t : ℝ => gPositive c |t|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun t : ℝ => -t := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hi := hneg.union hpos
  simpa only [Iic_union_Ioi, IntegrableOn, Measure.restrict_univ, gMajorant] using hi

theorem integral_gMajorant (c : ℝ) :
    (∫ t : ℝ, gMajorant c t) = 41986 * c / 3 := by
  unfold gMajorant
  rw [integral_comp_abs, integral_gPositive]
  ring

/-! ## The bound -/

/-- The pointwise majorant for the averaged left integrand, for any step `0 < δ ≤ 0.01`. -/
theorem norm_averagedIntegrand_le {x δ y : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 6 * δ ≤ y) (hy1 : y ≤ 1) (t : ℝ) :
    ‖logDeriv riemannZeta (leftLine t) * zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * gMajorant (1 / δ ^ 6) t := by
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hδ6 : 0 < δ ^ 6 := by positivity
  have hld := norm_logDeriv_zeta_left_log t
  change ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 + 80 * Real.log (max 1 |t|) at hld
  have hk := SchoenfeldSexticKernel.norm_zeroCoefficient_left hx hδ hδ1 hy0 hy1 (leftLine_re t)
  have hr0 : (0 : ℝ) < ‖rising (leftLine t) 6‖ :=
    lt_of_lt_of_le (by norm_num) (SchoenfeldSexticKernel.norm_rising_six_ge_left (leftLine_re t))
  rw [norm_mul]
  by_cases ht1 : |t| ≤ 1
  · have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 := by
      simpa only [max_eq_left ht1, Real.log_one, mul_zero, add_zero] using hld
    have hr := SchoenfeldSexticKernel.norm_rising_six_ge_left (leftLine_re t)
    have hk' : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
        x ^ (-1 / 2 : ℝ) * (91 / 81 * (1 / δ ^ 6)) := by
      refine hk.trans (mul_le_mul_of_nonneg_left ?_ hxp)
      rw [div_le_iff₀ (by positivity)]
      have : 91 / 81 * (1 / δ ^ 6) * (δ ^ 6 * ‖rising (leftLine t) 6‖) =
          91 / 81 * ‖rising (leftLine t) 6‖ := by
        field_simp
      rw [this]
      linarith
    have he : gMajorant (1 / δ ^ 6) t = 385 * (1 / δ ^ 6) := by
      unfold gMajorant gPositive
      simp only [ht1, ↓reduceIte]
    rw [he]
    have hc : 0 ≤ 1 / δ ^ 6 := by positivity
    calc
      _ ≤ 340 * (x ^ (-1 / 2 : ℝ) * (91 / 81 * (1 / δ ^ 6))) :=
        mul_le_mul hd hk' (norm_nonneg _) (by norm_num)
      _ ≤ x ^ (-1 / 2 : ℝ) * (385 * (1 / δ ^ 6)) := by
        have : 340 * (x ^ (-1 / 2 : ℝ) * (91 / 81 * (1 / δ ^ 6))) =
            x ^ (-1 / 2 : ℝ) * ((340 * 91 / 81) * (1 / δ ^ 6)) := by ring
        rw [this]
        apply mul_le_mul_of_nonneg_left _ hxp
        exact mul_le_mul_of_nonneg_right (by norm_num) hc
  · have htgt : 1 < |t| := lt_of_not_ge ht1
    have htpos : 0 < |t| := by linarith
    rw [max_eq_right htgt.le] at hld
    have hlog : Real.log |t| ≤ |t| := by
      have := Real.log_le_sub_one_of_pos htpos
      linarith
    have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 + 80 * |t| := by linarith
    have him : (leftLine t).im = t := by
      simp only [leftLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, zero_mul, add_zero, zero_add]
    have hr := SchoenfeldSexticKernel.abs_im_pow_le_norm_rising_six (leftLine t)
    rw [him] at hr
    have hk' : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
        x ^ (-1 / 2 : ℝ) * (91 / (δ ^ 6 * |t| ^ 7)) := by
      refine hk.trans (mul_le_mul_of_nonneg_left ?_ hxp)
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hr hδ6.le)
    have he : gMajorant (1 / δ ^ 6) t = 91 * (1 / δ ^ 6) * (340 + 80 * |t|) / |t| ^ 7 := by
      unfold gMajorant gPositive
      simp only [ht1, ↓reduceIte]
      rfl
    rw [he]
    calc
      _ ≤ (340 + 80 * |t|) * (x ^ (-1 / 2 : ℝ) * (91 / (δ ^ 6 * |t| ^ 7))) :=
        mul_le_mul hd hk' (norm_nonneg _) (by positivity)
      _ = _ := by field_simp

/-- **The averaged sextic left remainder for a general step.** -/
theorem norm_leftRemainder_le {x δ y : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 6 * δ ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (δ * x)‖ ≤
      x ^ (-1 / 2 : ℝ) / (2 * Real.pi) * (41986 * (1 / δ ^ 6) / 3) := by
  have hy : 0 < y := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx
  have hi := integrable_averagedIntegrand (mul_pos hx hy) hh
  have hmaj := (integrable_gMajorant (1 / δ ^ 6)).const_mul (x ^ (-1 / 2 : ℝ))
  have hnorm : ‖∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
      zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * (41986 * (1 / δ ^ 6) / 3) := by
    calc
      _ ≤ ∫ t : ℝ, ‖logDeriv riemannZeta (leftLine t) *
          zeroCoefficient (x * y) (δ * x) (leftLine t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, x ^ (-1 / 2 : ℝ) * gMajorant (1 / δ ^ 6) t :=
        integral_mono hi.norm hmaj (norm_averagedIntegrand_le hx hδ hδ1 hy0 hy1)
      _ = x ^ (-1 / 2 : ℝ) * ∫ t : ℝ, gMajorant (1 / δ ^ 6) t := integral_const_mul _ _
      _ = _ := by rw [integral_gMajorant]
  rw [leftRemainder_eq_integral (mul_pos hx hy) hh, norm_mul]
  have hfac : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hfac]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-1 / 2 : ℝ) * (41986 * (1 / δ ^ 6) / 3)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- The same bound in the form used by the envelopes: `2300/(δ⁶ √x)`. -/
theorem norm_leftRemainder_le_simple {x δ y : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 6 * δ ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (δ * x)‖ ≤ 2300 / (δ ^ 6 * Real.sqrt x) := by
  refine (norm_leftRemainder_le hx hδ hδ1 hy0 hy1).trans ?_
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hδ6 : 0 < δ ^ 6 := by positivity
  have hp : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
      one_div]
  rw [hp]
  have hpi := Real.pi_gt_d2
  rw [show 1 / Real.sqrt x / (2 * Real.pi) * (41986 * (1 / δ ^ 6) / 3) =
      (41986 / 3) / (2 * Real.pi * δ ^ 6 * Real.sqrt x) by
    field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (2300 : ℝ) * (2 * Real.pi) ≥ 41986 / 3 := by linarith
  calc
    (41986 / 3 : ℝ) * (δ ^ 6 * Real.sqrt x) ≤ 2300 * (2 * Real.pi) * (δ ^ 6 * Real.sqrt x) := by
      gcongr
    _ = 2300 * (2 * Real.pi * δ ^ 6 * Real.sqrt x) := by ring

/-- The upper smoothing direction (`y = 1`). -/
theorem norm_upper_leftRemainder_le {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) :
    ‖leftRemainder x (δ * x)‖ ≤ 2300 / (δ ^ 6 * Real.sqrt x) := by
  simpa only [mul_one] using
    norm_leftRemainder_le_simple (y := 1) hx hδ hδ1 (by linarith) le_rfl

/-- The lower smoothing direction (`y = 1 - 6δ`). -/
theorem norm_lower_leftRemainder_le {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) :
    ‖leftRemainder (x - 6 * (δ * x)) (δ * x)‖ ≤ 2300 / (δ ^ 6 * Real.sqrt x) := by
  rw [show x - 6 * (δ * x) = x * (1 - 6 * δ) by ring]
  exact norm_leftRemainder_le_simple hx hδ hδ1 le_rfl (by linarith)

end TernaryGoldbach.RSBounds.SchoenfeldSexticRemainder
