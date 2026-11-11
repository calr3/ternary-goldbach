import RSBounds.PolynomialRemainderBound

/-!
# The quartic left remainder for a general smoothing step

`PolynomialRemainderBound` bounds the averaged left remainder of the quartic explicit formula for
the historical step `δ = 0.0000211` only: its majorant has a fixed cutoff `65536 ≥ 1/δ`. The
far-only envelope at large `x` uses much smaller steps, so this file proves a bound for every
`0 < δ ≤ 0.01`.

The majorant is cruder: `748` on `|t| ≤ 1` (as before) and `19 (340 + 80|t|) / (δ⁴ |t|⁵)` beyond,
using `log |t| ≤ |t|` in the bound for `ζ'/ζ` on the line `Re s = -1/2`. Its integral over the real
line is `1496 + 12730/(3δ⁴)`, so

    ‖leftRemainder (x y) (δ x)‖ ≤ x^(-1/2)/(2π) · (1496 + 12730/(3δ⁴)) ≤ 700/(δ⁴ √x).

For the far-only envelope at `log x ≥ 400` this is negligible for any `δ` of interest. No RH or
zero-count estimate is assumed.
-/

open Complex Set MeasureTheory
open scoped Real

namespace TernaryGoldbach.RSBounds.PolynomialRemainderGeneral

open TernaryGoldbach.Explicit PolynomialAveraged PolynomialLeftRemainder
open PolynomialRemainderIntegral PolynomialLeftKernel

/-- The tail of the majorant; the step enters through `c = 1/δ⁴`. -/
noncomputable def gTail (c t : ℝ) : ℝ := 19 * c * (340 + 80 * t) / t ^ 5

/-- The majorant on `t > 0`. -/
noncomputable def gPositive (c t : ℝ) : ℝ := if t ≤ 1 then 748 else gTail c t

/-- The majorant on the real line. -/
noncomputable def gMajorant (c t : ℝ) : ℝ := gPositive c |t|

private theorem gTail_eq_powers (c t : ℝ) (ht : 0 < t) :
    gTail c t = (19 * c * 340) * (t ^ 5)⁻¹ + (19 * c * 80) * (t ^ 4)⁻¹ := by
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
      (19 * c * 340) * (t ^ 5)⁻¹ + (19 * c * 80) * (t ^ 4)⁻¹) (Ioi 1) :=
    ((integrableOn_inv_pow_one 5 (by omega)).const_mul _).add
      ((integrableOn_inv_pow_one 4 (by omega)).const_mul _)
  exact hi.congr_fun (fun t ht => (gTail_eq_powers c t (zero_lt_one.trans ht)).symm)
    measurableSet_Ioi

private theorem integral_gTail (c : ℝ) :
    (∫ t : ℝ in Ioi 1, gTail c t) = 6365 * c / 3 := by
  calc
    (∫ t : ℝ in Ioi 1, gTail c t) =
        ∫ t : ℝ in Ioi 1, (19 * c * 340) * (t ^ 5)⁻¹ + (19 * c * 80) * (t ^ 4)⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact gTail_eq_powers c t (zero_lt_one.trans ht)
    _ = _ := by
      rw [integral_add ((integrableOn_inv_pow_one 5 (by omega)).const_mul _)
          ((integrableOn_inv_pow_one 4 (by omega)).const_mul _),
        integral_const_mul, integral_const_mul,
        integral_inv_pow_one 5 (by omega), integral_inv_pow_one 4 (by omega)]
      norm_num
      ring

private theorem integrableOn_gPositive_low (c : ℝ) :
    IntegrableOn (gPositive c) (Ioc (0 : ℝ) 1) := by
  refine (integrableOn_const (C := (748 : ℝ)) (hs := by simp)).congr_fun
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
    (∫ t : ℝ in Ioi (0 : ℝ), gPositive c t) = 748 + 6365 * c / 3 := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union (by exact Set.disjoint_left.mpr (fun t h1 h2 => not_lt_of_ge h1.2 h2))
      measurableSet_Ioi (integrableOn_gPositive_low c) (integrableOn_gPositive_high c)]
  have hlow : (∫ t : ℝ in Ioc (0 : ℝ) 1, gPositive c t) = 748 := by
    calc
      _ = ∫ t : ℝ in Ioc (0 : ℝ) 1, (748 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        simp [gPositive, ht.2]
      _ = _ := by simp
  have hhigh : (∫ t : ℝ in Ioi (1 : ℝ), gPositive c t) = 6365 * c / 3 := by
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
    (∫ t : ℝ, gMajorant c t) = 1496 + 12730 * c / 3 := by
  unfold gMajorant
  rw [integral_comp_abs, integral_gPositive]
  ring

/-- The pointwise majorant for the averaged left integrand, for any step `0 < δ ≤ 0.01`. -/
theorem norm_averagedIntegrand_le {x δ y : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) (t : ℝ) :
    ‖logDeriv riemannZeta (leftLine t) * zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * gMajorant (1 / δ ^ 4) t := by
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hld := norm_logDeriv_zeta_left_log t
  change ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 + 80 * Real.log (max 1 |t|) at hld
  rw [norm_mul]
  by_cases ht1 : |t| ≤ 1
  · have hlo := norm_zeroCoefficient_left_low hx hδ hδ1 hy0 hy1 (leftLine_re t)
    have hhalf : (1 / 2 : ℝ) ≤ ‖leftLine t‖ := by
      have hh := Complex.abs_re_le_norm (leftLine t)
      rw [leftLine_re] at hh
      norm_num at hh
      exact hh
    have hn0 : 0 < ‖leftLine t‖ := by linarith
    have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 := by
      simpa only [max_eq_left ht1, Real.log_one, mul_zero, add_zero] using hld
    have hk : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤ x ^ (-1 / 2 : ℝ) * 2.2 := by
      refine hlo.trans (mul_le_mul_of_nonneg_left ?_ hxp)
      rw [div_le_iff₀ hn0]
      linarith
    have he : gMajorant (1 / δ ^ 4) t = 748 := by
      unfold gMajorant gPositive
      simp only [ht1, ↓reduceIte]
    rw [he]
    calc
      _ ≤ 340 * (x ^ (-1 / 2 : ℝ) * 2.2) := mul_le_mul hd hk (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  · have htgt : 1 < |t| := lt_of_not_ge ht1
    have htpos : 0 < |t| := by linarith
    rw [max_eq_right htgt.le] at hld
    have hlog : Real.log |t| ≤ |t| := by
      have := Real.log_le_sub_one_of_pos htpos
      linarith
    have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 + 80 * |t| := by linarith
    have htim : (leftLine t).im ≠ 0 := by
      simpa [leftLine] using (abs_pos.mp htpos)
    have hi := norm_zeroCoefficient_left_high hx hδ hδ1 hy0 hy1 (leftLine_re t) htim
    have him : (leftLine t).im = t := by
      simp only [leftLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, zero_mul, add_zero, zero_add]
    rw [him] at hi
    have he : gMajorant (1 / δ ^ 4) t = 19 * (1 / δ ^ 4) * (340 + 80 * |t|) / |t| ^ 5 := by
      unfold gMajorant gPositive
      simp only [ht1, ↓reduceIte]
      rfl
    rw [he]
    calc
      _ ≤ (340 + 80 * |t|) * (x ^ (-1 / 2 : ℝ) * (19 / (δ ^ 4 * |t| ^ 5))) :=
        mul_le_mul hd hi (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- **The averaged left remainder for a general step.** -/
theorem norm_leftRemainder_le {x δ y : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (δ * x)‖ ≤
      x ^ (-1 / 2 : ℝ) / (2 * Real.pi) * (1496 + 12730 * (1 / δ ^ 4) / 3) := by
  have hy : 0 < y := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx
  have hi := integrable_averagedIntegrand (mul_pos hx hy) hh
  have hmaj := (integrable_gMajorant (1 / δ ^ 4)).const_mul (x ^ (-1 / 2 : ℝ))
  have hnorm : ‖∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
      zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * (1496 + 12730 * (1 / δ ^ 4) / 3) := by
    calc
      _ ≤ ∫ t : ℝ, ‖logDeriv riemannZeta (leftLine t) *
          zeroCoefficient (x * y) (δ * x) (leftLine t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, x ^ (-1 / 2 : ℝ) * gMajorant (1 / δ ^ 4) t :=
        integral_mono hi.norm hmaj (norm_averagedIntegrand_le hx hδ hδ1 hy0 hy1)
      _ = x ^ (-1 / 2 : ℝ) * ∫ t : ℝ, gMajorant (1 / δ ^ 4) t := integral_const_mul _ _
      _ = _ := by rw [integral_gMajorant]
  rw [leftRemainder_eq_integral (mul_pos hx hy) hh, norm_mul]
  have hfac : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hfac]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-1 / 2 : ℝ) * (1496 + 12730 * (1 / δ ^ 4) / 3)) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- The same bound in the form used by the envelopes: `700/(δ⁴ √x)`. -/
theorem norm_leftRemainder_le_simple {x δ y : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (δ * x)‖ ≤ 700 / (δ ^ 4 * Real.sqrt x) := by
  refine (norm_leftRemainder_le hx hδ hδ1 hy0 hy1).trans ?_
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hδ4 : 0 < δ ^ 4 := by positivity
  have hδ4le : δ ^ 4 ≤ 1 / 100000000 := by
    calc
      δ ^ 4 ≤ (0.01 : ℝ) ^ 4 := by gcongr
      _ = 1 / 100000000 := by norm_num
  have hp : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
      one_div]
  rw [hp]
  have hpi := Real.pi_gt_d2
  rw [show 1 / Real.sqrt x / (2 * Real.pi) * (1496 + 12730 * (1 / δ ^ 4) / 3) =
      (1496 * δ ^ 4 + 12730 / 3) / (2 * Real.pi * δ ^ 4 * Real.sqrt x) by
    field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 1496 * δ ^ 4 + 12730 / 3 ≤ 4244 := by linarith
  have h2 : (700 : ℝ) * (2 * Real.pi) ≥ 4244 := by linarith
  calc
    (1496 * δ ^ 4 + 12730 / 3) * (δ ^ 4 * Real.sqrt x) ≤ 4244 * (δ ^ 4 * Real.sqrt x) := by
      gcongr
    _ ≤ 700 * (2 * Real.pi) * (δ ^ 4 * Real.sqrt x) := by gcongr
    _ = 700 * (2 * Real.pi * δ ^ 4 * Real.sqrt x) := by ring

/-- The upper smoothing direction (`y = 1`). -/
theorem norm_upper_leftRemainder_le {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) :
    ‖leftRemainder x (δ * x)‖ ≤ 700 / (δ ^ 4 * Real.sqrt x) := by
  simpa only [mul_one] using
    norm_leftRemainder_le_simple (y := 1) hx hδ hδ1 (by linarith) le_rfl

/-- The lower smoothing direction (`y = 1 - 4δ`). -/
theorem norm_lower_leftRemainder_le {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) :
    ‖leftRemainder (x - 4 * (δ * x)) (δ * x)‖ ≤ 700 / (δ ^ 4 * Real.sqrt x) := by
  rw [show x - 4 * (δ * x) = x * (1 - 4 * δ) by ring]
  exact norm_leftRemainder_le_simple hx hδ hδ1 le_rfl (by linarith)

end TernaryGoldbach.RSBounds.PolynomialRemainderGeneral
