import RSBounds.SchoenfeldQuarticFar
import RSBounds.SchoenfeldSexticRemainder

/-!
# The sextic envelope without a near region

The order-6 analogue of `SchoenfeldQuarticFar`, built from the sextic chain
(`SchoenfeldSexticAveraged`, `SchoenfeldSexticKernel`, `SchoenfeldSexticRemainder`):

    |ψ(x) − x| ≤ farEnvelope6 x δ + 2300/(δ⁶ √x) + log 2π + 3δx,

    farEnvelope6 x δ = (R6 δ/δ⁶) √x · 0.0463/14.13⁵ + x (R6 δ/δ⁶) F₆(log x / R),

with `R6 δ = 64 (1 + 6δ)⁷`, `R = 9.645908801` and `F₆` the far allowance of
`SchoenfeldWeightedZerosM.far_sum_le_m` at order `6` and height `A = 1894438.5122`. Every zero gets the
coefficient `(R6 δ/δ⁶) x^β/|γ|⁷`; zeros up to `A` lie on the critical line by the finite RH
hypothesis, and zeros above `A` are bounded with the RS75 zero-free region, exactly as in the
quadratic and quartic far-only envelopes. The only condition linking `x` to `A` is
`log x / R < 6 log(A/17)²`, that is `log x < 7800` or so.
-/

open Complex Finset Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticFar

open TernaryGoldbach.Explicit PolynomialExplicit BacklundCountIdentity PolynomialZeroCountBridge
open SchoenfeldCoefficientPairing
open SchoenfeldZeroWeights SchoenfeldLaplaceTails SchoenfeldWeightedZeros
open SchoenfeldQuadraticPsi SchoenfeldWeightedZerosM SchoenfeldSexticKernel

/-- The sextic coefficient of a zero at height `t`. -/
noncomputable def sexticCoefficient (δ t : ℝ) : ℝ := (R6 δ / δ ^ 6) / t ^ 7

theorem sexticCoefficient_nonneg {δ : ℝ} (hδ : 0 ≤ δ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ sexticCoefficient δ t := by
  unfold sexticCoefficient R6
  positivity

/-- The far allowance of order `6` at height `A`. -/
noncomputable def farAllowance6 (a A : ℝ) : ℝ :=
  (1 / (2 * Real.pi) + q A) * farPrimitive a d 6 (Real.log (A / 17)) / 17 ^ 6 +
    2 * rosserR 1.588 A * SchoenfeldZeroWeights.Phi a 6 A

/-- The sextic envelope with the split at `A = 1894438.5122`: no near zeros. -/
noncomputable def farEnvelope6 (x δ : ℝ) : ℝ :=
  (R6 δ / δ ^ 6) * Real.sqrt x * (0.0463 / 14.13 ^ 5) +
    x * ((R6 δ / δ ^ 6) * farAllowance6 (Real.log x / 9.645908801) 1894438.5122)

theorem rectangle_reciprocal_seventh_sum_lt {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 7) <
      0.0463 / 14.13 ^ 5 := by
  have hp : (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 7) ≤
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2) / 14.13 ^ 5 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hi := RS75XiIncrement.xi_zero_height_lower hz
    have hn := xiF_zero_im_ne_zero hz
    rw [div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (mul_pos (sq_pos_of_ne_zero hn) (by norm_num : (0 : ℝ) < 14.13 ^ 5))
    have ha : (14.13 : ℝ) ≤ |ρ.im| := hi.le
    calc
      ρ.im ^ 2 * 14.13 ^ 5 = |ρ.im| ^ 2 * 14.13 ^ 5 := by rw [sq_abs]
      _ ≤ |ρ.im| ^ 2 * |ρ.im| ^ 5 := by gcongr
      _ = |ρ.im| ^ 7 := by ring
  exact hp.trans_lt (div_lt_div_of_pos_right
    (SchoenfeldReciprocalSquare.rectangle_reciprocal_square_sum_lt hT) (by norm_num))

/-- The critical-line allowance is the reciprocal seventh-power sum. -/
theorem critical_sum_eq6 (T x δ : ℝ) :
    (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) * (sexticCoefficient δ |ρ.im| * Real.sqrt x)) =
      (R6 δ / δ ^ 6) * Real.sqrt x *
        ∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 7 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  unfold sexticCoefficient
  ring

/-- The high allowance is the order-6 weighted count. -/
theorem high_weightedSum_eq6 (A T x δ : ℝ) :
    WeightedZetaZeros.weightedSum A T (fun t => sexticCoefficient δ t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      x * (R6 δ / δ ^ 6) *
        WeightedZetaZeros.weightedSum A T
          (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 6) := by
  have he : (fun t => sexticCoefficient δ t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      (fun t => (x * (R6 δ / δ ^ 6)) *
        SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 6 t) := by
    funext t
    unfold sexticCoefficient SchoenfeldZeroWeights.Phi
    norm_num only [Nat.reduceAdd]
    ring
  rw [he, weightedSum_const_mul]

theorem norm_upper_sum_le6
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * SchoenfeldSexticAveraged.zeroCoefficient x (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (sexticCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => sexticCoefficient δ t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  have hK : ∀ ρ ∈ zerosRectD zetaF T,
      ‖SchoenfeldSexticAveraged.zeroCoefficient x (δ * x) ρ‖ ≤
        sexticCoefficient δ |ρ.im| * x ^ ρ.re := by
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := norm_zeroCoefficient_upper_le_high hx0 hδ hs.2.le hi
    calc
      _ ≤ (R6 δ / δ ^ 6) * x ^ ρ.re / |ρ.im| ^ 7 := hh
      _ = _ := by unfold sexticCoefficient; ring
  exact norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => SchoenfeldSexticAveraged.zeroCoefficient x (δ * x) ρ)
    (sexticCoefficient δ) (sexticCoefficient δ)
    (fun t ht => sexticCoefficient_nonneg hδ.le ht)
    (fun t ht => sexticCoefficient_nonneg hδ.le ht)
    hK (fun ρ hρ _ => hK ρ hρ)

theorem norm_lower_sum_le6
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (hδ6 : 6 * δ < 1) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) *
        SchoenfeldSexticAveraged.zeroCoefficient (x - 6 * (δ * x)) (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (sexticCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => sexticCoefficient δ t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  have hK : ∀ ρ ∈ zerosRectD zetaF T,
      ‖SchoenfeldSexticAveraged.zeroCoefficient (x - 6 * (δ * x)) (δ * x) ρ‖ ≤
        sexticCoefficient δ |ρ.im| * x ^ ρ.re := by
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := norm_zeroCoefficient_lower_le_high hx0 hδ hδ6 hs.1.le hi
    calc
      _ ≤ (R6 δ / δ ^ 6) * x ^ ρ.re / |ρ.im| ^ 7 := hh
      _ = _ := by unfold sexticCoefficient; ring
  exact norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => SchoenfeldSexticAveraged.zeroCoefficient (x - 6 * (δ * x)) (δ * x) ρ)
    (sexticCoefficient δ) (sexticCoefficient δ)
    (fun t ht => sexticCoefficient_nonneg hδ.le ht)
    (fun t ht => sexticCoefficient_nonneg hδ.le ht)
    hK (fun ρ hρ _ => hK ρ hρ)

theorem norm_le_farEnvelope6_of_pairing {T x δ : ℝ} (hT : 0 < T)
    (hx : 1 < x) (hAT : 1894438.5122 ≤ T) (hδ : 0 ≤ δ)
    (hfar : Real.log x / 9.645908801 < 6 * Real.log (1894438.5122 / 17) ^ 2)
    {z : ℂ}
    (hz : ‖z‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (sexticCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => sexticCoefficient δ t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))))) :
    ‖z‖ ≤ farEnvelope6 x δ := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < Real.log x / 9.645908801 := div_pos (Real.log_pos hx) (by norm_num)
  have hc : 0 ≤ R6 δ / δ ^ 6 := by unfold R6; positivity
  rw [critical_sum_eq6, high_weightedSum_eq6] at hz
  have hlo := mul_le_mul_of_nonneg_left (rectangle_reciprocal_seventh_sum_lt hT).le
    (mul_nonneg hc (Real.sqrt_nonneg x))
  have hf := far_sum_le_m (m := 6) (by norm_num) ha.le (by norm_num : (17 : ℝ) < 1894438.5122) hAT
    (by exact_mod_cast hfar)
  have hf' : WeightedZetaZeros.weightedSum 1894438.5122 T
      (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 6) ≤
      farAllowance6 (Real.log x / 9.645908801) 1894438.5122 := by
    unfold farAllowance6
    exact_mod_cast hf
  have hhi := mul_le_mul_of_nonneg_left hf' (mul_nonneg hx0.le hc)
  unfold farEnvelope6
  calc
    ‖z‖ ≤ _ := hz
    _ ≤ (R6 δ / δ ^ 6) * Real.sqrt x * (0.0463 / 14.13 ^ 5) +
        x * (R6 δ / δ ^ 6) * farAllowance6 (Real.log x / 9.645908801) 1894438.5122 :=
      add_le_add hlo hhi
    _ = _ := by ring

theorem eventually_upper_farEnvelope6 (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hfar : Real.log x / 9.645908801 < 6 * Real.log (1894438.5122 / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) *
        SchoenfeldSexticAveraged.zeroCoefficient x (δ * x) ρ‖ ≤ farEnvelope6 x δ := by
  filter_upwards [eventually_height_ge hT 1894438.5122] with k hk
  have hTk : 0 < T k := by linarith
  exact norm_le_farEnvelope6_of_pairing hTk hx hk hδ.le hfar
    (norm_upper_sum_le6 hRH hTk (zetaGoodHeight_of_generic_goodHeights hT k) hx.le hδ)

theorem eventually_lower_farEnvelope6 (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ6 : 6 * δ < 1)
    (hfar : Real.log x / 9.645908801 < 6 * Real.log (1894438.5122 / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) *
        SchoenfeldSexticAveraged.zeroCoefficient (x - 6 * (δ * x)) (δ * x) ρ‖ ≤
          farEnvelope6 x δ := by
  filter_upwards [eventually_height_ge hT 1894438.5122] with k hk
  have hTk : 0 < T k := by linarith
  exact norm_le_farEnvelope6_of_pairing hTk hx hk hδ.le hfar
    (norm_lower_sum_le6 hRH hTk (zetaGoodHeight_of_generic_goodHeights hT k) hx.le hδ hδ6)

/-- **The far-only sextic bound.** -/
theorem psi_error_le_farEnvelope6 (hRH : Goals.FiniteRH 1894438.5122)
    {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hfar : Real.log x / 9.645908801 < 6 * Real.log (1894438.5122 / 17) ^ 2) :
    |Chebyshev.psi x - x| ≤ farEnvelope6 x δ + 2300 / (δ ^ 6 * Real.sqrt x) +
      Real.log (2 * Real.pi) + 3 * (δ * x) := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx0
  have hδ6 : 6 * δ < 1 := by linarith
  have hshift : 6 * (δ * x) < x := by
    have hm := mul_le_mul_of_nonneg_right hδ1 hx0.le
    linarith
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  exact SchoenfeldSexticAveraged.psi_error_of_eventually_bounded_zero_sums hT hx0 hh hshift
    (eventually_upper_farEnvelope6 hRH hT hx hδ hfar)
    (eventually_lower_farEnvelope6 hRH hT hx hδ hδ6 hfar)
    (SchoenfeldSexticRemainder.norm_upper_leftRemainder_le hx0 hδ hδ1)
    (SchoenfeldSexticRemainder.norm_lower_leftRemainder_le hx0 hδ hδ1)

end TernaryGoldbach.RSBounds.SchoenfeldSexticFar
