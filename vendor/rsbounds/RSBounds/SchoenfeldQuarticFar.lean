import RSBounds.SchoenfeldQuadraticFar
import RSBounds.SchoenfeldWeightedZerosM
import RSBounds.PolynomialRemainderGeneral
import RSBounds.PolynomialZeroPairing
import RSBounds.PolynomialPsiFromZeroSums

/-!
# The quartic envelope without a near region

The order-4 case of the far-only envelope of `docs/SchoenfeldOrderMPlan.md`, built from the
existing quartic chain (`PolynomialPsiFromZeroSums`) instead of the quadratic one:

    |ψ(x) − x| ≤ farEnvelope4 x δ + 700/(δ⁴ √x) + log 2π + 2δx,

    farEnvelope4 x δ = (R4 δ/δ⁴) √x · 0.0463/14.13³ + x (R4 δ/δ⁴) F₄(log x / R),

with `R4 δ = ((1+δ)⁵ + 1)⁴`, `R = 9.645908801` and `F₄` the far allowance of
`SchoenfeldWeightedZerosM.far_sum_le_m` at order `4` and height `A = 1894438.5122`. Every zero gets the
same quartic coefficient `(R4 δ/δ⁴) x^β/|γ|⁵` (`PolynomialZeroPairing`); zeros up to `A` lie on the
critical line by the finite RH hypothesis, and zeros above `A` are bounded with the RS75 zero-free
region, as in `SchoenfeldQuadraticFar`. The left contour uses the general-step bound of
`PolynomialRemainderGeneral`. The only condition linking `x` to `A` is `log x / R < 4 log(A/17)²`,
that is `log x < 5200` or so.
-/

open Complex Finset Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.SchoenfeldQuarticFar

open TernaryGoldbach.Explicit PolynomialExplicit BacklundCountIdentity PolynomialZeroCountBridge
open PolynomialZeroKernel SchoenfeldCoefficientPairing
open SchoenfeldZeroWeights SchoenfeldLaplaceTails SchoenfeldWeightedZeros
open SchoenfeldQuadraticPsi SchoenfeldWeightedZerosM

/-- The quartic coefficient of a zero at height `t`. -/
noncomputable def quarticCoefficient (δ t : ℝ) : ℝ := (R4 δ / δ ^ 4) / t ^ 5

theorem quarticCoefficient_nonneg (δ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ quarticCoefficient δ t := by
  unfold quarticCoefficient R4
  positivity

/-- The far allowance of order `4` at height `A`. -/
noncomputable def farAllowance4 (a A : ℝ) : ℝ :=
  (1 / (2 * Real.pi) + q A) * farPrimitive a d 4 (Real.log (A / 17)) / 17 ^ 4 +
    2 * rosserR 1.588 A * SchoenfeldZeroWeights.Phi a 4 A

/-- The quartic envelope with the split at `A = 1894438.5122`: no near zeros. -/
noncomputable def farEnvelope4 (x δ : ℝ) : ℝ :=
  (R4 δ / δ ^ 4) * Real.sqrt x * (0.0463 / 14.13 ^ 3) +
    x * ((R4 δ / δ ^ 4) * farAllowance4 (Real.log x / 9.645908801) 1894438.5122)

theorem rectangle_reciprocal_fifth_sum_lt {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 5) <
      0.0463 / 14.13 ^ 3 := by
  have hp : (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 5) ≤
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2) / 14.13 ^ 3 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hi := RS75XiIncrement.xi_zero_height_lower hz
    have hn := xiF_zero_im_ne_zero hz
    rw [div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (mul_pos (sq_pos_of_ne_zero hn) (by norm_num : (0 : ℝ) < 14.13 ^ 3))
    have ha : (14.13 : ℝ) ≤ |ρ.im| := hi.le
    calc
      ρ.im ^ 2 * 14.13 ^ 3 = |ρ.im| ^ 2 * 14.13 ^ 3 := by rw [sq_abs]
      _ ≤ |ρ.im| ^ 2 * |ρ.im| ^ 3 := by gcongr
      _ = |ρ.im| ^ 5 := by ring
  exact hp.trans_lt (div_lt_div_of_pos_right
    (SchoenfeldReciprocalSquare.rectangle_reciprocal_square_sum_lt hT) (by norm_num))

/-- The critical-line allowance is the reciprocal fifth-power sum. -/
theorem critical_sum_eq4 (T x δ : ℝ) :
    (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) * (quarticCoefficient δ |ρ.im| * Real.sqrt x)) =
      (R4 δ / δ ^ 4) * Real.sqrt x *
        ∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 5 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  unfold quarticCoefficient
  ring

/-- The high allowance is the order-4 weighted count. -/
theorem high_weightedSum_eq4 (A T x δ : ℝ) :
    WeightedZetaZeros.weightedSum A T (fun t => quarticCoefficient δ t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      x * (R4 δ / δ ^ 4) *
        WeightedZetaZeros.weightedSum A T (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 4) := by
  have he : (fun t => quarticCoefficient δ t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      (fun t => (x * (R4 δ / δ ^ 4)) * SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 4 t) := by
    funext t
    unfold quarticCoefficient SchoenfeldZeroWeights.Phi
    norm_num only [Nat.reduceAdd]
    ring
  rw [he, weightedSum_const_mul]

theorem norm_upper_sum_le4
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * PolynomialAveraged.zeroCoefficient x (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (quarticCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => quarticCoefficient δ t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  have hK : ∀ ρ ∈ zerosRectD zetaF T, ‖PolynomialAveraged.zeroCoefficient x (δ * x) ρ‖ ≤
      quarticCoefficient δ |ρ.im| * x ^ ρ.re := by
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := PolynomialZeroPairing.norm_zeroCoefficient_upper_le_high hx0 hδ hs.2.le hi
    calc
      _ ≤ (R4 δ / δ ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := hh
      _ = _ := by unfold quarticCoefficient; ring
  exact norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => PolynomialAveraged.zeroCoefficient x (δ * x) ρ)
    (quarticCoefficient δ) (quarticCoefficient δ)
    (fun t ht => quarticCoefficient_nonneg δ ht)
    (fun t ht => quarticCoefficient_nonneg δ ht)
    hK (fun ρ hρ _ => hK ρ hρ)

theorem norm_lower_sum_le4
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (hδ4 : 4 * δ < 1) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) *
        PolynomialAveraged.zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (quarticCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => quarticCoefficient δ t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  have hK : ∀ ρ ∈ zerosRectD zetaF T,
      ‖PolynomialAveraged.zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ ≤
        quarticCoefficient δ |ρ.im| * x ^ ρ.re := by
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := PolynomialZeroPairing.norm_zeroCoefficient_lower_le_high hx0 hδ hδ4 hs.1.le hi
    calc
      _ ≤ (R4 δ / δ ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := hh
      _ = _ := by unfold quarticCoefficient; ring
  exact norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => PolynomialAveraged.zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ)
    (quarticCoefficient δ) (quarticCoefficient δ)
    (fun t ht => quarticCoefficient_nonneg δ ht)
    (fun t ht => quarticCoefficient_nonneg δ ht)
    hK (fun ρ hρ _ => hK ρ hρ)

theorem norm_le_farEnvelope4_of_pairing {T x δ : ℝ} (hT : 0 < T)
    (hx : 1 < x) (hAT : 1894438.5122 ≤ T)
    (hfar : Real.log x / 9.645908801 < 4 * Real.log (1894438.5122 / 17) ^ 2)
    {z : ℂ}
    (hz : ‖z‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (quarticCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => quarticCoefficient δ t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))))) :
    ‖z‖ ≤ farEnvelope4 x δ := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < Real.log x / 9.645908801 := div_pos (Real.log_pos hx) (by norm_num)
  have hc : 0 ≤ R4 δ / δ ^ 4 := by unfold R4; positivity
  rw [critical_sum_eq4, high_weightedSum_eq4] at hz
  have hlo := mul_le_mul_of_nonneg_left (rectangle_reciprocal_fifth_sum_lt hT).le
    (mul_nonneg hc (Real.sqrt_nonneg x))
  have hf := far_sum_le_m (m := 4) (by norm_num) ha.le (by norm_num : (17 : ℝ) < 1894438.5122) hAT
    (by exact_mod_cast hfar)
  have hf' : WeightedZetaZeros.weightedSum 1894438.5122 T
      (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 4) ≤
      farAllowance4 (Real.log x / 9.645908801) 1894438.5122 := by
    unfold farAllowance4
    exact_mod_cast hf
  have hhi := mul_le_mul_of_nonneg_left hf' (mul_nonneg hx0.le hc)
  unfold farEnvelope4
  calc
    ‖z‖ ≤ _ := hz
    _ ≤ (R4 δ / δ ^ 4) * Real.sqrt x * (0.0463 / 14.13 ^ 3) +
        x * (R4 δ / δ ^ 4) * farAllowance4 (Real.log x / 9.645908801) 1894438.5122 :=
      add_le_add hlo hhi
    _ = _ := by ring

theorem eventually_upper_farEnvelope4 (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hfar : Real.log x / 9.645908801 < 4 * Real.log (1894438.5122 / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * PolynomialAveraged.zeroCoefficient x (δ * x) ρ‖ ≤
        farEnvelope4 x δ := by
  filter_upwards [eventually_height_ge hT 1894438.5122] with k hk
  have hTk : 0 < T k := by linarith
  exact norm_le_farEnvelope4_of_pairing hTk hx hk hfar
    (norm_upper_sum_le4 hRH hTk (zetaGoodHeight_of_generic_goodHeights hT k) hx.le hδ)

theorem eventually_lower_farEnvelope4 (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ4 : 4 * δ < 1)
    (hfar : Real.log x / 9.645908801 < 4 * Real.log (1894438.5122 / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) *
        PolynomialAveraged.zeroCoefficient (x - 4 * (δ * x)) (δ * x) ρ‖ ≤
          farEnvelope4 x δ := by
  filter_upwards [eventually_height_ge hT 1894438.5122] with k hk
  have hTk : 0 < T k := by linarith
  exact norm_le_farEnvelope4_of_pairing hTk hx hk hfar
    (norm_lower_sum_le4 hRH hTk (zetaGoodHeight_of_generic_goodHeights hT k) hx.le hδ hδ4)

/-- **The far-only quartic bound.** -/
theorem psi_error_le_farEnvelope4 (hRH : Goals.FiniteRH 1894438.5122)
    {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hfar : Real.log x / 9.645908801 < 4 * Real.log (1894438.5122 / 17) ^ 2) :
    |Chebyshev.psi x - x| ≤ farEnvelope4 x δ + 700 / (δ ^ 4 * Real.sqrt x) +
      Real.log (2 * Real.pi) + 2 * (δ * x) := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx0
  have hδ4 : 4 * δ < 1 := by linarith
  have hshift : 4 * (δ * x) < x := by
    have hm := mul_le_mul_of_nonneg_right hδ1 hx0.le
    linarith
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 4 * (δ * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hu := PolynomialPsiFromZeroSums.upper_error_of_eventually_bounded_zero_sums hT hx0 hh hN
    (eventually_upper_farEnvelope4 hRH hT hx hδ hfar)
    (PolynomialRemainderGeneral.norm_upper_leftRemainder_le hx0 hδ hδ1)
  have hl := PolynomialPsiFromZeroSums.lower_error_of_eventually_bounded_zero_sums hT hshift hh
    hNx (eventually_lower_farEnvelope4 hRH hT hx hδ hδ4 hfar)
    (PolynomialRemainderGeneral.norm_lower_leftRemainder_le hx0 hδ hδ1)
  exact PolynomialPsi.psi_error_of_polynomial_errors hx0.le hh hN hu hl

end TernaryGoldbach.RSBounds.SchoenfeldQuarticFar
