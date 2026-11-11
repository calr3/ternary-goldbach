import RSBounds.SchoenfeldQuadraticLeft

/-!
# The quadratic envelope without a near region

`SchoenfeldQuadraticLeft.psi_error_le_envelope` splits the zeros above the finite-RH height
`A = 1894438.5122` at a height `U ≥ A`. Its near part needs `log(U/17)² ≤ log x / R`, which with
`U ≥ A` means `log x ≥ R log(A/17)² ≈ 1302.6`. Splitting at `U = A` leaves no near zeros, so that
condition is not needed: `psi_error_le_farEnvelope` keeps only the critical-line term, the far
zeros above `A` (zero-free region, quadratic weight), the left contour, `log 2π` and the smoothing
loss. This is the `m = 2` case of the far-only envelope used for moderate `x`.
-/

open Complex Finset Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticFar

open TernaryGoldbach.Explicit PolynomialExplicit BacklundCountIdentity PolynomialZeroCountBridge
open QuadraticZeroKernel QuadraticKernelScaling SchoenfeldQuadraticPairing
open SchoenfeldZeroWeights SchoenfeldLaplaceTails SchoenfeldWeightedZeros
open SchoenfeldQuadraticEnvelope SchoenfeldQuadraticPsi

/-- A weighted count over an empty height range vanishes. -/
theorem weightedSum_self (a : ℝ) (φ : ℝ → ℝ) : WeightedZetaZeros.weightedSum a a φ = 0 := by
  unfold WeightedZetaZeros.weightedSum
  apply Finset.sum_eq_zero
  intro ρ hρ
  have h : ρ.im ≤ a := by
    unfold closedPositiveZeros at hρ
    exact (Finset.mem_filter.mp hρ).2
  rw [if_neg (not_lt.mpr h)]

/-- The envelope with the split at `A = 1894438.5122`: no near zeros. -/
noncomputable def farEnvelope (x δ : ℝ) : ℝ :=
  (R2 δ / δ ^ 2) * Real.sqrt x * (0.0463 / 14.13) +
    x * ((R2 δ / δ ^ 2) * farAllowance (Real.log x / 9.645908801) 1894438.5122)

theorem norm_le_farEnvelope_of_pairing {T x δ : ℝ} (hT : 0 < T)
    (hx : 1 < x) (hδ : 0 < δ) (hAT : 1894438.5122 ≤ T)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2)
    {z : ℂ}
    (hz : ‖z‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ 1894438.5122 t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))))) :
    ‖z‖ ≤ farEnvelope x δ := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < Real.log x / 9.645908801 := div_pos (Real.log_pos hx) (by norm_num)
  have hc : 0 ≤ R2 δ / δ ^ 2 := by unfold R2; positivity
  rw [critical_sum_eq, high_weightedSum_eq (by norm_num) le_rfl hAT, weightedSum_self,
    mul_zero, zero_add] at hz
  have hlo := mul_le_mul_of_nonneg_left (rectangle_reciprocal_cube_sum_lt hT).le
    (mul_nonneg hc (Real.sqrt_nonneg x))
  have hf := far_sum_le ha.le (by norm_num : (17 : ℝ) < 1894438.5122) hAT hfar
  change WeightedZetaZeros.weightedSum 1894438.5122 T
    (Phi (Real.log x / 9.645908801) 2) ≤ farAllowance (Real.log x / 9.645908801) 1894438.5122 at hf
  have hf' := mul_le_mul_of_nonneg_left hf hc
  have hhi := mul_le_mul_of_nonneg_left hf' hx0.le
  unfold farEnvelope
  exact hz.trans (add_le_add hlo hhi)

theorem norm_upper_sum_le_farEnvelope
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 < x) (hδ : 0 < δ) (hAT : 1894438.5122 ≤ T)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤ farEnvelope x δ :=
  norm_le_farEnvelope_of_pairing hT hx hδ hAT hfar
    (norm_upper_sum_le hRH hT hg hx.le hδ 1894438.5122)

theorem norm_lower_sum_le_farEnvelope
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hAT : 1894438.5122 ≤ T)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
        farEnvelope x δ :=
  norm_le_farEnvelope_of_pairing hT hx hδ hAT hfar
    (norm_lower_sum_le hRH hT hg hx.le hδ hδ2 1894438.5122)

theorem eventually_upper_farEnvelope (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤ farEnvelope x δ := by
  filter_upwards [eventually_height_ge hT 1894438.5122] with k hk
  exact norm_upper_sum_le_farEnvelope hRH (by linarith)
    (zetaGoodHeight_of_generic_goodHeights hT k) hx hδ hk hfar

theorem eventually_lower_farEnvelope (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) *
        zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤ farEnvelope x δ := by
  filter_upwards [eventually_height_ge hT 1894438.5122] with k hk
  exact norm_lower_sum_le_farEnvelope hRH (by linarith)
    (zetaGoodHeight_of_generic_goodHeights hT k) hx hδ hδ2 hk hfar

theorem psi_error_le_farEnvelope_of_left_bounds (hRH : Goals.FiniteRH 1894438.5122)
    {x δ C : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2)
    (hleftUpper : ‖QuadraticAveraged.leftRemainder x (δ * x)‖ ≤ C)
    (hleftLower : ‖QuadraticAveraged.leftRemainder (x - 2 * (δ * x)) (δ * x)‖ ≤ C) :
    |Chebyshev.psi x - x| ≤ farEnvelope x δ + C + Real.log (2 * Real.pi) + δ * x := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx0
  have hshift : 2 * (δ * x) < x := by
    have hm := mul_lt_mul_of_pos_right hδ2 hx0
    nlinarith only [hm]
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 2 * (δ * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hu := upper_error_of_eventually_bounded_zero_sums hT hx0 hh hN
    (eventually_upper_farEnvelope hRH hT hx hδ hfar) hleftUpper
  have hl := lower_error_of_eventually_bounded_zero_sums hT hshift hh hNx
    (eventually_lower_farEnvelope hRH hT hx hδ hδ2 hfar) hleftLower
  exact QuadraticPsi.psi_error_of_polynomial_errors hx0.le hh hN hu hl

/-- **The far-only quadratic bound**, with the left contour discharged as in
`SchoenfeldQuadraticLeft`: no condition linking `x` to the split height. -/
theorem psi_error_le_farEnvelope (hRH : Goals.FiniteRH 1894438.5122)
    {x δ : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2) :
    |Chebyshev.psi x - x| ≤ farEnvelope x δ +
      150000 / (δ ^ 2 * Real.sqrt x) + Real.log (2 * Real.pi) + δ * x := by
  have h := psi_error_le_farEnvelope_of_left_bounds hRH hx hδ hδ2 hfar
    (le_max_left _ _) (le_max_right _ _)
  have hl := SchoenfeldQuadraticLeft.leftAllowance_le (by linarith : 0 < x) hδ hδ2
  change |Chebyshev.psi x - x| ≤ farEnvelope x δ + SchoenfeldQuadraticPsi.leftAllowance x δ +
    Real.log (2 * Real.pi) + δ * x at h
  linarith

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticFar
