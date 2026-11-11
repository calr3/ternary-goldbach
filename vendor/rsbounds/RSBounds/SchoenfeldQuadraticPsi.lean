import RSBounds.SchoenfeldQuadraticKernel
import RSBounds.PolynomialPsiFromZeroSums
import RSBounds.SchoenfeldCoefficientPairing
import RSBounds.SchoenfeldZeroWeights
import RSBounds.SchoenfeldSquareCutoffs
import RSBounds.SchoenfeldWeightedZeros

/-!
# Quadratic zero envelopes and the actual psi handoff

Verification is recorded by the matching exact-source runner and axiom audit.
The original draft files are preserved untouched. Already checked results are
imported; their declarations are not reproduced. Separate sections retain each
draft's namespace and local open-command scope.
-/

/-! ## Preserved draft: `RSBounds/SchoenfeldQuadraticPairing.lean` -/
section SchoenfeldQuadraticPairingDraft

/-!
# Reflection bounds for the actual quadratic smoothing coefficients

The all-zero critical-line allowance uses the far coefficient (T1=0), as
in Schoenfeld's Theorem 11. The high-zero allowance switches from the near
coefficient to the far coefficient at the supplied positive height U.
-/

open Complex Finset Real

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticPairing

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open SchoenfeldCoefficientPairing QuadraticZeroKernel QuadraticKernelScaling

noncomputable def criticalCoefficient (δ t : ℝ) : ℝ := (R2 δ / δ ^ 2) / t ^ 3

noncomputable def highCoefficient (δ U t : ℝ) : ℝ :=
  if t ≤ U then (1 + δ) / t else criticalCoefficient δ t

theorem criticalCoefficient_nonneg (δ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ criticalCoefficient δ t := by
  unfold criticalCoefficient R2
  positivity

theorem highCoefficient_nonneg {δ : ℝ} (hδ : 0 < δ) (U : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ highCoefficient δ U t := by
  unfold highCoefficient
  split_ifs
  · positivity
  · exact criticalCoefficient_nonneg δ ht

/-- Rosser's all-zero square allowance gives the cube allowance used at T1=0. -/
theorem rectangle_reciprocal_cube_sum_lt {T : ℝ} (hT : 0 < T) :
    (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 3) <
      0.0463 / 14.13 := by
  have hp : (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 3) ≤
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2) / 14.13 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hi := RS75XiIncrement.xi_zero_height_lower hz
    have hn := xiF_zero_im_ne_zero hz
    rw [div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (mul_pos (sq_pos_of_ne_zero hn) (by norm_num : (0 : ℝ) < 14.13))
    calc
      ρ.im ^ 2 * 14.13 = |ρ.im| ^ 2 * 14.13 := by rw [sq_abs]
      _ ≤ |ρ.im| ^ 2 * |ρ.im| := mul_le_mul_of_nonneg_left hi.le (sq_nonneg _)
      _ = |ρ.im| ^ 3 := by ring
  exact hp.trans_lt (div_lt_div_of_pos_right
    (SchoenfeldReciprocalSquare.rectangle_reciprocal_square_sum_lt hT)
    (by norm_num : (0 : ℝ) < 14.13))

/-- The critical-line allowance is the actual reciprocal-cube sum. -/
theorem critical_sum_eq (T x δ : ℝ) :
    (∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) =
      (R2 δ / δ ^ 2) * Real.sqrt x *
        ∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / |ρ.im| ^ 3 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  unfold criticalCoefficient
  ring

/-- The high allowance splits into the exact Phi0 and Phi2 weighted counts. -/
theorem high_weightedSum_eq {A U T : ℝ} (hU : 0 < U) (hAU : A ≤ U) (hUT : U ≤ T)
    (x δ : ℝ) :
    WeightedZetaZeros.weightedSum A T (fun t => highCoefficient δ U t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      x * ((1 + δ) * WeightedZetaZeros.weightedSum A U
        (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 0) +
        (R2 δ / δ ^ 2) * WeightedZetaZeros.weightedSum U T
          (SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 2)) := by
  have he : (fun t => highCoefficient δ U t *
      (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) =
      (fun t => if t ≤ U then (x * (1 + δ)) *
        SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 0 t
      else (x * (R2 δ / δ ^ 2)) *
        SchoenfeldZeroWeights.Phi (Real.log x / 9.645908801) 2 t) := by
    funext t
    unfold highCoefficient criticalCoefficient SchoenfeldZeroWeights.Phi
    split_ifs <;> norm_num only [Nat.reduceAdd, pow_one] <;> ring
  rw [he, weightedSum_split_ite hU hAU hUT,
    weightedSum_const_mul, weightedSum_const_mul]
  ring

/-- The actual upper coefficients, with one positive-height high allowance. -/
theorem norm_upper_sum_le
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (U : ℝ) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ U t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  apply norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => zeroCoefficient x (δ * x) ρ)
    (criticalCoefficient δ) (highCoefficient δ U)
    (fun t ht => criticalCoefficient_nonneg δ ht)
    (fun t ht => highCoefficient_nonneg hδ U ht)
  · intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_upper_le_high hx0 hδ hs.2.le hi
    convert hh using 1 <;> unfold criticalCoefficient <;> ring
  · intro ρ hρ _
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    unfold highCoefficient
    split_ifs
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_upper_le_low hx0 hδ hs.1 hs.2.le hi
      convert hh using 1 <;> ring
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_upper_le_high hx0 hδ hs.2.le hi
      convert hh using 1 <;> unfold criticalCoefficient <;> ring

/-- The actual lower coefficients use the identical positive-height allowance. -/
theorem norm_lower_sum_le
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1) (U : ℝ) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ U t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17)))) := by
  have hx0 : 0 < x := by linarith
  apply norm_sum_le_critical_and_weighted_high hRH hT hg hx
    (fun ρ => zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ)
    (criticalCoefficient δ) (highCoefficient δ U)
    (fun t ht => criticalCoefficient_nonneg δ ht)
    (fun t ht => highCoefficient_nonneg hδ U ht)
  · intro ρ hρ
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_lower_le_high hx0 hδ hδ2 hs.1.le hi
    convert hh using 1 <;> unfold criticalCoefficient <;> ring
  · intro ρ hρ _
    have hz := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
    have hs := xiF_zero_re_strip hz
    have hi := xiF_zero_im_ne_zero hz
    unfold highCoefficient
    split_ifs
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_lower_le_low hx0 hδ hδ2 hs.1 hi
      convert hh using 1 <;> ring
    · have hh := QuadraticCoefficientBounds.norm_zeroCoefficient_lower_le_high hx0 hδ hδ2 hs.1.le hi
      convert hh using 1 <;> unfold criticalCoefficient <;> ring

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticPairing
end SchoenfeldQuadraticPairingDraft

/-! ## Preserved draft: `RSBounds/SchoenfeldQuadraticEnvelope.lean` -/
section SchoenfeldQuadraticEnvelopeDraft

/-!
# A uniform finite-height envelope for Schoenfeld's quadratic zero sum

This binds the actual second-difference coefficients to the exact elementary
Laplace bounds. The upper contour height disappears from the majorant. No
zero-sum estimate is assumed: only the stated finite RH check remains.
-/

open Complex Finset Real

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticEnvelope

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open QuadraticZeroKernel QuadraticKernelScaling SchoenfeldQuadraticPairing
open SchoenfeldZeroWeights SchoenfeldLaplaceTails SchoenfeldWeightedZeros

noncomputable def nearAllowance (a U : ℝ) : ℝ :=
  nearPrimitive a d (Real.log (U / 17)) / (2 * Real.pi) +
    2 * rosserR 1.588 U * Phi a 0 U

noncomputable def farAllowance (a U : ℝ) : ℝ :=
  (1 / (2 * Real.pi) + q U) * farPrimitive a d 2 (Real.log (U / 17)) / 289 +
    2 * rosserR 1.588 U * Phi a 2 U

noncomputable def envelope (x δ U : ℝ) : ℝ :=
  (R2 δ / δ ^ 2) * Real.sqrt x * (0.0463 / 14.13) +
    x * ((1 + δ) * nearAllowance (Real.log x / 9.645908801) U +
      (R2 δ / δ ^ 2) * farAllowance (Real.log x / 9.645908801) U)

/-- Both exact weighted-count envelopes are independent of the upper height. -/
theorem norm_le_envelope_of_pairing {T x δ U : ℝ} (hT : 0 < T)
    (hx : 1 < x) (hδ : 0 < δ) (hAU : 1894438.5122 ≤ U) (hUT : U ≤ T)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2)
    {z : ℂ}
    (hz : ‖z‖ ≤
      (∑ ρ ∈ zerosRectD zetaF T,
        (multRectD zetaF T ρ : ℝ) * (criticalCoefficient δ |ρ.im| * Real.sqrt x)) +
      WeightedZetaZeros.weightedSum 1894438.5122 T (fun t => highCoefficient δ U t *
        (x * Real.exp (-(Real.log x / 9.645908801) / Real.log (t / 17))))) :
    ‖z‖ ≤ envelope x δ U := by
  have hx0 : 0 < x := by linarith
  have hU17 : 17 < U := by linarith
  have hU0 : 0 < U := by linarith
  have ha : 0 < Real.log x / 9.645908801 := div_pos (Real.log_pos hx) (by norm_num)
  have hc : 0 ≤ R2 δ / δ ^ 2 := by unfold R2; positivity
  rw [critical_sum_eq, high_weightedSum_eq hU0 hAU hUT] at hz
  have hlo := mul_le_mul_of_nonneg_left (rectangle_reciprocal_cube_sum_lt hT).le
    (mul_nonneg hc (Real.sqrt_nonneg x))
  have hn := near_sum_le ha (by norm_num : (17 : ℝ) < 1894438.5122) hAU hnear
  have hf := far_sum_le ha.le hU17 hUT hfar
  change WeightedZetaZeros.weightedSum 1894438.5122 U
    (Phi (Real.log x / 9.645908801) 0) ≤ nearAllowance (Real.log x / 9.645908801) U at hn
  change WeightedZetaZeros.weightedSum U T
    (Phi (Real.log x / 9.645908801) 2) ≤ farAllowance (Real.log x / 9.645908801) U at hf
  have hn' := mul_le_mul_of_nonneg_left hn (by linarith : 0 ≤ 1 + δ)
  have hf' := mul_le_mul_of_nonneg_left hf hc
  have hhi := mul_le_mul_of_nonneg_left (add_le_add hn' hf') hx0.le
  exact hz.trans (add_le_add hlo hhi)

/-- The actual upper zero sum satisfies the uniform envelope. -/
theorem norm_upper_sum_le_envelope
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ U : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 < x) (hδ : 0 < δ)
    (hAU : 1894438.5122 ≤ U) (hUT : U ≤ T)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤ envelope x δ U :=
  norm_le_envelope_of_pairing hT hx hδ hAU hUT hnear hfar
    (norm_upper_sum_le hRH hT hg hx.le hδ U)

/-- The actual lower zero sum satisfies the same uniform envelope. -/
theorem norm_lower_sum_le_envelope
    (hRH : Goals.FiniteRH 1894438.5122) {T x δ U : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hAU : 1894438.5122 ≤ U) (hUT : U ≤ T)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤
        envelope x δ U :=
  norm_le_envelope_of_pairing hT hx hδ hAU hUT hnear hfar
    (norm_lower_sum_le hRH hT hg hx.le hδ hδ2 U)

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticEnvelope
end SchoenfeldQuadraticEnvelopeDraft

/-! ## New bridge from the actual quadratic zero sums to psi

The final bound retains the actual averaged left integrals. Thus there is
no assumed remainder estimate or abstract zero-sum budget in that export.
Discharging the displayed left allowance and the paper's scalar parameter
balance are subsequent obligations.
-/

open Complex Finset Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticPsi

open TernaryGoldbach.Explicit PolynomialExplicit BacklundCountIdentity
open QuadraticKernelScaling SchoenfeldQuadraticEnvelope

/-- Only horizontal nonvanishing is needed; the datum may be `BPz2`. -/
theorem zetaGoodHeight_of_generic_goodHeights {B : ℝ → ℝ} {T : ℕ → ℝ}
    (hT : GoodHeights zetaF B T) (k : ℕ) : zetaGoodHeight (T k) := by
  have hTk : 0 < T k := by
    linarith [(hT.mem k).1, Nat.cast_nonneg (α := ℝ) k]
  intro ρ hz he
  have him : ρ.im ≠ 0 := by rw [he]; exact hTk.ne'
  have hxi := xiF_eq_zero_of_zeta_zero him hz
  have hre := xiF_zero_re_strip hxi
  have hs : ρ.re ∈ Set.uIcc (-1 / 2 : ℝ) (3 / 2) := by
    rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2)]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have hn := ((hT.bounds k ρ.re hs).1).1
  have hρ : (ρ.re : ℂ) + (T k : ℂ) * I = ρ := by
    apply Complex.ext <;> simp [he]
  rw [hρ] at hn
  have hne : ρ ≠ 1 := by
    intro h
    have := hre.2
    simpa [h] using this
  apply hn
  rw [zetaF_of_ne hne, hz, mul_zero]

/-- The contour sequence eventually exceeds every fixed splitting height. -/
theorem eventually_height_ge {B : ℝ → ℝ} {T : ℕ → ℝ}
    (hT : GoodHeights zetaF B T) (U : ℝ) : ∀ᶠ k in atTop, U ≤ T k := by
  obtain ⟨K, hK⟩ := exists_nat_ge U
  filter_upwards [eventually_ge_atTop K] with k hk
  have hkR : (K : ℝ) ≤ k := by exact_mod_cast hk
  linarith [(hT.mem k).1]

/-- Pass the actual upper zero sum to the quadratic smoothing error. -/
theorem upper_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x h E C : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 2 * h ≤ N)
    (hzero : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ‖ ≤ E)
    (hleft : ‖QuadraticAveraged.leftRemainder x h‖ ≤ C) :
    |QuadraticPsi.psiUpper N x h - (x + h)| ≤ E + C + Real.log (2 * Real.pi) := by
  have hlim := QuadraticAveraged.explicit_formula_upper_at_heights hT hx hh hN
  exact PolynomialPsiFromZeroSums.smoothing_error_of_norm_bound
    (le_of_tendsto hlim.norm hzero) hleft

/-- Pass the actual lower zero sum to the quadratic smoothing error. -/
theorem lower_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x h E C : ℝ} (hx : 2 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N)
    (hzero : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 2 * h) h ρ‖ ≤ E)
    (hleft : ‖QuadraticAveraged.leftRemainder (x - 2 * h) h‖ ≤ C) :
    |QuadraticPsi.psiLower N x h - (x - h)| ≤ E + C + Real.log (2 * Real.pi) := by
  have hlim := QuadraticAveraged.explicit_formula_lower_at_heights hT hx hh hN
  exact PolynomialPsiFromZeroSums.smoothing_error_of_norm_bound
    (le_of_tendsto hlim.norm hzero) hleft

/-- The upper finite-sum envelope holds eventually along the actual contour. -/
theorem eventually_upper_envelope (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x δ U : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hAU : 1894438.5122 ≤ U)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x (δ * x) ρ‖ ≤
        envelope x δ U := by
  filter_upwards [eventually_height_ge hT U] with k hk
  exact norm_upper_sum_le_envelope hRH (by linarith)
    (zetaGoodHeight_of_generic_goodHeights hT k) hx hδ hAU hk hnear hfar

/-- The lower finite-sum envelope holds along the same contour sequence. -/
theorem eventually_lower_envelope (hRH : Goals.FiniteRH 1894438.5122) {T : ℕ → ℝ}
    (hT : GoodHeights zetaF BPz2 T) {x δ U : ℝ} (hx : 1 < x) (hδ : 0 < δ)
    (hδ2 : 2 * δ < 1) (hAU : 1894438.5122 ≤ U)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    ∀ᶠ k in atTop, ‖∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) *
        zeroCoefficient (x - 2 * (δ * x)) (δ * x) ρ‖ ≤ envelope x δ U := by
  filter_upwards [eventually_height_ge hT U] with k hk
  exact norm_lower_sum_le_envelope hRH (by linarith)
    (zetaGoodHeight_of_generic_goodHeights hT k) hx hδ hδ2 hAU hk hnear hfar

/-- The only remaining analytic budgets here are bounds on the two actual
averaged left remainders; the zero envelope and unsmoothing are explicit. -/
theorem psi_error_le_envelope_of_left_bounds (hRH : Goals.FiniteRH 1894438.5122)
    {x δ U C : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hAU : 1894438.5122 ≤ U)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2)
    (hleftUpper : ‖QuadraticAveraged.leftRemainder x (δ * x)‖ ≤ C)
    (hleftLower : ‖QuadraticAveraged.leftRemainder (x - 2 * (δ * x)) (δ * x)‖ ≤ C) :
    |Chebyshev.psi x - x| ≤ envelope x δ U + C + Real.log (2 * Real.pi) + δ * x := by
  have hx0 : 0 < x := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx0
  have hshift : 2 * (δ * x) < x := by
    have hm := mul_lt_mul_of_pos_right hδ2 hx0
    nlinarith only [hm]
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 2 * (δ * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hu := upper_error_of_eventually_bounded_zero_sums hT hx0 hh hN
    (eventually_upper_envelope hRH hT hx hδ hAU hnear hfar) hleftUpper
  have hl := lower_error_of_eventually_bounded_zero_sums hT hshift hh hNx
    (eventually_lower_envelope hRH hT hx hδ hδ2 hAU hnear hfar) hleftLower
  exact QuadraticPsi.psi_error_of_polynomial_errors hx0.le hh hN hu hl

/-- The precise remaining left-contour allowance, without an estimate axiom. -/
noncomputable def leftAllowance (x δ : ℝ) : ℝ :=
  max ‖QuadraticAveraged.leftRemainder x (δ * x)‖
    ‖QuadraticAveraged.leftRemainder (x - 2 * (δ * x)) (δ * x)‖

/-- Actual psi, the exact quadratic zero envelope, and the two explicit left
integrals. No zero-sum or remainder inequality is supplied as a premise. -/
theorem psi_error_le_envelope (hRH : Goals.FiniteRH 1894438.5122)
    {x δ U : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hAU : 1894438.5122 ≤ U)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    |Chebyshev.psi x - x| ≤ envelope x δ U + leftAllowance x δ +
      Real.log (2 * Real.pi) + δ * x :=
  psi_error_le_envelope_of_left_bounds hRH hx hδ hδ2 hAU hnear hfar
    (le_max_left _ _) (le_max_right _ _)

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticPsi
