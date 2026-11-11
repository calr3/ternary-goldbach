import RSBounds.SchoenfeldZeroWeights
import RSBounds.RosserWeightedBounds

/-!
# Actual weighted-zero bounds for Schoenfeld's Theorem 11

The positive-ordinate sums carry analytic multiplicities. Rosser's zero-count
estimate is a proved input, and the finite endpoint corrections are retained.
-/

open Complex Real Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.SchoenfeldWeightedZeros

open BacklundCountIdentity Rosser1941 WeightedZetaZeros RosserTailIntegrals
open RosserWeightedBounds SchoenfeldLaplaceTails SchoenfeldZeroWeights

private theorem integrable_mainDensity {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun t => Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) volume l r := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hlr] at ht
  have ht0 : 0 < t := hl.trans_le ht.1
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

private theorem integrable_errorDensity {l r : ℝ} (hl : 1 < l) (hlr : l ≤ r) :
    IntervalIntegrable (fun t => (0.137 + 0.443 / Real.log t) / t) volume l r := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hlr] at ht
  have ht1 : 1 < t := hl.trans_le ht.1
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_pos ht1
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

/-- The increasing-weight envelope bound for actual zeros, retaining both endpoints. -/
theorem weightedSum_le_increasing {l r : ℝ} (hl : 2 ≤ l) (hlr : l ≤ r)
    {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc l r, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume l r)
    (hinc : ∀ t ∈ Ioo l r, 0 ≤ φ' t) :
    weightedSum l r φ ≤
      (∫ t in l..r, (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) -
        (0.137 + 0.443 / Real.log t) / t) * φ t) +
      (positiveZeroCount r - rosserF r + rosserR 1.588 r) * φ r -
      (positiveZeroCount l - rosserF l + rosserR 1.588 l) * φ l := by
  have hl0 : 0 < l := by linarith
  have he := weighted_ordinate_sum_le_increasing (zeroCopies r) (fun z => z.1.im) hlr hφ
    (fun t ht => hasDerivAt_rosserF (hl0.trans_le ht.1))
    (fun t ht => hasDerivAt_rosserR 1.588 (by linarith [ht.1]))
    hφ' (integrable_mainDensity hl0 hlr) (integrable_errorDensity (by linarith) hlr)
    hinc (fun t ht => by
      rw [ordinateCount_zeroCopies (hl0.trans_le ht.1) ht.2]
      have hc := zero_count_bounds t (hl.trans ht.1)
      change |positiveZeroCount t - rosserF t| < rosserR 1.588 t at hc
      linarith [(abs_lt.mp hc).1])
  rw [window_sum_zeroCopies (hl0.trans_le hlr),
    ordinateCount_zeroCopies (hl0.trans_le hlr) le_rfl,
    ordinateCount_zeroCopies hl0 hlr] at he
  exact he

/-- Remove the nonpositive lower correction and the negative `R'` integral. -/
theorem weightedSum_le_increasing_main {l r : ℝ} (hl : 2 ≤ l) (hlr : l ≤ r)
    {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc l r, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume l r)
    (hinc : ∀ t ∈ Ioo l r, 0 ≤ φ' t)
    (hnn : ∀ t ∈ Icc l r, 0 ≤ φ t) :
    weightedSum l r φ ≤
      (∫ t in l..r, Real.log (t / (2 * Real.pi)) / (2 * Real.pi) * φ t) +
        2 * rosserR 1.588 r * φ r := by
  have hl0 : 0 < l := by linarith
  have hcφ : ContinuousOn φ (uIcc l r) := by
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact (hφ t ht).continuousAt.continuousWithinAt
  have hF := integrable_mainDensity hl0 hlr
  have hR := integrable_errorDensity (by linarith : 1 < l) hlr
  have hi := intervalIntegral.integral_mono_on hlr ((hF.sub hR).mul_continuousOn hcφ)
    (hF.mul_continuousOn hcφ) (fun t ht => by
      have ht1 : 1 < t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      have hlog := Real.log_pos ht1
      have hnn' : 0 ≤ (0.137 + 0.443 / Real.log t) / t := by positivity
      exact mul_le_mul_of_nonneg_right (sub_le_self _ hnn') (hnn t ht))
  have hcl := zero_count_bounds l hl
  have hcr := zero_count_bounds r (hl.trans hlr)
  change |positiveZeroCount l - rosserF l| < rosserR 1.588 l at hcl
  change |positiveZeroCount r - rosserF r| < rosserR 1.588 r at hcr
  have hlcorr : 0 ≤ (positiveZeroCount l - rosserF l + rosserR 1.588 l) * φ l :=
    mul_nonneg (by linarith [(abs_lt.mp hcl).1]) (hnn l ⟨le_rfl, hlr⟩)
  have hrcorr : (positiveZeroCount r - rosserF r + rosserR 1.588 r) * φ r ≤
      2 * rosserR 1.588 r * φ r :=
    mul_le_mul_of_nonneg_right (by linarith [(abs_lt.mp hcr).2]) (hnn r ⟨hlr, le_rfl⟩)
  have he := weightedSum_le_increasing hl hlr hφ hφ' hinc
  linarith

/-- A decreasing-weight bound with the exact quotient `q(l)` of (7.14). -/
theorem weightedSum_le_decreasing_q {l r : ℝ} (hl : 7 ≤ l) (hlr : l ≤ r)
    {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc l r, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume l r)
    (hdec : ∀ t ∈ Ioo l r, φ' t ≤ 0)
    (hnn : ∀ t ∈ Icc l r, 0 ≤ φ t) :
    weightedSum l r φ ≤
      (1 / (2 * Real.pi) + q l) *
        (∫ t in l..r, Real.log (t / (2 * Real.pi)) * φ t) +
        2 * rosserR 1.588 l * φ l := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 < l := by linarith
  have hlπ : 2 * Real.pi < l := by linarith [Real.pi_lt_d4]
  have hcφ : ContinuousOn φ (uIcc l r) := by
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact (hφ t ht).continuousAt.continuousWithinAt
  have hd : IntervalIntegrable density volume l r := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact (continuousAt_density (hl1.trans_le ht.1)).continuousWithinAt
  have hlogI : IntervalIntegrable (fun t => Real.log (t / (2 * Real.pi))) volume l r := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hlr] at ht
    have ht0 : 0 < t := hl0.trans_le ht.1
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have hu := (hlogI.mul_continuousOn hcφ).const_mul (1 / (2 * Real.pi) + q l)
  have hi := intervalIntegral.integral_mono_on hlr (hd.mul_continuousOn hcφ) hu
    (fun t ht => by
      have hh := mul_le_mul_of_nonneg_right (density_le_q hl1 hlπ ht.1) (hnn t ht)
      simpa only [density, mul_assoc] using hh)
  rw [intervalIntegral.integral_const_mul] at hi
  have he := weightedSum_le_decreasing_head (by linarith : 2 ≤ l) hlr hφ hφ' hdec
    (hnn r ⟨hlr, le_rfl⟩)
  change weightedSum l r φ ≤ (∫ t in l..r, density t * φ t) +
    (G l - positiveZeroCount l) * φ l at he
  have hcorr := mul_le_mul_of_nonneg_right (head_correction_le (by linarith : 2 ≤ l))
    (hnn l ⟨le_rfl, hlr⟩)
  linarith


noncomputable def d : ℝ := Real.log (17 / (2 * Real.pi))

theorem d_pos : 0 < d := by
  unfold d
  apply Real.log_pos
  apply (one_lt_div (by positivity)).mpr
  linarith [Real.pi_lt_d4]

theorem log_height_split {t : ℝ} (ht : 0 < t) :
    Real.log (t / (2 * Real.pi)) = Real.log (t / 17) + d := by
  unfold d
  rw [← Real.log_mul (by positivity : t / 17 ≠ 0) (by positivity : (17 : ℝ) / (2 * Real.pi) ≠ 0)]
  congr 1
  field_simp

theorem Phi_mul_log_eq_heightIntegrand (a : ℝ) (m : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.log (t / (2 * Real.pi)) * Phi a m t = heightIntegrand a d m t := by
  rw [log_height_split ht]
  unfold Phi heightIntegrand
  ring

private theorem integrable_PhiDerivative (a : ℝ) (m : ℕ) {l r : ℝ}
    (hl : 17 < l) (hlr : l ≤ r) :
    IntervalIntegrable (PhiDerivative a m) volume l r := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hlr] at ht
  have ht17 : 17 < t := hl.trans_le ht.1
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log (t / 17) := Real.log_pos (by linarith)
  unfold PhiDerivative Phi
  fun_prop (disch := positivity)

/-- The actual near-high zero sum, with the exact integral constant of (7.11). -/
theorem near_sum_le {a l r : ℝ} (ha : 0 < a) (hl : 17 < l) (hlr : l ≤ r)
    (hnear : Real.log (r / 17) ^ 2 ≤ a) :
    weightedSum l r (Phi a 0) ≤
      nearPrimitive a d (Real.log (r / 17)) / (2 * Real.pi) +
        2 * rosserR 1.588 r * Phi a 0 r := by
  have hl0 : 0 < l := by linarith
  have hr0 : 0 < r := hl0.trans_le hlr
  have hφ := fun t (ht : t ∈ Icc l r) => hasDerivAt_Phi a 0 (hl.trans_le ht.1)
  have hinc : ∀ t ∈ Ioo l r, 0 ≤ PhiDerivative a 0 t := by
    intro t ht
    have ht17 : 17 < t := hl.trans ht.1
    have ht0 : 0 < t := by linarith
    have hlogt : 0 < Real.log (t / 17) := Real.log_pos (by linarith)
    have hlogtr : Real.log (t / 17) ≤ Real.log (r / 17) :=
      Real.log_le_log (by positivity : 0 < t / 17)
        (div_le_div_of_nonneg_right ht.2.le (by norm_num))
    exact PhiDerivative_zero_nonneg ht17
      ((pow_le_pow_left₀ hlogt.le hlogtr 2).trans hnear)
  have he := weightedSum_le_increasing_main (by linarith : 2 ≤ l) hlr hφ
    (integrable_PhiDerivative a 0 hl hlr) hinc
    (fun t ht => (Phi_pos a 0 (hl0.trans_le ht.1)).le)
  have heq : (∫ t in l..r, Real.log (t / (2 * Real.pi)) / (2 * Real.pi) * Phi a 0 t) =
      (∫ t in l..r, heightIntegrand a d 0 t) / (2 * Real.pi) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlr] at ht
    change Real.log (t / (2 * Real.pi)) / (2 * Real.pi) * Phi a 0 t =
      heightIntegrand a d 0 t / (2 * Real.pi)
    rw [← Phi_mul_log_eq_heightIntegrand a 0 (hl0.trans_le ht.1)]
    ring
  rw [heq] at he
  exact he.trans (add_le_add
    (div_le_div_of_nonneg_right (integral_height_near_le ha d_pos.le hl hlr)
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)) le_rfl)

/-- The actual far-high zero sum, with the exact integral constant of (7.18). -/
theorem far_sum_le {a l r : ℝ} (ha : 0 ≤ a) (hl : 17 < l) (hlr : l ≤ r)
    (hfar : a < 2 * Real.log (l / 17) ^ 2) :
    weightedSum l r (Phi a 2) ≤
      (1 / (2 * Real.pi) + q l) * farPrimitive a d 2 (Real.log (l / 17)) / 289 +
        2 * rosserR 1.588 l * Phi a 2 l := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 < l := by linarith
  have hlπ : 2 * Real.pi < l := by linarith [Real.pi_lt_d4]
  have hlogl : 0 < Real.log (l / 17) := Real.log_pos (by linarith)
  have hφ := fun t (ht : t ∈ Icc l r) => hasDerivAt_Phi a 2 (hl.trans_le ht.1)
  have hdec : ∀ t ∈ Ioo l r, PhiDerivative a 2 t ≤ 0 := by
    intro t ht
    have ht17 : 17 < t := hl.trans ht.1
    have hloglt : Real.log (l / 17) ≤ Real.log (t / 17) :=
      Real.log_le_log (by positivity : 0 < l / 17)
        (div_le_div_of_nonneg_right ht.1.le (by norm_num))
    have hs := pow_le_pow_left₀ hlogl.le hloglt 2
    exact PhiDerivative_two_nonpos ht17 (by linarith)
  have he := weightedSum_le_decreasing_q (by linarith : 7 ≤ l) hlr hφ
    (integrable_PhiDerivative a 2 hl hlr) hdec
    (fun t ht => (Phi_pos a 2 (hl0.trans_le ht.1)).le)
  have heq : (∫ t in l..r, Real.log (t / (2 * Real.pi)) * Phi a 2 t) =
      (∫ t in l..r, heightIntegrand a d 2 t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact Phi_mul_log_eq_heightIntegrand a 2 (hl0.trans_le ht.1)
  rw [heq] at he
  have hc : 0 ≤ 1 / (2 * Real.pi) + q l := by
    have hq := q_nonneg hl1 hlπ
    positivity
  have hi := mul_le_mul_of_nonneg_left (integral_height_far_le ha d_pos.le hl hlr hfar) hc
  have hi' : (1 / (2 * Real.pi) + q l) * (∫ t in l..r, heightIntegrand a d 2 t) ≤
      (1 / (2 * Real.pi) + q l) * farPrimitive a d 2 (Real.log (l / 17)) / 289 := by
    convert hi using 1 <;> ring
  exact he.trans (add_le_add hi' le_rfl)

end TernaryGoldbach.RSBounds.SchoenfeldWeightedZeros
