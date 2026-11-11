import RSBounds.SchoenfeldWeightedZeros

/-!
# Far weighted zero sums for smoothing of any order `m ≥ 1`

`SchoenfeldWeightedZeros.far_sum_le` is the case `m = 2`. The Laplace bounds
(`SchoenfeldLaplaceTails.integral_far_le`) and the substitution
(`SchoenfeldLaplacePhysical.integral_height_eq`) already allow any order, so only the
monotonicity of `Phi a m` needs a general statement. This is the zero-free-region input of an
order-`m` far-only envelope.
-/

open Complex Real Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.SchoenfeldWeightedZerosM

open BacklundCountIdentity Rosser1941 WeightedZetaZeros RosserTailIntegrals
open RosserWeightedBounds SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldWeightedZeros

/-- `Phi a m` decreases where `a ≤ (m + 1) log(t/17)²`. -/
theorem PhiDerivative_nonpos {a t : ℝ} (m : ℕ) (ht : 17 < t)
    (ha : a ≤ (m + 1) * Real.log (t / 17) ^ 2) : PhiDerivative a m t ≤ 0 := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log (t / 17) := Real.log_pos (by linarith)
  have hquot : a / Real.log (t / 17) ^ 2 ≤ m + 1 :=
    (div_le_iff₀ (sq_pos_of_pos hl)).mpr ha
  unfold PhiDerivative
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (Phi_pos a m ht0).le (by push_cast; linarith)) ht0.le

/-- A copy of the private `SchoenfeldWeightedZeros.integrable_PhiDerivative`. -/
theorem integrable_PhiDerivative_m (a : ℝ) (m : ℕ) {l r : ℝ}
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

/-- The order-`m` height integral, after `u = log(t/17)`. -/

theorem integral_height_far_le_m {a d l r : ℝ} {m : ℕ} (hm : 0 < m) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hl : 17 < l) (hlr : l ≤ r) (hq : a < m * Real.log (l / 17) ^ 2) :
    (∫ t in l..r, heightIntegrand a d m t) ≤
      farPrimitive a d m (Real.log (l / 17)) / 17 ^ m := by
  rw [integral_height_eq hl hlr]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply integral_far_le ha hd (by exact_mod_cast hm)
  · exact Real.log_pos (by linarith)
  · exact Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hlr (by norm_num))
  · exact hq

/-- **Far zeros, any order `m ≥ 1`:** the analogue of `far_sum_le`, with the condition
`a < m log(l/17)²` in place of `a < 2 log(l/17)²`. -/
theorem far_sum_le_m {a l r : ℝ} {m : ℕ} (hm : 0 < m) (ha : 0 ≤ a) (hl : 17 < l) (hlr : l ≤ r)
    (hfar : a < m * Real.log (l / 17) ^ 2) :
    weightedSum l r (Phi a m) ≤
      (1 / (2 * Real.pi) + q l) * farPrimitive a d m (Real.log (l / 17)) / 17 ^ m +
        2 * rosserR 1.588 l * Phi a m l := by
  have hl0 : 0 < l := by linarith
  have hl1 : 1 < l := by linarith
  have hlπ : 2 * Real.pi < l := by linarith [Real.pi_lt_d4]
  have hlogl : 0 < Real.log (l / 17) := Real.log_pos (by linarith)
  have hφ := fun t (ht : t ∈ Icc l r) => hasDerivAt_Phi a m (hl.trans_le ht.1)
  have hdec : ∀ t ∈ Ioo l r, PhiDerivative a m t ≤ 0 := by
    intro t ht
    have ht17 : 17 < t := hl.trans ht.1
    have hloglt : Real.log (l / 17) ≤ Real.log (t / 17) :=
      Real.log_le_log (by positivity : 0 < l / 17)
        (div_le_div_of_nonneg_right ht.1.le (by norm_num))
    have hs := pow_le_pow_left₀ hlogl.le hloglt 2
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    apply PhiDerivative_nonpos m ht17
    nlinarith [mul_le_mul_of_nonneg_left hs hm0, sq_nonneg (Real.log (t / 17))]
  have he := weightedSum_le_decreasing_q (by linarith : 7 ≤ l) hlr hφ
    (integrable_PhiDerivative_m a m hl hlr) hdec
    (fun t ht => (Phi_pos a m (hl0.trans_le ht.1)).le)
  have heq : (∫ t in l..r, Real.log (t / (2 * Real.pi)) * Phi a m t) =
      (∫ t in l..r, heightIntegrand a d m t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact Phi_mul_log_eq_heightIntegrand a m (hl0.trans_le ht.1)
  rw [heq] at he
  have hc : 0 ≤ 1 / (2 * Real.pi) + q l := by
    have hq := q_nonneg hl1 hlπ
    positivity
  have hi := mul_le_mul_of_nonneg_left (integral_height_far_le_m hm ha d_pos.le hl hlr hfar) hc
  have hi' : (1 / (2 * Real.pi) + q l) * (∫ t in l..r, heightIntegrand a d m t) ≤
      (1 / (2 * Real.pi) + q l) * farPrimitive a d m (Real.log (l / 17)) / 17 ^ m := by
    convert hi using 1
    ring
  exact he.trans (add_le_add hi' le_rfl)

end TernaryGoldbach.RSBounds.SchoenfeldWeightedZerosM
