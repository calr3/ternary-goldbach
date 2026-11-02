import TernaryGoldbach.Helfgott.Eta2

/-!
# Moments of `η₂`

`∫ η₂ = 1`, `∫ w^{-1/2} η₂ = 24 − 16√2 ≤ 1.37259`, `∫ w^{-1} η₂ = 4 (log 2)² ≤ 1.92182`,
`∫ w^{-3/2} η₂ = 48 − 32√2 ≤ 2.74517` (all over `w > 0`) — the values used in [H, Cor 9.3.3].
-/

open Real MeasureTheory Set intervalIntegral

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (eta2 eta2_eq_left eta2_eq_right eta2_eq_zero continuous_eta2
  integral_abs_eta2)

theorem eta2_nonneg (t : ℝ) : 0 ≤ eta2 t := by
  unfold TernaryGoldbach.Helfgott.eta2; split_ifs <;> positivity

/-- `∫_{r>0} η₂(r) g(r) dr` split into the two explicit pieces. -/
theorem setIntegral_eta2_mul {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (1 / 4) 1)) :
    ∫ r in Ioi 0, eta2 r * g r =
      (∫ r in (1 / 4 : ℝ)..(1 / 2), 4 * Real.log (4 * r) * g r) +
        ∫ r in (1 / 2 : ℝ)..1, -4 * Real.log r * g r := by
  have h1 : ∫ r in Ioi 0, eta2 r * g r = ∫ r in Ioc (1 / 4 : ℝ) 1, eta2 r * g r := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun r (hr : r ∈ Ioc (1 / 4 : ℝ) 1) => mem_Ioi.2 (by linarith [hr.1])) fun r hr => ?_
    rw [eta2_eq_zero (fun h => hr.2 ⟨h.1, h.2.le⟩), zero_mul]
  have hc : ContinuousOn (fun r => eta2 r * g r) (Icc (1 / 4) 1) :=
    continuous_eta2.continuousOn.mul hg
  rw [h1, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
      ((hc.mono (Icc_subset_Icc le_rfl (by norm_num))).intervalIntegrable_of_Icc (by norm_num))
      ((hc.mono (Icc_subset_Icc (by norm_num) le_rfl)).intervalIntegrable_of_Icc (by norm_num))]
  congr 1
  · refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (by norm_num)] at hr
    simp only [eta2_eq_left hr.1 hr.2]
  · refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (by norm_num)] at hr
    simp only [eta2_eq_right hr.1 hr.2]

theorem integrableOn_eta2_mul {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (1 / 4) 1)) :
    IntegrableOn (fun r => eta2 r * g r) (Ioi 0) := by
  have hc : ContinuousOn (fun r => eta2 r * g r) (Icc (1 / 4) 1) :=
    continuous_eta2.continuousOn.mul hg
  have hI : IntegrableOn (fun r => eta2 r * g r) (Icc (1 / 4) 1) := hc.integrableOn_Icc
  refine hI.of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr => ?_
  rw [eta2_eq_zero (fun h' => hr.2 ⟨h'.1.le, h'.2.le⟩), zero_mul]

/-- `∫_{r>0} η₂ = 1`. -/
theorem moment0 : ∫ r in Ioi 0, eta2 r = 1 := by
  rw [← integral_abs_eta2, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun r => (abs_of_nonneg (eta2_nonneg r)).symm)
  · intro r hr
    exact eta2_eq_zero fun h => hr (mem_Ioi.2 (by linarith [h.1]))

theorem hasDerivAt_log_mul {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (fun r => Real.log (c * r)) (1 / r) r := by
  have h : HasDerivAt (fun y => c * y) c r := by simpa using (hasDerivAt_id r).const_mul c
  have := h.log (by positivity : c * r ≠ 0)
  convert this using 1; field_simp

/-- `d/dr [8√r (log(cr) − 2)] = 4 log(cr)/√r`. -/
theorem hasDerivAt_Fhalf {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (fun r => 8 * √r * (Real.log (c * r) - 2)) (4 * Real.log (c * r) * (1 / √r)) r := by
  have h1 := (Real.hasDerivAt_sqrt hr.ne').const_mul 8
  have h2 := (hasDerivAt_log_mul hc hr).sub_const 2
  have := h1.mul h2
  convert this using 1
  have hs : 0 < √r := Real.sqrt_pos.2 hr
  have hss : √r * √r = r := Real.mul_self_sqrt hr.le
  field_simp
  nlinarith [hss]

/-- `d/dr [-8 (log(cr) + 2)/√r] = 4 log(cr)/(r√r)`. -/
theorem hasDerivAt_F3half {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (fun r => -8 * (Real.log (c * r) + 2) / √r)
      (4 * Real.log (c * r) * (1 / (r * √r))) r := by
  have hs : 0 < √r := Real.sqrt_pos.2 hr
  have h1 := ((hasDerivAt_log_mul hc hr).add_const 2).const_mul (-8)
  have h2 := Real.hasDerivAt_sqrt hr.ne'
  have := h1.div h2 hs.ne'
  convert this using 1
  field_simp
  simp only [Real.sq_sqrt hr.le]
  ring

/-- `d/dr [2 (log(cr))²] = 4 log(cr)/r`. -/
theorem hasDerivAt_Fone {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (fun r => 2 * Real.log (c * r) ^ 2) (4 * Real.log (c * r) * (1 / r)) r := by
  have := ((hasDerivAt_log_mul hc hr).pow 2).const_mul 2
  convert this using 1; push_cast; ring

/-- FTC on `[a, b] ⊆ (0, ∞)`. -/
theorem integral_eq_of_deriv {F f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hF : ∀ r, 0 < r → HasDerivAt F (f r) r) (hf : ContinuousOn f (Icc a b)) :
    ∫ r in a..b, f r = F b - F a := by
  refine integral_eq_sub_of_hasDerivAt (fun r hr => hF r ?_) (hf.intervalIntegrable_of_Icc hab)
  rw [uIcc_of_le hab] at hr; linarith [hr.1]

theorem contOn_log_mul {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc a b)) :
    ContinuousOn (fun r => 4 * Real.log (c * r) * g r) (Icc a b) := by
  refine (continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).log fun r hr => ?_)).mul hg
  show c * r ≠ 0
  have : 0 < r := by linarith [hr.1]
  positivity

theorem contOn_inv_sqrt {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun r : ℝ => 1 / √r) (Icc a b) :=
  continuousOn_const.div (Real.continuous_sqrt.continuousOn) fun r hr =>
    (Real.sqrt_pos.2 (by linarith [hr.1])).ne'

theorem contOn_inv {a b : ℝ} (ha : 0 < a) : ContinuousOn (fun r : ℝ => 1 / r) (Icc a b) :=
  continuousOn_const.div continuousOn_id fun r hr => ne_of_gt (show (0:ℝ) < r by linarith [hr.1])

theorem contOn_inv_mul_sqrt {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun r : ℝ => 1 / (r * √r)) (Icc a b) :=
  continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn) fun r hr => by
    have : 0 < r := by linarith [hr.1]
    show r * √r ≠ 0
    positivity

theorem sqrt_half_bounds : (0.70710678 : ℝ) ≤ √(1 / 2) ∧ √(1 / 2) ≤ 0.70710679 := by
  refine ⟨Real.le_sqrt_of_sq_le (by norm_num), ?_⟩
  calc √(1 / 2 : ℝ) ≤ √(0.70710679 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = 0.70710679 := Real.sqrt_sq (by norm_num)

/-- `∫_{r>0} η₂(r)/√r = 24 − 32/√2 ≤ 1.37259`. -/
theorem moment_half : ∫ r in Ioi 0, eta2 r * (1 / √r) ≤ 1.37259 := by
  rw [setIntegral_eta2_mul (contOn_inv_sqrt (by norm_num))]
  have hL := integral_eq_of_deriv (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_Fhalf (c := 4) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (contOn_inv_sqrt (by norm_num)))
  have hR := integral_eq_of_deriv (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_Fhalf (c := 1) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (contOn_inv_sqrt (by norm_num)))
  have eR : ∫ r in (1 / 2 : ℝ)..1, -4 * Real.log r * (1 / √r) =
      -∫ r in (1 / 2 : ℝ)..1, 4 * Real.log (1 * r) * (1 / √r) := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext r; rw [one_mul]; ring
  rw [hL, eR, hR]
  simp only [one_mul]
  have e1 : Real.log (4 * (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  have e2 : Real.log (4 * (1 / 4 : ℝ)) = 0 := by norm_num
  have e3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have e4 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e1, e2, e3, e4, Real.log_one, Real.sqrt_one]
  obtain ⟨hs1, hs2⟩ := sqrt_half_bounds
  have := Real.log_two_lt_d9
  nlinarith

/-- `∫_{r>0} η₂(r)/r = 4 (log 2)² ≤ 1.92182`. -/
theorem moment_one : ∫ r in Ioi 0, eta2 r * (1 / r) ≤ 1.92182 := by
  rw [setIntegral_eta2_mul (contOn_inv (by norm_num))]
  have hL := integral_eq_of_deriv (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_Fone (c := 4) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (contOn_inv (by norm_num)))
  have hR := integral_eq_of_deriv (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_Fone (c := 1) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (contOn_inv (by norm_num)))
  have eR : ∫ r in (1 / 2 : ℝ)..1, -4 * Real.log r * (1 / r) =
      -∫ r in (1 / 2 : ℝ)..1, 4 * Real.log (1 * r) * (1 / r) := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext r; rw [one_mul]; ring
  rw [hL, eR, hR]
  simp only [one_mul]
  have e1 : Real.log (4 * (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  have e2 : Real.log (4 * (1 / 4 : ℝ)) = 0 := by norm_num
  have e3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  rw [e1, e2, e3, Real.log_one]
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_two_gt_d9
  nlinarith

/-- `∫_{r>0} η₂(r)/(r√r) = 48 − 64/√2 ≤ 2.74517`. -/
theorem moment_3half : ∫ r in Ioi 0, eta2 r * (1 / (r * √r)) ≤ 2.74517 := by
  rw [setIntegral_eta2_mul (contOn_inv_mul_sqrt (by norm_num))]
  have hL := integral_eq_of_deriv (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_F3half (c := 4) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (contOn_inv_mul_sqrt (by norm_num)))
  have hR := integral_eq_of_deriv (a := 1 / 2) (b := 1) (by norm_num) (by norm_num)
    (fun r hr => hasDerivAt_F3half (c := 1) (by norm_num) hr)
    (contOn_log_mul (by norm_num) (by norm_num) (contOn_inv_mul_sqrt (by norm_num)))
  have eR : ∫ r in (1 / 2 : ℝ)..1, -4 * Real.log r * (1 / (r * √r)) =
      -∫ r in (1 / 2 : ℝ)..1, 4 * Real.log (1 * r) * (1 / (r * √r)) := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext r; rw [one_mul]; ring
  rw [hL, eR, hR]
  simp only [one_mul]
  have e1 : Real.log (4 * (1 / 2 : ℝ)) = Real.log 2 := by norm_num
  have e2 : Real.log (4 * (1 / 4 : ℝ)) = 0 := by norm_num
  have e3 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have e4 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e1, e2, e3, e4, Real.log_one, Real.sqrt_one]
  obtain ⟨hs1, hs2⟩ := sqrt_half_bounds
  have hpos : 0 < √(1 / 2 : ℝ) := by linarith
  have := Real.log_two_lt_d9
  have h3 : -8 * (Real.log 2 + 2) / √(1 / 2 : ℝ) - -8 * (0 + 2) / (1 / 2) +
      -(-8 * (0 + 2) / 1 - -8 * (-Real.log 2 + 2) / √(1 / 2 : ℝ)) =
      48 - 32 / √(1 / 2 : ℝ) := by field_simp; ring
  rw [h3, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hpos]
  nlinarith

end TernaryGoldbach.MajorArcs
