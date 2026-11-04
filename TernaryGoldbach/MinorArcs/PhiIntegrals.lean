import TernaryGoldbach.MinorArcs.Prop1123

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# Integrals of `φ(w) = w² e^{-w²/2}` needed in Prop 11.2.3′

* `integral_exp_Ioc_ge`: `∫_0^1 e^{-w²/2} ≥ 0.8556` (Taylor, `Real.exp_bound`);
* `integral_phi_Ioi_one`: `∫_1^∞ φ = e^{-1/2} + ∫_1^∞ e^{-w²/2}` (`φ = e^{-w²/2} + (-w e^{-w²/2})'`);
* **`integral_max_inv_phi_le`**: `∫_{w₀}^∞ max(1, 1/w) φ(w) dw ≤ 1.398` for `0 < w₀ ≤ 1`
  (`= ∫_{w₀}^1 w e^{-w²/2} + ∫_1^∞ φ ≤ 1 + √(2π)/2 - ∫_0^1 e^{-w²/2}`);
* `integral_phi_Ioo_le`: `∫_0^{w₀} φ ≤ w₀³/3`.

Proved, with no `sorry`.
-/

open Real Set MeasureTheory Filter Topology

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (phi)

theorem exp_neg_ge_poly {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 - u ^ 5 / 120 - u ^ 6 * (7 / 4320) ≤ rexp (-u) := by
  have h := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg hu]; exact hu1) (n := 6)
    (by norm_num)
  rw [abs_neg, abs_of_nonneg hu] at h
  have h' := (abs_le.1 h).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at h'
  nlinarith [h']

theorem integral_exp_Ioc_ge : 0.8556 ≤ ∫ w in Ioc (0:ℝ) 1, rexp (-w ^ 2 / 2) := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  set P : ℝ → ℝ := fun w => 1 - w ^ 2 / 2 + (w ^ 2 / 2) ^ 2 / 2 - (w ^ 2 / 2) ^ 3 / 6 +
    (w ^ 2 / 2) ^ 4 / 24 - (w ^ 2 / 2) ^ 5 / 120 - (w ^ 2 / 2) ^ 6 * (7 / 4320) with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hle : ∫ w in (0:ℝ)..1, P w ≤ ∫ w in (0:ℝ)..1, rexp (-w ^ 2 / 2) := by
    refine intervalIntegral.integral_mono_on zero_le_one (hPc.intervalIntegrable _ _)
      ((by fun_prop : Continuous fun w : ℝ => rexp (-w ^ 2 / 2)).intervalIntegrable _ _) ?_
    intro w hw
    have := exp_neg_ge_poly (u := w ^ 2 / 2) (by positivity) (by nlinarith [hw.1, hw.2])
    rw [show -w ^ 2 / 2 = -(w ^ 2 / 2) by ring]
    simpa [hP] using this
  have hval : ∫ w in (0:ℝ)..1, P w = 1 - 1 / 6 + 1 / 40 - 1 / 336 + 1 / 3456 - 1 / 42240 -
      7 / 4320 / (64 * 13) := by
    set Fp : ℝ → ℝ := fun w => w - w ^ 3 / 6 + w ^ 5 / 40 - w ^ 7 / 336 + w ^ 9 / 3456 -
      w ^ 11 / 42240 - 7 / 4320 * w ^ 13 / (64 * 13)
    have hd : ∀ w ∈ uIcc (0:ℝ) 1, HasDerivAt Fp (P w) w := by
      intro w _
      have := ((((((((hasDerivAt_id w).sub ((hasDerivAt_pow 3 w).div_const 6)).add
        ((hasDerivAt_pow 5 w).div_const 40)).sub ((hasDerivAt_pow 7 w).div_const 336)).add
        ((hasDerivAt_pow 9 w).div_const 3456)).sub ((hasDerivAt_pow 11 w).div_const 42240)).sub
        (((hasDerivAt_pow 13 w).const_mul (7 / 4320)).div_const (64 * 13))))
      convert this using 1
      · ext x; simp only [Fp, Pi.sub_apply, Pi.add_apply, id]
      · simp only [P]; push_cast; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hPc.intervalIntegrable _ _)]
    simp only [Fp]; norm_num
  rw [hval] at hle
  linarith [show (0.8556 : ℝ) ≤ 1 - 1 / 6 + 1 / 40 - 1 / 336 + 1 / 3456 - 1 / 42240 -
      7 / 4320 / (64 * 13) by norm_num]

theorem hasDerivAt_neg_mul_exp (w : ℝ) :
    HasDerivAt (fun w => -w * rexp (-w ^ 2 / 2)) (phi w - rexp (-w ^ 2 / 2)) w := by
  have h1 : HasDerivAt (fun w : ℝ => -w ^ 2 / 2) (-w) w := by
    have := ((hasDerivAt_pow 2 w).neg).div_const 2
    convert this using 1; push_cast; ring
  have := (hasDerivAt_id w).neg.mul h1.exp
  convert this using 1
  · ext; simp
  · simp only [phi, Pi.neg_apply, id_eq]; ring

theorem integrable_exp_neg_sq_half : Integrable fun w : ℝ => rexp (-w ^ 2 / 2) := by
  have := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  refine this.congr (Eventually.of_forall fun w => ?_)
  simp only; ring_nf

theorem integral_phi_Ioi_one :
    ∫ w in Ioi (1:ℝ), phi w = rexp (-(1 / 2)) + ∫ w in Ioi (1:ℝ), rexp (-w ^ 2 / 2) := by
  have hφ : Integrable phi := integrable_phi
  have hd : ∀ w ∈ Ici (1:ℝ), HasDerivAt (fun w => -w * rexp (-w ^ 2 / 2))
      (phi w - rexp (-w ^ 2 / 2)) w := fun w _ => hasDerivAt_neg_mul_exp w
  have hlim : Tendsto (fun w : ℝ => -w * rexp (-w ^ 2 / 2)) atTop (𝓝 0) := by
    have h2 := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    -- `|w e^{-w²/2}| ≤ w e^{-w}` for `w ≥ 2`
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop (2:ℝ)] with w hw
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by linarith), abs_of_pos (Real.exp_pos _),
      pow_one]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by linarith)
  have hint := (hφ.sub integrable_exp_neg_sq_half).integrableOn (s := Ioi 1)
  have := integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim
  rw [integral_sub hφ.integrableOn integrable_exp_neg_sq_half.integrableOn] at this
  have e : -(1:ℝ) * rexp (-1 ^ 2 / 2) = -rexp (-(1 / 2)) := by norm_num
  rw [e] at this
  linarith

theorem integral_mul_exp_Ioc_le {w₀ : ℝ} (hw₀1 : w₀ ≤ 1) :
    ∫ w in Ioc w₀ 1, w * rexp (-w ^ 2 / 2) ≤ 1 - rexp (-(1 / 2)) := by
  rw [← intervalIntegral.integral_of_le hw₀1]
  have hd : ∀ w ∈ uIcc w₀ 1, HasDerivAt (fun w => -rexp (-w ^ 2 / 2)) (w * rexp (-w ^ 2 / 2)) w := by
    intro w _
    have h1 : HasDerivAt (fun w : ℝ => -w ^ 2 / 2) (-w) w := by
      have := ((hasDerivAt_pow 2 w).neg).div_const 2
      convert this using 1; push_cast; ring
    have := h1.exp.neg
    convert this using 1; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun w : ℝ => w * rexp (-w ^ 2 / 2)).intervalIntegrable _ _)]
  have : rexp (-w₀ ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have e : -1 ^ 2 / 2 = -(1 / 2 : ℝ) := by norm_num
  simp only [e]
  linarith

/-- **`∫_{w₀}^∞ max(1, 1/w) φ ≤ 1.398`**. -/
theorem integral_max_inv_phi_le {w₀ : ℝ} (hw₀ : 0 < w₀) (hw₀1 : w₀ ≤ 1) :
    ∫ w in Ici w₀, max 1 (1 / w) * phi w ≤ 1.398 := by
  have hsplit : Ici w₀ = Ioc w₀ 1 ∪ Ioi 1 ∪ {w₀} := by
    ext w; simp only [mem_Ici, mem_union, mem_Ioc, mem_Ioi, mem_singleton_iff]
    constructor
    · intro h; rcases eq_or_lt_of_le h with h | h
      · exact Or.inr h.symm
      · left; by_cases h1 : w ≤ 1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr (by linarith)
    · rintro ((⟨h, _⟩ | h) | h) <;> linarith
  have hint : IntegrableOn (fun w => max 1 (1 / w) * phi w) (Ici w₀) := by
    refine (integrable_phi.const_mul (max 1 (1 / w₀))).integrableOn.mono' ?_ ?_
    · exact ((measurable_const.max (measurable_const.div measurable_id)).mul
        (by unfold phi; fun_prop)).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun w (hw : w₀ ≤ w) => ?_)
      have hw0 : 0 < w := lt_of_lt_of_le hw₀ hw
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_max_of_le_left zero_le_one)
        (phi_nonneg w))]
      refine mul_le_mul_of_nonneg_right (max_le_max le_rfl ?_) (phi_nonneg w)
      exact one_div_le_one_div_of_le hw₀ hw
  rw [integral_Ici_eq_integral_Ioi, ← Ioc_union_Ioi_eq_Ioi hw₀1,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set (fun w hw => le_of_lt hw.1)) (hint.mono_set (fun w hw => le_of_lt
        (lt_of_le_of_lt hw₀1 hw)))]
  have e1 : ∫ w in Ioc w₀ 1, max 1 (1 / w) * phi w = ∫ w in Ioc w₀ 1, w * rexp (-w ^ 2 / 2) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun w hw => ?_
    have hw0 : 0 < w := lt_trans hw₀ hw.1
    rw [max_eq_right (by rw [le_div_iff₀ hw0]; linarith [hw.2])]
    unfold phi; field_simp
  have e2 : ∫ w in Ioi 1, max 1 (1 / w) * phi w = ∫ w in Ioi (1:ℝ), phi w := by
    refine setIntegral_congr_fun measurableSet_Ioi fun w (hw : 1 < w) => ?_
    rw [max_eq_left (by rw [div_le_iff₀ (by linarith)]; linarith), one_mul]
  rw [e1, e2, integral_phi_Ioi_one]
  have h1 := integral_mul_exp_Ioc_le hw₀1
  -- `∫_1^∞ e^{-w²/2} = √(2π)/2 - ∫_0^1 e^{-w²/2}`
  have hg := integral_gaussian_Ioi (1 / 2)
  have hg' : ∫ w in Ioi (0:ℝ), rexp (-w ^ 2 / 2) = √(π / (1 / 2)) / 2 := by
    rw [← hg]; congr 1; ext w; ring_nf
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
    measurableSet_Ioi integrable_exp_neg_sq_half.integrableOn
    integrable_exp_neg_sq_half.integrableOn] at hg'
  have h2 := integral_exp_Ioc_ge
  have hpi : √(π / (1 / 2)) ≤ 2.50664 := by
    rw [Real.sqrt_le_left (by norm_num), div_div_eq_mul_div]
    have := Real.pi_lt_d6; nlinarith
  linarith

theorem integral_phi_Ioo_le {w₀ : ℝ} (hw₀ : 0 ≤ w₀) : ∫ w in Ioo 0 w₀, phi w ≤ w₀ ^ 3 / 3 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hw₀]
  have h : ∫ w in (0:ℝ)..w₀, phi w ≤ ∫ w in (0:ℝ)..w₀, w ^ 2 := by
    refine intervalIntegral.integral_mono_on hw₀ (integrable_phi.intervalIntegrable)
      ((continuous_pow 2).intervalIntegrable _ _) fun w _ => ?_
    unfold phi
    have : rexp (-w ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [sq_nonneg w]
  rw [integral_pow] at h
  linarith [show (w₀ ^ (2 + 1) - 0 ^ (2 + 1)) / (2 + 1 : ℝ) = w₀ ^ 3 / 3 by norm_num]

end TernaryGoldbach.MinorArcs
