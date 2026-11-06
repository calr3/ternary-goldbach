import TernaryGoldbach.MinorArcs.TypeIIReduction

/-!
# Integrals for the Type II total [H, §6.2.3]
-/

open Real Finset MeasureTheory

namespace TernaryGoldbach.MinorArcs

/-- `∫_V^{x/U} H₂(x/WU) dW/W = ∫_1^{x/UV} H₂(s) ds/s ≤ 0.15107 log(x/UV) + 0.0231` ([H, (6.25)],
with the corrected (5.36)), and the integrand is integrable. -/
theorem integral_H2_comp {x U V : ℝ} (hx : 0 < x) (hU : 0 < U) (hV : 0 < V) (hVU : V ≤ x / U) :
    IntervalIntegrable (fun W => H2 (x / (W * U)) / W) volume V (x / U) ∧
    ∫ W in V..x / U, H2 (x / (W * U)) / W ≤ 0.15107 * Real.log (x / (U * V)) + 0.0231 := by
  set φ : ℝ → ℝ := fun W => x / (W * U)
  set φ' : ℝ → ℝ := fun W => -(x / (U * W ^ 2))
  set G : ℝ → ℝ := fun s => H2 s / s
  have hxU : 0 < x / U := by positivity
  have hmin : min V (x / U) = V := min_eq_left hVU
  have hmax : max V (x / U) = x / U := max_eq_right hVU
  have hcont : ContinuousOn φ (Set.uIcc V (x / U)) := by
    refine ContinuousOn.div continuousOn_const (continuousOn_id.mul continuousOn_const) ?_
    intro W hW; rw [Set.uIcc_of_le hVU] at hW
    exact (mul_pos (lt_of_lt_of_le hV hW.1) hU).ne'
  have hderiv : ∀ W ∈ Set.Ioo (min V (x / U)) (max V (x / U)), HasDerivAt φ (φ' W) W := by
    intro W hW
    rw [hmin, hmax] at hW
    have hW0 : 0 < W := lt_trans hV hW.1
    have := ((hasDerivAt_id W).mul_const U).inv (mul_pos hW0 hU).ne' |>.const_mul x
    convert this using 1
    · ext W'; simp only [φ, div_eq_mul_inv]; rfl
    · simp only [φ', id]; field_simp
  have hnonpos : ∀ W ∈ Set.Ioo (min V (x / U)) (max V (x / U)), φ' W ≤ 0 := by
    intro W _; simp only [φ']; have : 0 ≤ x / (U * W ^ 2) := by positivity
    linarith
  have hφV : φ V = x / (U * V) := by simp only [φ]; rw [mul_comm]
  have hφ1 : φ (x / U) = 1 := by simp only [φ]; field_simp
  have heq : ∀ W, 0 < W → H2 (x / (W * U)) / W = -((G ∘ φ) W * φ' W) := by
    intro W hW
    simp only [Function.comp, G, φ, φ']
    field_simp
  have hGint : IntervalIntegrable G volume (φ V) (φ (x / U)) := by
    rw [hφV, hφ1]; exact (intervalIntegrable_H2_div _).symm
  have hint1 := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos hcont hderiv hnonpos).2 hGint
  have hint : IntervalIntegrable (fun W => H2 (x / (W * U)) / W) volume V (x / U) := by
    refine hint1.neg.congr ?_
    rw [Set.uIoc_of_le hVU]
    intro W hW
    simp only [Pi.neg_apply]
    exact (heq W (lt_trans hV hW.1)).symm
  refine ⟨hint, ?_⟩
  have hI : ∫ W in V..x / U, H2 (x / (W * U)) / W = ∫ s in (1 : ℝ)..x / (U * V), G s := by
    rw [intervalIntegral.integral_congr (g := fun W => -((G ∘ φ) W * φ' W)) (fun W hW => by
        rw [Set.uIcc_of_le hVU] at hW; exact heq W (lt_of_lt_of_le hV hW.1)),
      intervalIntegral.integral_neg, intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos hcont hderiv hnonpos,
      hφV, hφ1, intervalIntegral.integral_symm, neg_neg]
  rw [hI]
  exact integral_H2_le (by rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hU] at hVU; linarith)


/-- `∫_a^b dW/(W log(W/c)) = log log(b/c) - log log(a/c)` for `0 < c < a ≤ b`. -/
theorem integral_inv_mul_log {c a b : ℝ} (hc : 0 < c) (hca : c < a) (hab : a ≤ b) :
    ∫ W in a..b, 1 / (W * Real.log (W / c)) =
      Real.log (Real.log (b / c)) - Real.log (Real.log (a / c)) := by
  have hpos : ∀ W ∈ Set.uIcc a b, 0 < W ∧ 0 < Real.log (W / c) := by
    intro W hW; rw [Set.uIcc_of_le hab] at hW
    have : c < W := lt_of_lt_of_le hca hW.1
    exact ⟨by linarith, Real.log_pos (by rw [one_lt_div hc]; exact this)⟩
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun W => Real.log (Real.log (W / c))) (fun W hW => ?_) ?_
  · obtain ⟨hW0, hL⟩ := hpos W hW
    have h1 : HasDerivAt (fun W => W / c) (1 / c) W := (hasDerivAt_id W).div_const c
    have h2 := (h1.log (by positivity)).log hL.ne'
    convert h2 using 1
    field_simp
  · refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (continuousOn_id.mul ?_) fun W hW => ?_
    · exact ContinuousOn.log (continuousOn_id.div_const c) fun W hW =>
        (div_pos (hpos W hW).1 hc).ne'
    · exact (mul_pos (hpos W hW).1 (hpos W hW).2).ne'

/-- `∫_a^b dW/(W √W) = 2/√a - 2/√b ≤ 2/√a`. -/
theorem integral_inv_mul_sqrt_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ W in a..b, 1 / (W * √W) ≤ 2 / √a := by
  have hpos : ∀ W ∈ Set.uIcc a b, 0 < W := by
    intro W hW; rw [Set.uIcc_of_le hab] at hW; exact lt_of_lt_of_le ha hW.1
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun W => -2 / √W)
    (f' := fun W => 1 / (W * √W)) (a := a) (b := b) (fun W hW => by
      have hW := hpos W hW
      have h1 := ((Real.hasDerivAt_sqrt hW.ne').inv (Real.sqrt_pos.2 hW).ne').const_mul (-2)
      convert h1 using 1
      · ext; simp [div_eq_mul_inv]
      · have : √W * √W = W := Real.mul_self_sqrt hW.le
        field_simp
        nlinarith [Real.sqrt_pos.2 hW])
    (ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      fun W hW => (mul_pos (hpos W hW) (Real.sqrt_pos.2 (hpos W hW))).ne'))
  rw [hI]
  have : 0 < √b := Real.sqrt_pos.2 (lt_of_lt_of_le ha hab)
  have : 0 < 2 / √b := by positivity
  have e1 : -2 / √b = -(2 / √b) := by ring
  have e2 : -2 / √a = -(2 / √a) := by ring
  rw [e1, e2]; linarith

/-- `∫_a^b dW/√W = 2√b - 2√a`. -/
theorem integral_inv_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ W in a..b, 1 / √W = 2 * √b - 2 * √a := by
  have hpos : ∀ W ∈ Set.uIcc a b, 0 < W := by
    intro W hW; rw [Set.uIcc_of_le hab] at hW; exact lt_of_lt_of_le ha hW.1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun W => 2 * √W)
    (fun W hW => ?_) ?_
  · have hW := hpos W hW
    convert (Real.hasDerivAt_sqrt hW.ne').const_mul 2 using 1
    field_simp
  · exact ContinuousOn.intervalIntegrable (continuousOn_const.div
      Real.continuous_sqrt.continuousOn fun W hW => (Real.sqrt_pos.2 (hpos W hW)).ne')


/-- A crude form of [H, (6.22)]: for `ce ≤ a ≤ b`,
`∫_a^b dW/(√W √(log(W/c))) ≤ 2e√c + 4√(b/log(b/c))`. ([H] has `2.3 √(T/log T)` after a numerical
check; we split at `ce²` instead.) -/
theorem integral_inv_sqrt_log_le {c a b : ℝ} (hc : 0 < c) (hca : c * rexp 1 ≤ a) (hab : a ≤ b) :
    ∫ W in a..b, 1 / (√W * √(Real.log (W / c))) ≤
      2 * rexp 1 * √c + 4 * √(b / Real.log (b / c)) := by
  have he : 1 < rexp 1 := by have := Real.add_one_lt_exp (one_ne_zero); linarith
  have ha : 0 < a := lt_of_lt_of_le (by positivity) hca
  have hL1 : ∀ W, c * rexp 1 ≤ W → 1 ≤ Real.log (W / c) := by
    intro W hW
    rw [Real.le_log_iff_exp_le (div_pos (lt_of_lt_of_le (by positivity) hW) hc),
      le_div_iff₀ hc]; linarith
  set f : ℝ → ℝ := fun W => 1 / (√W * √(Real.log (W / c)))
  have hcontf : ContinuousOn f (Set.Icc a b) := by
    refine continuousOn_const.div (Real.continuous_sqrt.continuousOn.mul ?_) fun W hW => ?_
    · refine Real.continuous_sqrt.comp_continuousOn (ContinuousOn.log
        (continuousOn_id.div_const c) fun W hW => ?_)
      exact (div_pos (lt_of_lt_of_le ha hW.1) hc).ne'
    · have h1 := lt_of_lt_of_le ha hW.1
      have h2 := hL1 W (hca.trans hW.1)
      exact (mul_pos (Real.sqrt_pos.2 h1) (Real.sqrt_pos.2 (by linarith))).ne'
  set m := max a (min b (c * rexp 1 ^ 2))
  have ham : a ≤ m := le_max_left _ _
  have hmb : m ≤ b := max_le hab (min_le_left _ _)
  have hint : ∀ u v, a ≤ u → u ≤ v → v ≤ b → IntervalIntegrable f volume u v := fun u v hu huv hv =>
    (hcontf.mono (Set.Icc_subset_Icc hu hv)).intervalIntegrable_of_Icc huv
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a m le_rfl ham hmb)
    (hint m b ham hmb le_rfl)]
  have hF0 : 0 ≤ 4 * √(b / Real.log (b / c)) := by positivity
  -- First piece: `f ≤ 1/√W`.
  have h1 : ∫ W in a..m, f W ≤ 2 * rexp 1 * √c := by
    calc ∫ W in a..m, f W ≤ ∫ W in a..m, 1 / √W := by
          refine intervalIntegral.integral_mono_on ham (hint a m le_rfl ham hmb) ?_ fun W hW => ?_
          · exact ContinuousOn.intervalIntegrable_of_Icc ham (continuousOn_const.div
              Real.continuous_sqrt.continuousOn fun W hW => (Real.sqrt_pos.2
                (lt_of_lt_of_le ha hW.1)).ne')
          · have hW0 := lt_of_lt_of_le ha hW.1
            have hL := hL1 W (hca.trans hW.1)
            simp only [f]
            rw [div_le_div_iff₀ (mul_pos (Real.sqrt_pos.2 hW0) (Real.sqrt_pos.2 (by linarith)))
              (Real.sqrt_pos.2 hW0), one_mul, one_mul]
            exact le_mul_of_one_le_right (Real.sqrt_nonneg _) (by
              rw [Real.one_le_sqrt]; exact hL)
      _ = 2 * √m - 2 * √a := integral_inv_sqrt ha ham
      _ ≤ 2 * rexp 1 * √c := by
          rcases le_or_gt (min b (c * rexp 1 ^ 2)) a with h | h
          · have : m = a := max_eq_left h
            rw [this]; simp; positivity
          · have : m = min b (c * rexp 1 ^ 2) := max_eq_right h.le
            have hm : √m ≤ √(c * rexp 1 ^ 2) := Real.sqrt_le_sqrt (this ▸ min_le_right _ _)
            rw [Real.sqrt_mul hc.le, Real.sqrt_sq (by positivity)] at hm
            have : 0 ≤ √a := Real.sqrt_nonneg a
            nlinarith
  -- Second piece: `f ≤ 4F'` with `F = √(W/log(W/c))`, valid for `log(W/c) ≥ 2`.
  have h2 : ∫ W in m..b, f W ≤ 4 * √(b / Real.log (b / c)) := by
    rcases hmb.eq_or_lt with heq | hlt
    · rw [heq, intervalIntegral.integral_same]; exact hF0
    have hm2 : c * rexp 1 ^ 2 ≤ m := by
      have : min b (c * rexp 1 ^ 2) = c * rexp 1 ^ 2 := by
        by_contra hne
        have : min b (c * rexp 1 ^ 2) = b := (min_choice _ _).resolve_right hne
        have := le_max_right a (min b (c * rexp 1 ^ 2)); linarith
      rw [← this]; exact le_max_right _ _
    have hL2 : ∀ W, m ≤ W → 2 ≤ Real.log (W / c) := by
      intro W hW
      rw [Real.le_log_iff_exp_le (div_pos (by nlinarith [Real.exp_pos 1]) hc), le_div_iff₀ hc,
        show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    set F : ℝ → ℝ := fun W => √(W / Real.log (W / c))
    set F' : ℝ → ℝ := fun W => (Real.log (W / c) - 1) / Real.log (W / c) ^ 2 /
      (2 * √(W / Real.log (W / c)))
    have hW0 : ∀ W, m ≤ W → 0 < W := fun W hW => lt_of_lt_of_le (lt_of_lt_of_le ha ham) hW
    have hderiv : ∀ W ∈ Set.uIcc m b, HasDerivAt F (F' W) W := by
      intro W hW; rw [Set.uIcc_of_le hmb] at hW
      have hW' := hW0 W hW.1
      have hL := hL2 W hW.1
      have hlog : HasDerivAt (fun W => Real.log (W / c)) (1 / W) W := by
        have h := ((hasDerivAt_id W).div_const c).log (div_pos hW' hc).ne'
        simp only [id] at h
        convert h using 1; field_simp
      have hg := (hasDerivAt_id W).div hlog (by linarith)
      have hsq := hg.sqrt (div_pos hW' (by linarith)).ne'
      convert hsq using 1
      · ext y; simp [F]
      · simp only [F', id, Pi.div_apply]; field_simp
    have hcontF' : ContinuousOn F' (Set.uIcc m b) := by
      rw [Set.uIcc_of_le hmb]
      have hlogc : ContinuousOn (fun W => Real.log (W / c)) (Set.Icc m b) :=
        ContinuousOn.log (continuousOn_id.div_const c) fun W hW =>
          (div_pos (hW0 W hW.1) hc).ne'
      refine ContinuousOn.div (ContinuousOn.div (hlogc.sub continuousOn_const) (hlogc.pow 2)
        fun W hW => by have := hL2 W hW.1; positivity) (continuousOn_const.mul
          (Real.continuous_sqrt.comp_continuousOn (continuousOn_id.div hlogc fun W hW => by
            have := hL2 W hW.1; linarith))) fun W hW => ?_
      have := hL2 W hW.1; have := hW0 W hW.1
      have : 0 < √(W / Real.log (W / c)) := Real.sqrt_pos.2 (by positivity)
      positivity
    have hint' : IntervalIntegrable F' volume m b := hcontF'.intervalIntegrable
    calc ∫ W in m..b, f W ≤ ∫ W in m..b, 4 * F' W := by
          refine intervalIntegral.integral_mono_on hmb (hint m b ham hmb le_rfl)
            (hint'.const_mul 4) fun W hW => ?_
          have hW' := hW0 W hW.1
          have hL := hL2 W hW.1
          set L := Real.log (W / c)
          simp only [f, F']
          have hsW : 0 < √W := Real.sqrt_pos.2 hW'
          have hsL : 0 < √L := Real.sqrt_pos.2 (by linarith)
          have hsq : √(W / L) = √W / √L := Real.sqrt_div' W (by linarith)
          have hLL : √L * √L = L := Real.mul_self_sqrt (by linarith)
          rw [hsq]
          have e : 4 * ((L - 1) / L ^ 2 / (2 * (√W / √L))) = 2 * (L - 1) / (L * (√W * √L)) := by
            have key : ∀ (L s w : ℝ), 0 < s → 0 < w → s * s = L →
                4 * ((L - 1) / L ^ 2 / (2 * (w / s))) = 2 * (L - 1) / (L * (w * s)) := by
              intro L s w hs hw h; subst h; field_simp; ring
            exact key L (√L) (√W) hsL hsW hLL
          rw [e, div_le_div_iff₀ (mul_pos hsW hsL) (by positivity)]
          nlinarith [mul_pos hsW hsL]
      _ = 4 * (F b - F m) := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint']
      _ ≤ 4 * √(b / Real.log (b / c)) := by
          have : 0 ≤ F m := Real.sqrt_nonneg _
          simp only [F] at this ⊢; linarith
  linarith

end TernaryGoldbach.MinorArcs
