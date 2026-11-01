import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.DSlope

/-!
# Residues on rectangles

`rectInt f z w` is the boundary integral of `f` around the rectangle with corners `z`, `w`
(Mathlib's convention in `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`).
* `rectInt_inv_sub`: `∮ ds/(s − ρ) = 2πi` for `ρ` strictly inside (antiderivatives `log(s − ρ)` on
  three sides and `log(ρ − s)` on the left side, and `arg p − arg(−p) = ±π`);
* `rectInt_div_sub`: Cauchy's formula `∮ g(s)/(s − ρ) ds = 2πi g(ρ)`.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Real Interval

namespace TernaryGoldbach.Explicit

/-- The boundary integral around the rectangle `[z.re, w.re] × [z.im, w.im]`. -/
noncomputable def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- `∫_a^b dx/(x + κ) = log(b + κ) − log(a + κ)` if the segment avoids the slit. -/
theorem integral_inv_add_real {a b : ℝ} {κ : ℂ} (h : ∀ x ∈ [[a, b]], (x : ℂ) + κ ∈ slitPlane) :
    ∫ x : ℝ in a..b, ((x : ℂ) + κ)⁻¹ = Complex.log (b + κ) - Complex.log (a + κ) := by
  have hd : ∀ x ∈ [[a, b]], HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + κ)) ((x : ℂ) + κ)⁻¹ x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + κ) 1 x := (hasDerivAt_id x).ofReal_comp.add_const κ
    have := h1.clog_real (h x hx)
    simpa using this
  have hc : ContinuousOn (fun x : ℝ => ((x : ℂ) + κ)⁻¹) [[a, b]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    exact slitPlane_ne_zero (h x hx)
  exact integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable)

/-- `∫_c^d dy/(σ + iy + κ) = −i (log(σ + id + κ) − log(σ + ic + κ))` if the segment avoids the slit. -/
theorem integral_inv_add_imag {c d σ : ℝ} {κ : ℂ}
    (h : ∀ y ∈ [[c, d]], (σ : ℂ) + y * I + κ ∈ slitPlane) :
    ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
      -I * (Complex.log (σ + d * I + κ) - Complex.log (σ + c * I + κ)) := by
  have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log ((σ : ℂ) + y * I + κ))
      ((σ : ℂ) + y * I + κ)⁻¹ y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => (σ : ℂ) + y * I + κ) I y := by
      have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ) |>.add_const κ
      simpa using this
    have := (h1.clog_real (h y hy)).const_mul (-I)
    refine this.congr_deriv ?_
    have hne := slitPlane_ne_zero (h y hy)
    field_simp
    rw [I_sq]; ring
  have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    exact slitPlane_ne_zero (h y hy)
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- Same with `log(−·)`: for segments in the left half-plane. -/
theorem integral_inv_add_imag_neg {c d σ : ℝ} {κ : ℂ}
    (h : ∀ y ∈ [[c, d]], -((σ : ℂ) + y * I + κ) ∈ slitPlane) :
    ∫ y : ℝ in c..d, ((σ : ℂ) + y * I + κ)⁻¹ =
      -I * (Complex.log (-((σ : ℂ) + d * I + κ)) - Complex.log (-((σ : ℂ) + c * I + κ))) := by
  have hd : ∀ y ∈ [[c, d]], HasDerivAt (fun y : ℝ => -I * Complex.log (-((σ : ℂ) + y * I + κ)))
      ((σ : ℂ) + y * I + κ)⁻¹ y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => -((σ : ℂ) + y * I + κ)) (-I) y :=
      ((((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (σ : ℂ)).add_const κ).neg.congr_deriv
        (by simp)
    have := (h1.clog_real (h y hy)).const_mul (-I)
    refine this.congr_deriv ?_
    have hne : (σ : ℂ) + y * I + κ ≠ 0 := by
      intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
    field_simp
    rw [I_sq]; ring
  have hc : ContinuousOn (fun y : ℝ => ((σ : ℂ) + y * I + κ)⁻¹) [[c, d]] := by
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    intro h0; have := slitPlane_ne_zero (h y hy); rw [h0, neg_zero] at this; exact this rfl
  rw [integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

theorem log_sub_log_neg_of_im_pos {p : ℂ} (hp : 0 < p.im) :
    Complex.log p - Complex.log (-p) = π * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hp]
  push_cast; ring

theorem log_sub_log_neg_of_im_neg {p : ℂ} (hp : p.im < 0) :
    Complex.log p - Complex.log (-p) = -(π * I) := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hp]
  push_cast; ring

/-- **`∮ ds/(s − ρ) = 2πi`** for `ρ` strictly inside the rectangle. -/
theorem rectInt_inv_sub {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
    (h4 : ρ.im < w.im) : rectInt (fun s => (s - ρ)⁻¹) z w = 2 * π * I := by
  unfold rectInt
  -- bottom and top
  have hB : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - ρ)⁻¹ =
      Complex.log (w.re + (z.im * I - ρ)) - Complex.log (z.re + (z.im * I - ρ)) := by
    have := integral_inv_add_real (a := z.re) (b := w.re) (κ := z.im * I - ρ) (fun x _ => by
      refine Or.inr ?_
      simp; linarith)
    simpa [add_sub_assoc] using this
  have hT : ∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - ρ)⁻¹ =
      Complex.log (w.re + (w.im * I - ρ)) - Complex.log (z.re + (w.im * I - ρ)) := by
    have := integral_inv_add_real (a := z.re) (b := w.re) (κ := w.im * I - ρ) (fun x _ => by
      refine Or.inr ?_
      simp; linarith)
    simpa [add_sub_assoc] using this
  have hR : ∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + y * I - ρ)⁻¹ =
      -I * (Complex.log (w.re + w.im * I + -ρ) - Complex.log (w.re + z.im * I + -ρ)) := by
    have := integral_inv_add_imag (c := z.im) (d := w.im) (σ := w.re) (κ := -ρ) (fun y _ => by
      refine Or.inl ?_
      simp; linarith)
    simpa [sub_eq_add_neg] using this
  have hL : ∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + y * I - ρ)⁻¹ =
      -I * (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) := by
    have := integral_inv_add_imag_neg (c := z.im) (d := w.im) (σ := z.re) (κ := -ρ) (fun y _ => by
      refine Or.inl ?_
      simp; linarith)
    simpa [sub_eq_add_neg] using this
  simp only [smul_eq_mul]
  rw [hB, hT, hR, hL]
  have eTL : Complex.log ((z.re : ℂ) + (w.im * I - ρ)) - Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) =
      π * I := by
    have hp : 0 < ((z.re : ℂ) + (w.im * I - ρ)).im := by simp; linarith
    rw [← log_sub_log_neg_of_im_pos hp]; congr 2; ring
  have eBL : Complex.log ((z.re : ℂ) + (z.im * I - ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ)) =
      -(π * I) := by
    have hp : ((z.re : ℂ) + (z.im * I - ρ)).im < 0 := by simp; linarith
    rw [← log_sub_log_neg_of_im_neg hp]; congr 2; ring
  have e1 : Complex.log ((w.re : ℂ) + w.im * I + -ρ) = Complex.log ((w.re : ℂ) + (w.im * I - ρ)) := by
    congr 1; ring
  have e2 : Complex.log ((w.re : ℂ) + z.im * I + -ρ) = Complex.log ((w.re : ℂ) + (z.im * I - ρ)) := by
    congr 1; ring
  rw [e1, e2]
  have hII : I * -I = 1 := by rw [mul_neg, I_mul_I, neg_neg]
  linear_combination eTL - eBL + (Complex.log ((w.re : ℂ) + (w.im * I - ρ)) -
    Complex.log ((w.re : ℂ) + (z.im * I - ρ))) * hII -
    (Complex.log (-((z.re : ℂ) + w.im * I + -ρ)) - Complex.log (-((z.re : ℂ) + z.im * I + -ρ))) * hII

/-! ## Cauchy's formula on rectangles -/

theorem mem_rect_boundary_ne {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im)
    (h4 : ρ.im < w.im) :
    (∀ x : ℝ, (x : ℂ) + z.im * I ≠ ρ) ∧ (∀ x : ℝ, (x : ℂ) + w.im * I ≠ ρ) ∧
      (∀ y : ℝ, (w.re : ℂ) + y * I ≠ ρ) ∧ (∀ y : ℝ, (z.re : ℂ) + y * I ≠ ρ) := by
  refine ⟨fun x h => ?_, fun x h => ?_, fun y h => ?_, fun y h => ?_⟩
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

/-- `rectInt` is additive (for functions continuous on the boundary). -/
theorem rectInt_add {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hg : ContinuousOn g ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  have hseg1 : ∀ c ∈ [[z.im, w.im]], ∀ φ : ℂ → ℂ,
      ContinuousOn φ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) →
      IntervalIntegrable (fun x : ℝ => φ (x + c * I)) volume z.re w.re := by
    intro c hc φ hφ
    refine ContinuousOn.intervalIntegrable ?_
    refine hφ.comp (by fun_prop) fun x hx => ?_
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨hx, hc⟩
  have hseg2 : ∀ c ∈ [[z.re, w.re]], ∀ φ : ℂ → ℂ,
      ContinuousOn φ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) →
      IntervalIntegrable (fun y : ℝ => φ (c + y * I)) volume z.im w.im := by
    intro c hc φ hφ
    refine ContinuousOn.intervalIntegrable ?_
    refine hφ.comp (by fun_prop) fun y hy => ?_
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
    exact ⟨hc, hy⟩
  have lz : z.im ∈ [[z.im, w.im]] := left_mem_uIcc
  have lw : w.im ∈ [[z.im, w.im]] := right_mem_uIcc
  have rz : z.re ∈ [[z.re, w.re]] := left_mem_uIcc
  have rw' : w.re ∈ [[z.re, w.re]] := right_mem_uIcc
  unfold rectInt
  rw [integral_add (hseg1 _ lz f hf) (hseg1 _ lz g hg), integral_add (hseg1 _ lw f hf) (hseg1 _ lw g hg),
    integral_add (hseg2 _ rw' f hf) (hseg2 _ rw' g hg), integral_add (hseg2 _ rz f hf) (hseg2 _ rz g hg)]
  simp only [smul_eq_mul]
  ring

theorem rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

/-- `rectInt` is additive when all eight boundary integrals exist. -/
theorem rectInt_add_of_integrable {f g : ℂ → ℂ} {z w : ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) volume z.im w.im) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  unfold rectInt
  rw [integral_add hf1 hg1, integral_add hf2 hg2, integral_add hf3 hg3, integral_add hf4 hg4]
  simp only [smul_eq_mul]
  ring

theorem rectInt_congr {f g : ℂ → ℂ} {z w : ℂ}
    (h1 : ∀ x : ℝ, f (x + z.im * I) = g (x + z.im * I)) (h2 : ∀ x : ℝ, f (x + w.im * I) = g (x + w.im * I))
    (h3 : ∀ y : ℝ, f (w.re + y * I) = g (w.re + y * I)) (h4 : ∀ y : ℝ, f (z.re + y * I) = g (z.re + y * I)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  simp only [h1, h2, h3, h4]

/-- Continuous functions are integrable along the four sides. -/
theorem rect_sides_integrable {f : ℂ → ℂ} {z w : ℂ}
    (hf : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
    refine hf.comp (by fun_prop) fun t ht => ?_ <;>
    simp only [mem_reProdIm, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add]
  · exact ⟨ht, left_mem_uIcc⟩
  · exact ⟨ht, right_mem_uIcc⟩
  · exact ⟨right_mem_uIcc, ht⟩
  · exact ⟨left_mem_uIcc, ht⟩

/-- `(s − ρ)⁻¹` is integrable along the sides when `ρ` is strictly inside. -/
theorem rect_sides_integrable_inv {z w ρ : ℂ} (h1 : z.re < ρ.re) (h2 : ρ.re < w.re)
    (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    IntervalIntegrable (fun x : ℝ => ((x + z.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => ((x + w.im * I : ℂ) - ρ)⁻¹) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => ((w.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => ((z.re + y * I : ℂ) - ρ)⁻¹) volume z.im w.im := by
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine ContinuousOn.intervalIntegrable ?_ <;>
    refine ContinuousOn.inv₀ (by fun_prop) fun t _ => sub_ne_zero.2 ?_
  exacts [b1 t, b2 t, b3 t, b4 t]

/-- **Cauchy's formula on a rectangle**: `∮ g(s)/(s − ρ) ds = 2πi g(ρ)` for `ρ` strictly inside and
`g` holomorphic on an open set containing the closed rectangle. -/
theorem rectInt_mul_inv_sub {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {z w ρ : ℂ}
    (hsub : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U) (hg : DifferentiableOn ℂ g U)
    (h1 : z.re < ρ.re) (h2 : ρ.re < w.re) (h3 : z.im < ρ.im) (h4 : ρ.im < w.im) :
    rectInt (fun s => g s * (s - ρ)⁻¹) z w = 2 * π * I * g ρ := by
  set R := [[z.re, w.re]] ×ℂ [[z.im, w.im]] with hR
  have hρU : ρ ∈ U := hsub (mem_reProdIm.2 ⟨Set.mem_uIcc.2 (Or.inl ⟨h1.le, h2.le⟩),
    Set.mem_uIcc.2 (Or.inl ⟨h3.le, h4.le⟩)⟩)
  have hgρ : DifferentiableAt ℂ g ρ := hg.differentiableAt (hU.mem_nhds hρU)
  have hdc : ContinuousOn (dslope g ρ) R := by
    intro s hs
    by_cases hsρ : s = ρ
    · subst hsρ; exact (continuousAt_dslope_same.2 hgρ).continuousWithinAt
    · have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hs))
      exact ((differentiableAt_dslope_of_ne hsρ).2 hgs).continuousAt.continuousWithinAt
  have hdd : ∀ s ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ {ρ},
      DifferentiableAt ℂ (dslope g ρ) s := by
    intro s hs
    have hsR : s ∈ R := ⟨Ioo_subset_Icc_self hs.1.1, Ioo_subset_Icc_self hs.1.2⟩
    have hgs : DifferentiableAt ℂ g s := hg.differentiableAt (hU.mem_nhds (hsub hsR))
    exact (differentiableAt_dslope_of_ne hs.2).2 hgs
  have h0 : rectInt (dslope g ρ) z w = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (dslope g ρ)
      z w {ρ} (countable_singleton ρ) hdc hdd
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne h1 h2 h3 h4
  have hpt : ∀ s, s ≠ ρ → g s * (s - ρ)⁻¹ = dslope g ρ s + g ρ * (s - ρ)⁻¹ := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field]
    have : s - ρ ≠ 0 := sub_ne_zero.2 hs
    field_simp
    ring
  rw [rectInt_congr (g := fun s => dslope g ρ s + g ρ * (s - ρ)⁻¹)
    (fun x => hpt _ (b1 x)) (fun x => hpt _ (b2 x)) (fun y => hpt _ (b3 y)) (fun y => hpt _ (b4 y))]
  obtain ⟨d1, d2, d3, d4⟩ := rect_sides_integrable hdc
  obtain ⟨i1, i2, i3, i4⟩ := rect_sides_integrable_inv h1 h2 h3 h4
  rw [rectInt_add_of_integrable d1 d2 d3 d4 (i1.const_mul _) (i2.const_mul _) (i3.const_mul _)
    (i4.const_mul _), h0, zero_add, rectInt_const_mul, rectInt_inv_sub h1 h2 h3 h4]
  ring

end TernaryGoldbach.Explicit
