import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# Gaussian smoothing of an interval in `log` scale

`φ(u) = ∫_{(b − log u)/δ}^{(a − log u)/δ} g(z) dz` (`g` the standard normal density), i.e. the indicator of
`[e^b, e^a]` smoothed by a log-normal kernel of width `δ`. Its Mellin transform is the entire function
`M(s) = e^{δ²s²/2} ∫_b^a e^{sw} dw = e^{δ²s²/2}(e^{as} − e^{bs})/s`.
-/

open Complex Set Filter MeasureTheory
open scoped Real Interval Topology

namespace TernaryGoldbach.Explicit

/-- The standard normal density. -/
noncomputable def gpdf (z : ℝ) : ℝ := Real.exp (-(z ^ 2 / 2)) / √(2 * π)

theorem gpdf_pos (z : ℝ) : 0 < gpdf z := by unfold gpdf; positivity

theorem gpdf_nonneg (z : ℝ) : 0 ≤ gpdf z := (gpdf_pos z).le

theorem continuous_gpdf : Continuous gpdf := by unfold gpdf; fun_prop

theorem sqrt_two_pi_pos : 0 < √(2 * π) := Real.sqrt_pos.2 (by positivity)

theorem integral_gpdf : ∫ z, gpdf z = 1 := by
  unfold gpdf
  rw [integral_div]
  have h := integral_gaussian (1 / 2)
  have e : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) = fun x => Real.exp (-(x ^ 2 / 2)) := by
    funext x; ring_nf
  rw [e, show π / (1 / 2) = 2 * π by ring] at h
  rw [h, div_self sqrt_two_pi_pos.ne']

theorem integrable_gpdf : Integrable gpdf := by
  unfold gpdf
  have h := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  have e : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) = fun x => Real.exp (-(x ^ 2 / 2)) := by
    funext x; ring_nf
  rw [e] at h
  exact h.div_const _

/-- `E[e^{cZ}] = e^{c²/2}` for complex `c`. -/
theorem integral_gpdf_mul_cexp (c : ℂ) : ∫ z : ℝ, (gpdf z : ℂ) * cexp (c * z) = cexp (c ^ 2 / 2) := by
  have h := integral_cexp_quadratic (b := (-(1 / 2) : ℂ)) (by simp) c 0
  have e1 : ∀ z : ℝ, (gpdf z : ℂ) * cexp (c * z) =
      cexp (-(1 / 2) * (z : ℂ) ^ 2 + c * z + 0) / ((√(2 * π) : ℝ) : ℂ) := by
    intro z
    unfold gpdf
    rw [Complex.ofReal_div, Complex.ofReal_exp, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [e1]
  rw [integral_div, h]
  have e2 : ((π : ℂ) / -(-(1 / 2) : ℂ)) ^ (1 / 2 : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
    rw [show (π : ℂ) / -(-(1 / 2) : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Real.sqrt_eq_rpow,
      Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  rw [e2, mul_div_assoc, mul_div_cancel₀ _ (by exact_mod_cast sqrt_two_pi_pos.ne')]
  congr 1; ring

theorem integrable_gpdf_mul_cexp (c : ℂ) : Integrable fun z : ℝ => (gpdf z : ℂ) * cexp (c * z) := by
  have h := integrable_cexp_quadratic' (b := (-(1 / 2) : ℂ)) (by simp) c 0
  have e1 : (fun z : ℝ => (gpdf z : ℂ) * cexp (c * z)) =
      fun z : ℝ => cexp (-(1 / 2) * (z : ℂ) ^ 2 + c * z + 0) / ((√(2 * π) : ℝ) : ℂ) := by
    funext z
    unfold gpdf
    rw [Complex.ofReal_div, Complex.ofReal_exp, div_mul_eq_mul_div, ← Complex.exp_add]
    congr 2; push_cast; ring
  rw [e1]; exact h.div_const _

/-- Real version: `E[e^{tZ}] = e^{t²/2}`. -/
theorem integral_gpdf_mul_exp (t : ℝ) : ∫ z : ℝ, gpdf z * Real.exp (t * z) = Real.exp (t ^ 2 / 2) := by
  have h := integral_gpdf_mul_cexp (t : ℂ)
  have e : (fun z : ℝ => (gpdf z : ℂ) * cexp ((t : ℂ) * z)) = fun z => ((gpdf z * Real.exp (t * z) : ℝ) : ℂ) := by
    funext z; push_cast; ring_nf
  rw [e, integral_complex_ofReal, show (t : ℂ) ^ 2 / 2 = ((t ^ 2 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp] at h
  exact_mod_cast h

theorem integrable_gpdf_mul_exp (t : ℝ) : Integrable fun z : ℝ => gpdf z * Real.exp (t * z) := by
  have h := (integrable_gpdf_mul_cexp (t : ℂ)).re
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only
  rw [show (t : ℂ) * (z : ℂ) = ((t * z : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul]
  rfl

/-! ## The smoothing and its Mellin transform -/

/-- `φ(u) = ∫_{(b − log u)/δ}^{(a − log u)/δ} g`. -/
noncomputable def gsm (a b δ : ℝ) (u : ℝ) : ℝ := ∫ z in (b - Real.log u) / δ..(a - Real.log u) / δ, gpdf z

/-- The kernel `g((w − v)/δ)/δ`. -/
noncomputable def gker (δ w v : ℝ) : ℝ := gpdf ((w - v) / δ) / δ

theorem gsm_exp_eq {a b δ : ℝ} (hδ : 0 < δ) (v : ℝ) :
    gsm a b δ (Real.exp v) = ∫ w in b..a, gker δ w v := by
  unfold gsm gker
  rw [Real.log_exp, intervalIntegral.integral_div]
  have h := intervalIntegral.integral_comp_div_sub (f := gpdf) (a := b) (b := a) hδ.ne' (v / δ)
  have e : ∀ w : ℝ, (w - v) / δ = w / δ - v / δ := fun w => by ring
  simp_rw [e, h, smul_eq_mul]
  rw [mul_div_cancel_left₀ _ hδ.ne', show b / δ - v / δ = (b - v) / δ by ring,
    show a / δ - v / δ = (a - v) / δ by ring]

/-- The Mellin transform `M(s) = e^{δ²s²/2} ∫_b^a e^{sw} dw`. -/
noncomputable def Mg (a b δ : ℝ) (s : ℂ) : ℂ :=
  cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2) * ∫ w in b..a, cexp (s * w)

theorem mellin_eq_integral_exp (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ x : ℝ, cexp (s * x) * f (Real.exp x) := by
  rw [mellin, ← integral_comp_exp]
  congr 1; funext x
  have h1 : ((Real.exp x : ℝ) : ℂ) ^ (s - 1) = cexp ((s - 1) * x) := by
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    ring_nf
  rw [h1, Complex.real_smul, smul_eq_mul, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2; ring

theorem norm_gker_le {δ w x M : ℝ} (hδ : 0 < δ) (hw : w ^ 2 ≤ M ^ 2) :
    gker δ w x ≤ Real.exp (M ^ 2 / (2 * δ ^ 2)) / (√(2 * π) * δ) * Real.exp (-(x ^ 2 / (4 * δ ^ 2))) := by
  unfold gker gpdf
  rw [div_div, mul_comm (Real.exp (M ^ 2 / (2 * δ ^ 2)) / (√(2 * π) * δ)), ← mul_div_assoc,
    ← Real.exp_add]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Real.exp_le_exp.2
  have h2 : 2 * (w - x) ^ 2 ≥ x ^ 2 - 2 * w ^ 2 := by nlinarith [sq_nonneg (2 * w - x)]
  have hd : 0 < δ ^ 2 := by positivity
  have e1 : ((w - x) / δ) ^ 2 / 2 = (w - x) ^ 2 / (2 * δ ^ 2) := by field_simp
  have : x ^ 2 / (4 * δ ^ 2) - M ^ 2 / (2 * δ ^ 2) ≤ (w - x) ^ 2 / (2 * δ ^ 2) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : x ^ 2 - 2 * M ^ 2 ≤ 2 * (w - x) ^ 2 := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 4 * δ ^ 2 * δ ^ 2)
    nlinarith
  rw [e1]
  linarith

/-- The Fubini integrand. -/
noncomputable def gF (s : ℂ) (δ : ℝ) (p : ℝ × ℝ) : ℂ := cexp (s * p.1) * (gker δ p.2 p.1 : ℂ)

theorem continuous_gF (s : ℂ) (δ : ℝ) : Continuous (gF s δ) := by
  unfold gF gker gpdf; fun_prop

theorem integrable_gF {a b δ : ℝ} (hδ : 0 < δ) (s : ℂ) :
    Integrable (gF s δ) ((volume : Measure ℝ).prod (volume.restrict (Ioc b a))) := by
  set M := |a| + |b| with hM
  set C := Real.exp (M ^ 2 / (2 * δ ^ 2)) / (√(2 * π) * δ) with hC
  set q : ℂ := ((-(1 / (4 * δ ^ 2)) : ℝ) : ℂ) with hqdef
  have hq0 : q.re < 0 := by
    rw [hqdef, Complex.ofReal_re]; have : 0 < 1 / (4 * δ ^ 2) := by positivity
    linarith
  have hq : Integrable fun x : ℝ => cexp (q * (x : ℂ) ^ 2 + s * x + 0) :=
    integrable_cexp_quadratic' hq0 s 0
  have hG : Integrable (fun p : ℝ × ℝ => (C * ‖cexp (q * (p.1 : ℂ) ^ 2 + s * p.1 + 0)‖) * 1)
      ((volume : Measure ℝ).prod (volume.restrict (Ioc b a))) := by
    have h1 : Integrable (fun x : ℝ => C * ‖cexp (q * (x : ℂ) ^ 2 + s * x + 0)‖) :=
      hq.norm.const_mul C
    have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc b a)) := by
      refine integrable_const _
    exact h1.mul_prod h2
  refine hG.mono' (continuous_gF s δ).aestronglyMeasurable ?_
  have hm : (volume : Measure ℝ).prod (volume.restrict (Ioc b a)) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioc b a) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm]
  have : ∀ᵐ p ∂(((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioc b a)), p ∈ univ ×ˢ Ioc b a :=
    ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)
  refine this.mono fun p hp => ?_
  obtain ⟨-, hp2⟩ := hp
  rw [gF, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (by unfold gker; exact div_nonneg (gpdf_nonneg _) hδ.le), mul_one]
  have hw : p.2 ^ 2 ≤ M ^ 2 := by
    rw [hM]
    have := hp2.1; have := hp2.2
    have h1 : |p.2| ≤ |a| + |b| := by
      rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
    nlinarith [abs_nonneg p.2, sq_abs p.2]
  have hk := norm_gker_le (x := p.1) hδ hw
  have e : ‖cexp (q * (p.1 : ℂ) ^ 2 + s * p.1 + 0)‖ =
      Real.exp (-(p.1 ^ 2 / (4 * δ ^ 2))) * ‖cexp (s * p.1)‖ := by
    rw [add_zero, Complex.exp_add, norm_mul, Complex.norm_exp]
    congr 2
    rw [hqdef, show (((-(1 / (4 * δ ^ 2)) : ℝ) : ℂ) * (p.1 : ℂ) ^ 2) = ((-(p.1 ^ 2 / (4 * δ ^ 2)) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  rw [e]
  rw [← hC] at hk
  calc ‖cexp (s * p.1)‖ * gker δ p.2 p.1 ≤ ‖cexp (s * p.1)‖ * (C * Real.exp (-(p.1 ^ 2 / (4 * δ ^ 2)))) :=
        mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ = _ := by ring

/-- The inner integral: `∫ e^{sv} g((w−v)/δ)/δ dv = e^{sw} e^{δ²s²/2}`. -/
theorem integral_gF_left {δ : ℝ} (hδ : 0 < δ) (s : ℂ) (w : ℝ) :
    ∫ x : ℝ, gF s δ (x, w) = cexp (s * w) * cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2) := by
  have h1 : ∫ x : ℝ, gF s δ (x, w) = ∫ x : ℝ, gF s δ (w - x, w) :=
    (integral_sub_left_eq_self (fun x => gF s δ (x, w)) volume w).symm
  have h2 : ∫ x : ℝ, gF s δ (w - x, w) = δ • ∫ z : ℝ, gF s δ (w - δ * z, w) := by
    have := Measure.integral_comp_mul_left (fun x => gF s δ (w - x, w)) δ
    rw [this, abs_of_pos (inv_pos.2 hδ), smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  rw [h1, h2]
  have e : ∀ z : ℝ, gF s δ (w - δ * z, w) = (1 / δ : ℂ) * cexp (s * w) * ((gpdf z : ℂ) * cexp ((-(s * δ)) * z)) := by
    intro z
    unfold gF gker
    simp only
    rw [show (w - (w - δ * z)) / δ = z by field_simp; ring]
    push_cast
    rw [show s * ((w : ℂ) - δ * z) = s * w + (-(s * δ)) * z by ring, Complex.exp_add]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_gpdf_mul_cexp, Complex.real_smul]
  have : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  field_simp

/-- **The Mellin transform of the smoothing.** -/
theorem mellin_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (s : ℂ) :
    mellin (fun u => (gsm a b δ u : ℂ)) s = Mg a b δ s := by
  rw [mellin_eq_integral_exp]
  have h1 : ∀ x : ℝ, cexp (s * x) * ((gsm a b δ (Real.exp x) : ℝ) : ℂ) =
      ∫ w in Ioc b a, gF s δ (x, w) := by
    intro x
    rw [gsm_exp_eq hδ, intervalIntegral.integral_of_le hab, ← integral_complex_ofReal, ← integral_const_mul]
    rfl
  simp_rw [h1]
  have hI : Integrable (Function.uncurry fun (x : ℝ) (w : ℝ) => gF s δ (x, w))
      ((volume : Measure ℝ).prod (volume.restrict (Ioc b a))) := integrable_gF hδ s
  rw [integral_integral_swap hI]
  simp_rw [integral_gF_left hδ s]
  rw [integral_mul_const, Mg, ← intervalIntegral.integral_of_le hab, mul_comm]

/-! ## `M` is entire; the admissibility conditions -/

theorem differentiable_intExp (a b : ℝ) : Differentiable ℂ fun s : ℂ => ∫ w in b..a, cexp (s * w) := by
  intro x₀
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := b) (b := a)
    (F := fun (s : ℂ) (w : ℝ) => cexp (s * w)) (F' := fun (s : ℂ) (w : ℝ) => (w : ℂ) * cexp (s * w))
    (x₀ := x₀) (s := Metric.ball x₀ 1)
    (bound := fun w : ℝ => |w| * Real.exp ((‖x₀‖ + 1) * |w|)) (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun s => (by fun_prop : Continuous fun w : ℝ => cexp (s * w)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun w : ℝ => cexp (x₀ * w)).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun w : ℝ => (w : ℂ) * cexp (x₀ * w)).aestronglyMeasurable)
    (Eventually.of_forall fun w _ s hs => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg w)
      apply Real.exp_le_exp.2
      have h1 : (s * (w : ℂ)).re = s.re * w := by simp
      rw [h1]
      have h2 : |s.re| ≤ ‖x₀‖ + 1 := by
        refine (Complex.abs_re_le_norm s).trans ?_
        have := norm_le_norm_add_norm_sub' s x₀
        rw [Metric.mem_ball, dist_eq_norm] at hs
        linarith
      calc s.re * w ≤ |s.re * w| := le_abs_self _
        _ = |s.re| * |w| := abs_mul _ _
        _ ≤ (‖x₀‖ + 1) * |w| := mul_le_mul_of_nonneg_right h2 (abs_nonneg w))
    ((by fun_prop : Continuous fun w : ℝ => |w| * Real.exp ((‖x₀‖ + 1) * |w|)).intervalIntegrable _ _)
    (Eventually.of_forall fun w _ s _ => by
      have := ((hasDerivAt_id s).mul_const (w : ℂ)).cexp
      simp only [id, one_mul] at this
      convert this using 1; ring)
  exact h.2.differentiableAt

theorem differentiable_Mg (a b δ : ℝ) : Differentiable ℂ (Mg a b δ) := by
  unfold Mg
  exact (by fun_prop : Differentiable ℂ fun s : ℂ => cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)).mul (differentiable_intExp a b)

theorem continuous_gsm {a b δ : ℝ} {u : ℝ} (hu : 0 < u) : ContinuousAt (gsm a b δ) u := by
  have hint : ∀ p q : ℝ, IntervalIntegrable gpdf volume p q := fun p q => continuous_gpdf.intervalIntegrable _ _
  have e : gsm a b δ = fun u => (∫ z in (0:ℝ)..(a - Real.log u) / δ, gpdf z) - ∫ z in (0:ℝ)..(b - Real.log u) / δ, gpdf z := by
    funext u; unfold gsm
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
  rw [e]
  have hP := intervalIntegral.continuous_primitive hint 0
  have hl : ContinuousAt Real.log u := Real.continuousAt_log hu.ne'
  exact ((hP.continuousAt).comp ((continuousAt_const.sub hl).div_const δ)).sub
    ((hP.continuousAt).comp ((continuousAt_const.sub hl).div_const δ))

theorem integrable_mellin_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (s : ℂ) :
    Integrable fun x : ℝ => cexp (s * x) * ((gsm a b δ (Real.exp x) : ℝ) : ℂ) := by
  have hI := (integrable_gF (a := a) (b := b) hδ s).integral_prod_left
  refine hI.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [gsm_exp_eq hδ, intervalIntegral.integral_of_le hab, ← integral_complex_ofReal, ← integral_const_mul]
  rfl

theorem mellinConvergent_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) (s : ℂ) :
    MellinConvergent (fun u => (gsm a b δ u : ℂ)) s := by
  unfold MellinConvergent
  rw [← integrable_comp_exp]
  refine (integrable_mellin_gsm hδ hab s).congr (Eventually.of_forall fun x => ?_)
  have h1 : ((Real.exp x : ℝ) : ℂ) ^ (s - 1) = cexp ((s - 1) * x) := by
    rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    ring_nf
  simp only
  rw [h1, Complex.real_smul, smul_eq_mul, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2; ring

/-- `‖∫_b^a e^{sw} dw‖ ≤ (a − b) e^{(|a| + |b|)|ℜs|}`. -/
theorem norm_intExp_le {a b : ℝ} (hab : b ≤ a) (s : ℂ) :
    ‖∫ w in b..a, cexp (s * w)‖ ≤ (a - b) * Real.exp ((|a| + |b|) * |s.re|) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := b) (b := a)
    (C := Real.exp ((|a| + |b|) * |s.re|)) (f := fun w : ℝ => cexp (s * w)) (fun w hw => by
      rw [Set.uIoc_of_le hab] at hw
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.2
      have h1 : (s * (w : ℂ)).re = s.re * w := by simp
      rw [h1]
      have hw' : |w| ≤ |a| + |b| := by
        rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [hw.1, hw.2]
      calc s.re * w ≤ |s.re| * |w| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |s.re| * (|a| + |b|) := mul_le_mul_of_nonneg_left hw' (abs_nonneg _)
        _ = _ := by ring)
  rwa [abs_of_nonneg (show (0:ℝ) ≤ a - b by linarith), mul_comm] at this

/-- `‖e^{δ²s²/2}‖ = e^{δ²(σ² − t²)/2}`. -/
theorem norm_cexp_gauss (δ : ℝ) (s : ℂ) :
    ‖cexp ((δ : ℂ) ^ 2 * s ^ 2 / 2)‖ = Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) := by
  rw [Complex.norm_exp]; congr 1
  have : ((δ : ℂ) ^ 2 * s ^ 2 / 2) = ((δ ^ 2 / 2 : ℝ) : ℂ) * s ^ 2 := by push_cast; ring
  rw [this, Complex.re_ofReal_mul, sq s, Complex.mul_re]; ring

/-- **Admissibility**. -/
theorem goodSmoothing_gsm {a b δ : ℝ} (hδ : 0 < δ) (hab : b ≤ a) :
    GoodSmoothing (fun u => (gsm a b δ u : ℂ))
      ((a - b) * Real.exp ((|a| + |b|) * (3 / 2)) * Real.exp (9 * δ ^ 2 / 8) * Real.exp (1 / 2)) δ where
  continuousAt := fun y hy => Complex.continuous_ofReal.continuousAt.comp (continuous_gsm hy)
  conv := mellinConvergent_gsm hδ hab _
  diff := fun s _ => by
    have : mellin (fun u => (gsm a b δ u : ℂ)) = Mg a b δ := funext (mellin_gsm hδ hab)
    rw [this]; exact differentiable_Mg a b δ s
  c_pos := hδ
  strip := fun s h1 h2 => by
    rw [mellin_gsm hδ hab, Mg, norm_mul, norm_cexp_gauss]
    have hσ : |s.re| ≤ 3 / 2 := abs_le.2 ⟨by linarith, h2⟩
    have hI := norm_intExp_le hab s
    have hI' : ‖∫ w in b..a, cexp (s * w)‖ ≤ (a - b) * Real.exp ((|a| + |b|) * (3 / 2)) :=
      hI.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hσ
        (by positivity))) (by linarith))
    have hg : Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) ≤
        Real.exp (9 * δ ^ 2 / 8) * Real.exp (1 / 2) * Real.exp (-(δ * |s.im|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hs2 : s.re ^ 2 ≤ 9 / 4 := by nlinarith [abs_nonneg s.re, sq_abs s.re]
      have hsq : s.im ^ 2 = |s.im| ^ 2 := (sq_abs _).symm
      have : 0 ≤ (δ * |s.im| - 1) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg δ]
    calc Real.exp (δ ^ 2 * (s.re ^ 2 - s.im ^ 2) / 2) * ‖∫ w in b..a, cexp (s * w)‖
        ≤ (Real.exp (9 * δ ^ 2 / 8) * Real.exp (1 / 2) * Real.exp (-(δ * |s.im|))) *
            ((a - b) * Real.exp ((|a| + |b|) * (3 / 2))) :=
          mul_le_mul hg hI' (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- `∫_b^a e^{sw} dw = (e^{as} − e^{bs})/s`, so `‖·‖ ≤ (e^{aσ} + e^{bσ})/‖s‖`. -/
theorem norm_intExp_le' {a b : ℝ} {s : ℂ} (hs : s ≠ 0) :
    ‖∫ w in b..a, cexp (s * w)‖ ≤ (Real.exp (a * s.re) + Real.exp (b * s.re)) / ‖s‖ := by
  rw [integral_exp_mul_complex hs, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_exp, Complex.norm_exp]
  congr 2 <;> simp [mul_comm]

theorem Mg_one {a b δ : ℝ} : Mg a b δ 1 = ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) := by
  rw [Mg, integral_exp_mul_complex one_ne_zero]
  push_cast
  simp

end TernaryGoldbach.Explicit
