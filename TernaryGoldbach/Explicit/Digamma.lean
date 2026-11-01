import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bounds for the digamma function

* Frullani: `∫₀^∞ (e^{−au} − e^{−bu})/u du = log(b/a)`.
* Dirichlet's formula: `ψ(s) = ∫₀^∞ (e^{−u} − (1+u)^{−s}) du/u` for `ℜs > 1/2`.
* `Re ψ(σ+it) − ψ(σ) ≤ ½ log(1 + t²/(σ − ½)²)`, `|Im ψ(σ + it)| ≤ …`, `ψ(σ) ≤ log σ`.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.Explicit

/-- `∫_a^b e^{−vu} dv = (e^{−au} − e^{−bu})/u` for `u ≠ 0`. -/
theorem intervalIntegral_exp_neg_mul {u : ℝ} (hu : u ≠ 0) (a b : ℝ) :
    ∫ v in a..b, Real.exp (-(v * u)) = (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u := by
  have hF : ∀ v ∈ [[a, b]], HasDerivAt (fun v => -Real.exp (-(v * u)) / u) (Real.exp (-(v * u))) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => -(v * u)) (-u) v := by
      have := ((hasDerivAt_id v).mul_const u).neg
      simp only [id, one_mul] at this
      exact this
    have h := (h1.exp.neg).div_const u
    convert h using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (-(v * u))).intervalIntegrable _ _)]
  ring

theorem integral_exp_neg_mul_Ioi' {v : ℝ} (hv : 0 < v) :
    ∫ u in Ioi (0:ℝ), Real.exp (-(v * u)) = 1 / v := by
  have h := integral_exp_mul_Ioi (a := -v) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at h
  rw [h]; field_simp

theorem frullani_pt {a b : ℝ} (hab : a ≤ b) : ∀ u ∈ Ioi (0:ℝ),
    (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u = ∫ v in Ioc a b, Real.exp (-(v * u)) := by
  intro u (hu : 0 < u)
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral_exp_neg_mul hu.ne']

theorem frullani_prod {a b : ℝ} (ha : 0 < a) :
    Integrable (Function.uncurry fun (u v : ℝ) => Real.exp (-(v * u)))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc a b))) := by
  have hi : Integrable (fun u : ℝ => Real.exp (-(a * u))) (volume.restrict (Ioi 0)) := by
    have := integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0
    refine this.congr_fun (fun u _ => by ring_nf) measurableSet_Ioi
  have hb' : Integrable (fun p : ℝ × ℝ => Real.exp (-(a * p.1)) * (1 : ℝ))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc a b))) :=
    Integrable.mul_prod hi (integrable_const (1:ℝ))
  refine hb'.mono' (by fun_prop) ?_
  rw [Measure.prod_restrict]
  refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioc)).2
    (Eventually.of_forall fun p hp => ?_)
  have h1 : 0 < p.1 := hp.1
  have h2 : a < p.2 := hp.2.1
  simp only [Function.uncurry, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_one]
  exact Real.exp_le_exp.2 (by nlinarith)

theorem integrableOn_frullani {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (fun u => (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => ∫ v in Ioc a b, Real.exp (-(v * u))) (Ioi 0) :=
    (frullani_prod (b := b) ha).integral_prod_left
  exact h.congr_fun (fun u hu => (frullani_pt hab u hu).symm) measurableSet_Ioi

/-- **Frullani**: `∫₀^∞ (e^{−au} − e^{−bu})/u du = log(b/a)` for `0 < a ≤ b`. -/
theorem frullani_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ u in Ioi (0:ℝ), (Real.exp (-(a * u)) - Real.exp (-(b * u))) / u = Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hpt := frullani_pt hab
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  rw [integral_integral_swap (frullani_prod ha)]
  rw [setIntegral_congr_fun measurableSet_Ioc fun v (hv : v ∈ Ioc a b) =>
    integral_exp_neg_mul_Ioi' (lt_trans ha hv.1)]
  rw [← intervalIntegral.integral_of_le hab]
  have : ∫ v in a..b, 1 / v = ∫ v in a..b, v⁻¹ := by simp only [one_div]
  rw [this, integral_inv_of_pos ha hb]

/-- **Frullani for `log`**: `∫₀^∞ (e^{−u} − e^{−tu})/u du = log t` for `t > 0`. -/
theorem frullani_log {t : ℝ} (ht : 0 < t) :
    ∫ u in Ioi (0:ℝ), (Real.exp (-u) - Real.exp (-(t * u))) / u = Real.log t := by
  rcases le_total 1 t with h | h
  · have := frullani_of_le one_pos h
    simp only [one_mul, div_one] at this
    exact this
  · have := frullani_of_le ht h
    rw [Real.log_div one_ne_zero ht.ne', Real.log_one, zero_sub] at this
    have e : ∀ u, (Real.exp (-u) - Real.exp (-(t * u))) / u =
        -((Real.exp (-(t * u)) - Real.exp (-(1 * u))) / u) := by intro u; ring_nf
    simp_rw [e, integral_neg, this, neg_neg]

theorem integrableOn_frullani_log {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => (Real.exp (-u) - Real.exp (-(t * u))) / u) (Ioi 0) := by
  rcases le_total 1 t with h | h
  · have := integrableOn_frullani one_pos h
    simpa only [one_mul] using this
  · have := (integrableOn_frullani ht h).neg
    refine this.congr_fun (fun u _ => by simp only [Pi.neg_apply, one_mul]; ring) measurableSet_Ioi

/-- `∫₀^∞ |e^{−u} − e^{−tu}|/u du = |log t|`. -/
theorem integral_abs_frullani {t : ℝ} (ht : 0 < t) :
    ∫ u in Ioi (0:ℝ), |Real.exp (-u) - Real.exp (-(t * u))| / u = |Real.log t| := by
  rcases le_total 1 t with h | h
  · have hpt : ∀ u ∈ Ioi (0:ℝ), |Real.exp (-u) - Real.exp (-(t * u))| / u =
        (Real.exp (-u) - Real.exp (-(t * u))) / u := by
      intro u (hu : 0 < u)
      rw [abs_of_nonneg]
      rw [sub_nonneg]; exact Real.exp_le_exp.2 (by nlinarith)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, frullani_log ht,
      abs_of_nonneg (Real.log_nonneg h)]
  · have hpt : ∀ u ∈ Ioi (0:ℝ), |Real.exp (-u) - Real.exp (-(t * u))| / u =
        -((Real.exp (-u) - Real.exp (-(t * u))) / u) := by
      intro u (hu : 0 < u)
      rw [abs_of_nonpos, neg_div]
      rw [sub_nonpos]; exact Real.exp_le_exp.2 (by nlinarith)
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_neg, frullani_log ht,
      abs_of_nonpos (Real.log_nonpos ht.le h)]

/-- `|log t| ≤ t + 2/√t`. -/
theorem abs_log_le_add {t : ℝ} (ht : 0 < t) : |Real.log t| ≤ t + 2 * t ^ (-(1 / 2 : ℝ)) := by
  have hs : 0 < t ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos ht _
  rcases le_total 1 t with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos ht
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos ht.le h)]
    have h1 := Real.log_le_sub_one_of_pos hs
    rw [Real.log_rpow ht] at h1
    linarith

/-! ## Dirichlet's formula -/

/-- The integrand of the double integral. -/
noncomputable def digF (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (s - 1) * ((Real.exp (-p.1) * ((Real.exp (-p.2) - Real.exp (-(p.1 * p.2))) / p.2) : ℝ) : ℂ)

theorem norm_digF {s : ℂ} {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) :
    ‖digF s p‖ = p.1 ^ (s.re - 1) * (Real.exp (-p.1) * (|Real.exp (-p.2) - Real.exp (-(p.1 * p.2))| / p.2)) := by
  rw [digF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h1, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_div, abs_of_pos h2]
  simp only [Complex.sub_re, Complex.one_re]

theorem continuousOn_digF (s : ℂ) : ContinuousOn (digF s) (Ioi 0 ×ˢ Ioi 0) := by
  intro p hp
  have h1 : (0:ℝ) < p.1 := hp.1
  have h2 : (0:ℝ) < p.2 := hp.2
  unfold digF
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.mul ?_ ?_
  · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (Complex.ofReal_mem_slitPlane.2 h1)
  · refine Complex.continuous_ofReal.continuousAt.comp ?_
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.div (by fun_prop) (by fun_prop) h2.ne')

theorem integrable_digF {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (digF s) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hmeas : AEStronglyMeasurable (digF s)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (continuousOn_digF s).aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    have h := ((integrableOn_frullani_log ht).norm).const_mul (‖(t : ℂ) ^ (s - 1)‖ * Real.exp (-t))
    refine h.mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u (hu : 0 < u) => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt ?_
      have hc : ContinuousAt (fun u : ℝ => Real.exp (-t) * ((Real.exp (-u) - Real.exp (-(t * u))) / u))
          u := ContinuousAt.mul continuousAt_const (ContinuousAt.div (by fun_prop) (by fun_prop) hu.ne')
      show ContinuousAt (fun u : ℝ => (t : ℂ) ^ (s - 1) *
        ((Real.exp (-t) * ((Real.exp (-u) - Real.exp (-(t * u))) / u) : ℝ) : ℂ)) u
      exact continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hc)
    · refine Eventually.of_forall fun u => ?_
      simp only [digF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (-t))]
      rw [mul_assoc]
  · have hint : ∀ t ∈ Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), ‖digF s (t, u)‖ =
        t ^ (s.re - 1) * (Real.exp (-t) * |Real.log t|) := by
      intro t (ht : 0 < t)
      rw [setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => norm_digF (s := s)
        (p := (t, u)) ht hu]
      simp only
      rw [integral_const_mul, integral_const_mul, integral_abs_frullani ht]
    have hb : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ ((s.re + 1) - 1) +
        2 * (Real.exp (-t) * t ^ ((s.re - 1 / 2) - 1))) (Ioi 0) :=
      (Real.GammaIntegral_convergent (by linarith)).add
        ((Real.GammaIntegral_convergent (by linarith)).const_mul 2)
    refine (hb.mono' ?_ ?_)
    · refine ((ContinuousOn.aestronglyMeasurable
        (f := fun t : ℝ => t ^ (s.re - 1) * (Real.exp (-t) * |Real.log t|)) ?_ measurableSet_Ioi).congr ?_)
      · exact fun t (ht : 0 < t) => ((Real.continuousAt_rpow_const _ _ (Or.inl ht.ne')).mul
          ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).continuousAt.mul
            (Real.continuousAt_log ht.ne').abs)).continuousWithinAt
      · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => (hint t ht).symm)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
      rw [hint t ht, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hl := abs_log_le_add ht
      have e1 : t ^ (s.re + 1 - 1) = t ^ (s.re - 1) * t := by
        rw [show s.re + 1 - 1 = (s.re - 1) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
      have e2 : t ^ (s.re - 1 / 2 - 1) = t ^ (s.re - 1) * t ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add ht]; congr 1; ring
      rw [e1, e2]
      have h0 : 0 ≤ t ^ (s.re - 1) * Real.exp (-t) := by positivity
      have := mul_le_mul_of_nonneg_left hl h0
      nlinarith

theorem integral_cpow_exp_one_add {s : ℂ} (hs : 0 < s.re) {u : ℝ} (hu : 0 ≤ u) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * (Real.exp (-(t * u)) * Real.exp (-t) : ℝ) =
      ((1 + u : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs (r := 1 + u) (by linarith)
  have e : ∀ t : ℝ, (t : ℂ) ^ (s - 1) * (Real.exp (-(t * u)) * Real.exp (-t) : ℝ) =
      (t : ℂ) ^ (s - 1) * Complex.exp (-(((1 + u : ℝ) : ℂ) * t)) := by
    intro t
    congr 1
    rw [← Real.exp_add]; push_cast; congr 1; ring
  simp_rw [e]
  rw [h]
  congr 1
  have hr : (0:ℝ) < 1 + u := by linarith
  rw [one_div, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm), Complex.cpow_neg]

/-- **Dirichlet's formula**: `ψ(s) = ∫₀^∞ (e^{−u} − (1+u)^{−s}) du/u` for `ℜs > 1/2`. -/
theorem digamma_eq_integral {s : ℂ} (hs : 1 / 2 < s.re) :
    Complex.digamma s =
      ∫ u : ℝ in Ioi 0, ((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-s)) / u := by
  have hs0 : 0 < s.re := by linarith
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have hd := (Complex.hasDerivAt_Gamma_of_re_pos hs0).deriv
  -- `Γ'(s) = ∫∫ F`
  have hA : deriv Complex.Gamma s = ∫ t : ℝ in Ioi 0, ∫ u : ℝ in Ioi 0, digF s (t, u) := by
    rw [hd]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    simp only [digF]
    rw [integral_const_mul, integral_complex_ofReal, integral_const_mul, frullani_log ht]
    push_cast; ring
  have hint : Integrable (Function.uncurry fun t u => digF s (t, u))
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := integrable_digF hs
  rw [integral_integral_swap hint] at hA
  -- the inner integrals
  have hB : ∀ u ∈ Ioi (0:ℝ), ∫ t : ℝ in Ioi 0, digF s (t, u) =
      Complex.Gamma s * (((Real.exp (-u) : ℂ) - ((1 + u : ℝ) : ℂ) ^ (-s)) / u) := by
    intro u (hu : 0 < u)
    have i1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ)) (Ioi 0) := by
      refine (Complex.GammaIntegral_convergent hs0).congr_fun (fun t _ => by ring) measurableSet_Ioi
    have i2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        ((Real.exp (-(t * u)) * Real.exp (-t) : ℝ) : ℂ)) (Ioi 0) := by
      refine i1.norm.mono' ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable (fun t (ht : 0 < t) =>
          ((ContinuousAt.cpow (by fun_prop) continuousAt_const
            (Complex.ofReal_mem_slitPlane.2 ht)).mul (by fun_prop)).continuousWithinAt) measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
        have : Real.exp (-(t * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        have h0 : 0 ≤ ‖(t : ℂ) ^ (s - 1)‖ := norm_nonneg _
        have h1 := Real.exp_pos (-t)
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this h1.le) h0
        linarith
    have e : ∀ t : ℝ, digF s (t, u) = (1 / (u : ℂ)) * ((t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ) *
        (Real.exp (-u) : ℂ) - (t : ℂ) ^ (s - 1) * ((Real.exp (-(t * u)) * Real.exp (-t) : ℝ) : ℂ)) := by
      intro t
      simp only [digF]; push_cast; field_simp
    simp_rw [e]
    rw [integral_const_mul, integral_sub (i1.mul_const _) i2, integral_mul_const,
      integral_cpow_exp_one_add hs0 hu.le]
    have hG : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * (Real.exp (-t) : ℂ) = Complex.Gamma s := by
      rw [Complex.Gamma_eq_integral hs0, Complex.GammaIntegral]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring
    rw [hG]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hB, integral_const_mul] at hA
  rw [Complex.digamma_def, logDeriv_apply, hA]
  field_simp

end TernaryGoldbach.Explicit
