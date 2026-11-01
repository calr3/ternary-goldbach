import TernaryGoldbach.Explicit.GrExtend
import TernaryGoldbach.Explicit.ZetaBound
import TernaryGoldbach.MajorArcs.HHFourier

/-!
# The Mellin transform of `η₊(t) e(δt)`

`h_H(t) = ∫_{|ξ| ≤ H/2π} t^{2πiξ} ĝ(ξ) dξ` (`MajorArcs.hH_eq_fourier`, `g(u) = h(eᵘ)`), so for `ℜs > −1`
`M₊(s) = ∫_{|ξ| ≤ H/2π} ĝ(ξ) G_δ(s − 1 + 2πiξ) dξ` (`H = 200`), and the bounds for `G_δ` (shifted by at most
`H` in height) transfer to `M₊`.
-/

open Complex MeasureTheory Set Filter Asymptotics FourierTransform
open scoped Real Topology

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.MajorArcs (gC gL hH_eq_fourier integrable_gC)
open TernaryGoldbach.Helfgott (hH etaPlus)

/-- `a = H/2π`, `H = 200`. -/
noncomputable def aH : ℝ := 200 / (2 * π)

theorem aH_pos : 0 < aH := by unfold aH; positivity

/-- The Fourier representation of `h_H`. -/
noncomputable def hHc (t : ℝ) : ℂ :=
  ∫ ξ in Icc (-aH) aH, Complex.exp (↑(2 * π * ξ * Real.log t) * I) * 𝓕 gC ξ

theorem hH_eq_hHc {t : ℝ} (ht : 0 < t) : (hH 200 t : ℂ) = hHc t := by
  rw [hH_eq_fourier (by norm_num) ht, hHc, aH]

/-- `C_g = ∫ |g|`. -/
noncomputable def Cg : ℝ := ∫ u, ‖gC u‖

theorem norm_fourier_gC_le (ξ : ℝ) : ‖𝓕 gC ξ‖ ≤ Cg := Real.norm_fourier_le_integral_norm gC ξ

theorem Cg_nonneg : 0 ≤ Cg := integral_nonneg fun _ => norm_nonneg _

theorem continuous_fourier_gC' : Continuous (𝓕 gC) := MajorArcs.continuous_fourier_gC

theorem continuousAt_hHc {t₀ : ℝ} (ht₀ : 0 < t₀) : ContinuousAt hHc t₀ := by
  unfold hHc
  refine continuousAt_of_dominated (bound := fun ξ => Cg) ?_ ?_ (integrable_const _) ?_
  · refine Eventually.of_forall fun t => ?_
    exact ((by fun_prop : Continuous fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * Real.log t) * I)).mul
      continuous_fourier_gC').aestronglyMeasurable
  · refine Eventually.of_forall fun t => Eventually.of_forall fun ξ => ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_fourier_gC_le ξ
  · refine Eventually.of_forall fun ξ => ?_
    have hlog : ContinuousAt Real.log t₀ := Real.continuousAt_log ht₀.ne'
    exact ((Complex.continuous_exp.continuousAt.comp ((Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_const.mul hlog))).mul continuousAt_const)).mul continuousAt_const)

theorem abs_hH_le {t : ℝ} (ht : 0 ≤ t) : |hH 200 t| ≤ 3.15 := TernaryGoldbach.Helfgott.abs_hH200_le ht

/-- `φ₊(t) = η₊(t) e(δt)`. -/
noncomputable def fP (δ t : ℝ) : ℂ := ((etaPlus t : ℝ) : ℂ) * Complex.exp (2 * π * I * δ * t)

theorem norm_fP (δ t : ℝ) : ‖fP δ t‖ = |etaPlus t| := by
  rw [fP, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : ‖Complex.exp (2 * π * I * δ * t)‖ = 1 := by rw [Complex.norm_exp]; simp
  rw [this, mul_one]

theorem norm_fP_le {δ t : ℝ} (ht : 0 ≤ t) : ‖fP δ t‖ ≤ 3.15 * (t * Real.exp (-t ^ 2 / 2)) := by
  rw [norm_fP, TernaryGoldbach.Helfgott.etaPlus, abs_mul, abs_mul, abs_of_nonneg ht,
    abs_of_pos (Real.exp_pos _)]
  have := abs_hH_le ht
  have h0 : 0 ≤ t * Real.exp (-t ^ 2 / 2) := by positivity
  nlinarith

theorem fP_eq {δ t : ℝ} (ht : 0 < t) :
    fP δ t = hHc t * (((t * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * Complex.exp (2 * π * I * δ * t)) := by
  rw [fP, ← hH_eq_hHc ht, TernaryGoldbach.Helfgott.etaPlus]; push_cast; ring

theorem continuousAt_fP (δ : ℝ) {y : ℝ} (hy : 0 < y) : ContinuousAt (fP δ) y := by
  have hev : fP δ =ᶠ[𝓝 y] fun t => hHc t * (((t * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) *
      Complex.exp (2 * π * I * δ * t)) := by
    filter_upwards [lt_mem_nhds hy] with t ht using fP_eq ht
  refine ContinuousAt.congr ?_ hev.symm
  exact (continuousAt_hHc hy).mul (by fun_prop)

theorem continuousOn_fP (δ : ℝ) : ContinuousOn (fP δ) (Ioi 0) := fun y hy =>
  (continuousAt_fP δ hy).continuousWithinAt

theorem fP_isBigO_top (δ : ℝ) : fP δ =O[atTop] fun t => Real.exp (-1 * t) := by
  refine Asymptotics.IsBigO.of_bound (3.15 * Real.exp 4) ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  refine (norm_fP_le ht).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have h1 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h2 : Real.exp t * Real.exp (-t ^ 2 / 2) ≤ Real.exp 2 * Real.exp (-1 * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 2)])
  have h3 : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.2 (by norm_num)
  calc 3.15 * (t * Real.exp (-t ^ 2 / 2)) ≤ 3.15 * (Real.exp t * Real.exp (-t ^ 2 / 2)) := by gcongr
    _ ≤ 3.15 * (Real.exp 2 * Real.exp (-1 * t)) := by gcongr
    _ ≤ 3.15 * (Real.exp 4 * Real.exp (-1 * t)) := by gcongr
    _ = _ := by ring

theorem fP_isBigO_bot (δ : ℝ) : fP δ =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 3.15 ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  refine (norm_fP_le ht.le).trans ?_
  rw [neg_neg, Real.rpow_one, Real.norm_eq_abs, abs_of_pos ht]
  have : Real.exp (-t ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  nlinarith

theorem differentiableAt_mellin_fP (δ : ℝ) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (mellin (fP δ)) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := -1) one_pos
    ((continuousOn_fP δ).locallyIntegrableOn measurableSet_Ioi) (fP_isBigO_top δ) (fP_isBigO_bot δ) hs

theorem mellinConvergent_fP (δ : ℝ) {s : ℂ} (hs : -1 < s.re) : MellinConvergent (fP δ) s :=
  mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := -1) one_pos
    ((continuousOn_fP δ).locallyIntegrableOn measurableSet_Ioi) (fP_isBigO_top δ) (fP_isBigO_bot δ) hs

/-! ## The convolution formula -/

theorem cpow_mul_exp_log {t : ℝ} (ht : 0 < t) (s : ℂ) (ξ : ℝ) :
    (t : ℂ) ^ (s - 1) * Complex.exp (↑(2 * π * ξ * Real.log t) * I) * (t : ℂ) =
      (t : ℂ) ^ (s - 1 + ((2 * π * ξ : ℝ) : ℂ) * I - 1) * (t : ℂ) ^ (2 : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have he : Complex.exp (↑(2 * π * ξ * Real.log t) * I) = (t : ℂ) ^ (((2 * π * ξ : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
    congr 1; push_cast; ring
  rw [he, ← Complex.cpow_add _ _ ht0, ← Complex.cpow_add _ _ ht0]
  nth_rewrite 2 [show (t : ℂ) = (t : ℂ) ^ (1 : ℂ) from (Complex.cpow_one _).symm]
  rw [← Complex.cpow_add _ _ ht0]
  congr 1; ring

/-- **`M₊(s) = ∫_{|ξ| ≤ a} ĝ(ξ) G_δ(s − 1 + 2πiξ) dξ`** for `ℜs > −1`. -/
theorem mellin_fP_eq (δ : ℝ) {s : ℂ} (hs : -1 < s.re) :
    mellin (fP δ) s = ∫ ξ in Icc (-aH) aH, 𝓕 gC ξ * Gr (s - 1 + ((2 * π * ξ : ℝ) : ℂ) * I) δ 0 := by
  set g1 : ℝ → ℂ := fun t => ((t * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * Complex.exp (2 * π * I * δ * t)
    with hg1
  set F : ℝ → ℝ → ℂ := fun t ξ => (t : ℂ) ^ (s - 1) *
    (Complex.exp (↑(2 * π * ξ * Real.log t) * I) * 𝓕 gC ξ) * g1 t with hF
  have hstep1 : mellin (fP δ) s = ∫ t in Ioi (0:ℝ), ∫ ξ in Icc (-aH) aH, F t ξ := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [smul_eq_mul, fP_eq ht, hHc, ← integral_mul_const, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
    simp only [hF, hg1]; ring
  -- integrability on the product
  have hσ : -1 < s.re := hs
  have hI1 : Integrable (fun t : ℝ => Cg * (t ^ s.re * Real.exp (-t ^ 2 / 2))) (volume.restrict (Ioi 0)) := by
    have := integrableOn_rpow_mul_exp_quad (p := s.re) (a := 1 / 2) (b := 0) hσ (by norm_num)
    refine Integrable.congr (this.const_mul Cg) (Eventually.of_forall fun t => ?_)
    simp only; ring_nf
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Icc (-aH) aH))) := by
    have hb : Integrable (fun p : ℝ × ℝ => Cg * (p.1 ^ s.re * Real.exp (-p.1 ^ 2 / 2)) * (1 : ℝ))
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Icc (-aH) aH))) :=
      Integrable.mul_prod hI1 (integrable_const (1 : ℝ))
    refine hb.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hF, hg1]
      have h1 : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 1) :=
        (Complex.measurable_ofReal.comp measurable_fst).pow_const _
      have h2 : Measurable fun p : ℝ × ℝ => Complex.exp (↑(2 * π * p.2 * Real.log p.1) * I) := by
        refine Complex.measurable_exp.comp (Measurable.mul ?_ measurable_const)
        exact Complex.measurable_ofReal.comp ((measurable_const.mul measurable_snd).mul
          (Real.measurable_log.comp measurable_fst))
      have h3 : Measurable fun p : ℝ × ℝ => 𝓕 gC p.2 := continuous_fourier_gC'.measurable.comp measurable_snd
      have h4 : Measurable fun p : ℝ × ℝ => ((p.1 * Real.exp (-p.1 ^ 2 / 2) : ℝ) : ℂ) *
          Complex.exp (2 * π * I * δ * p.1) := by
        refine Measurable.mul ?_ ?_
        · exact Complex.measurable_ofReal.comp (by fun_prop)
        · exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp measurable_fst))
      exact (h1.mul (h2.mul h3)).mul h4
    · rw [Measure.prod_restrict]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Icc)).2
        (Eventually.of_forall fun p hp => ?_)
      have ht : 0 < p.1 := hp.1
      simp only [Function.uncurry, hF, hg1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_real, Real.norm_eq_abs, mul_one]
      have hE : ‖Complex.exp (2 * π * I * δ * p.1)‖ = 1 := by rw [Complex.norm_exp]; simp
      have hsr : (s - 1).re = s.re - 1 := by simp
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, abs_of_pos ht, abs_of_pos (Real.exp_pos _), hE,
        mul_one, hsr]
      have hF0 := norm_fourier_gC_le p.2
      have hpow : p.1 ^ (s.re - 1) * p.1 = p.1 ^ s.re := by
        rw [Real.rpow_sub ht, Real.rpow_one, div_mul_cancel₀ _ ht.ne']
      calc p.1 ^ (s.re - 1) * ‖𝓕 gC p.2‖ * (p.1 * Real.exp (-p.1 ^ 2 / 2))
          = ‖𝓕 gC p.2‖ * ((p.1 ^ (s.re - 1) * p.1) * Real.exp (-p.1 ^ 2 / 2)) := by ring
        _ ≤ Cg * (p.1 ^ s.re * Real.exp (-p.1 ^ 2 / 2)) := by
            rw [hpow]; exact mul_le_mul_of_nonneg_right hF0 (by positivity)
  rw [hstep1, integral_integral_swap hprod]
  refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
  rw [Gr_zero_eq, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hF, hg1]
  have key := cpow_mul_exp_log ht s ξ
  have ht2 : (t : ℂ) ^ (2 : ℂ) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; push_cast; ring
  calc (t : ℂ) ^ (s - 1) * (Complex.exp (↑(2 * π * ξ * Real.log t) * I) * 𝓕 gC ξ) *
        (((t * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * Complex.exp (2 * π * I * δ * t))
      = 𝓕 gC ξ * (((t : ℂ) ^ (s - 1) * Complex.exp (↑(2 * π * ξ * Real.log t) * I) * (t : ℂ)) *
          (Real.exp (-t ^ 2 / 2) : ℂ) * Complex.exp (2 * π * I * δ * t)) := by push_cast; ring
    _ = 𝓕 gC ξ * ((t : ℂ) ^ (s - 1 + ((2 * π * ξ : ℝ) : ℂ) * I - 1) *
          (((t ^ 2 * Real.exp (-t ^ 2 / 2) : ℝ) : ℂ) * Complex.exp (2 * π * I * δ * t))) := by
        rw [key, ht2]; push_cast; ring

end TernaryGoldbach.Explicit
