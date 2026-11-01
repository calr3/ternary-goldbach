import TernaryGoldbach.Explicit.EtaPlusBound
import TernaryGoldbach.Explicit.GammaBounds

/-!
# The Mellin transform of `η₊²` and `η₊² log`

`h_H(t) = ∫_{|ξ| ≤ a} t^{2πiξ} ĝ(ξ) dξ` (`a = H/2π`, `H = 200`) gives, for any `g` with
`|g(t)| ≤ C t^b e^{−t²/2}`, `M(h_H g)(s) = ∫_{|ξ|≤a} ĝ(ξ) M g(s + 2πiξ) dξ`. With `η₊² = h_H · h_H · t²e^{−t²}`
and `M(t²e^{−t²})(s) = Γ(s/2 + 1)/2`:
`|M(η₊²)(s)| ≤ (2a C_g)² · 8 e^{400c} e^{−c|ℑs|}` on `−1 ≤ ℜs ≤ 2` for every `0 ≤ c ≤ 0.6`.
`M(η₊² log) = M(η₊²)'` (Cauchy's estimate on circles of radius `1/2`).
-/

open Complex MeasureTheory Set Filter Metric FourierTransform
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

open TernaryGoldbach.MajorArcs (gC)
open TernaryGoldbach.Helfgott (etaPlus hH)

theorem cpow_exp_log {t : ℝ} (ht : 0 < t) (s : ℂ) (ξ : ℝ) :
    (t : ℂ) ^ (s - 1) * Complex.exp (↑(2 * π * ξ * Real.log t) * I) =
      (t : ℂ) ^ (s + ((2 * π * ξ : ℝ) : ℂ) * I - 1) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have he : Complex.exp (↑(2 * π * ξ * Real.log t) * I) = (t : ℂ) ^ (((2 * π * ξ : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
    congr 1; push_cast; ring
  rw [he, ← Complex.cpow_add _ _ ht0]
  congr 1; ring

/-- **`M(h_H g)(s) = ∫_{|ξ| ≤ a} ĝ(ξ) M g(s + 2πiξ) dξ`** for `|g(t)| ≤ C t^b e^{−t²/2}`, `ℜs + b > 0`. -/
theorem mellin_hHc_mul {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (volume.restrict (Ioi 0)))
    {C b : ℝ} (hC : 0 ≤ C) (hgb : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (t ^ b * Real.exp (-t ^ 2 / 2)))
    {s : ℂ} (hs : 0 < s.re + b) :
    mellin (fun t => hHc t * g t) s =
      ∫ ξ in Icc (-aH) aH, 𝓕 gC ξ * mellin g (s + ((2 * π * ξ : ℝ) : ℂ) * I) := by
  set F : ℝ → ℝ → ℂ := fun t ξ => (t : ℂ) ^ (s - 1) *
    (Complex.exp (↑(2 * π * ξ * Real.log t) * I) * 𝓕 gC ξ) * g t with hF
  have hstep1 : mellin (fun t => hHc t * g t) s = ∫ t in Ioi (0:ℝ), ∫ ξ in Icc (-aH) aH, F t ξ := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [smul_eq_mul, hHc, ← integral_mul_const, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
    simp only [hF]; ring
  have hI1 : Integrable (fun t : ℝ => Cg * C * (t ^ (s.re - 1 + b) * Real.exp (-t ^ 2 / 2)))
      (volume.restrict (Ioi 0)) := by
    have := integrableOn_rpow_mul_exp_quad (p := s.re - 1 + b) (a := 1 / 2) (b := 0) (by linarith)
      (by norm_num)
    refine Integrable.congr (this.const_mul (Cg * C)) (Eventually.of_forall fun t => ?_)
    simp only; ring_nf
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Icc (-aH) aH))) := by
    have hb : Integrable (fun p : ℝ × ℝ => Cg * C * (p.1 ^ (s.re - 1 + b) * Real.exp (-p.1 ^ 2 / 2)) *
        (1 : ℝ)) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Icc (-aH) aH))) :=
      Integrable.mul_prod hI1 (integrable_const (1 : ℝ))
    refine hb.mono' ?_ ?_
    · have h1 : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) ^ (s - 1) :=
        (Complex.measurable_ofReal.comp measurable_fst).pow_const _
      have h2 : Measurable fun p : ℝ × ℝ => Complex.exp (↑(2 * π * p.2 * Real.log p.1) * I) := by
        refine Complex.measurable_exp.comp (Measurable.mul ?_ measurable_const)
        exact Complex.measurable_ofReal.comp ((measurable_const.mul measurable_snd).mul
          (Real.measurable_log.comp measurable_fst))
      have h3 : Measurable fun p : ℝ × ℝ => 𝓕 gC p.2 :=
        continuous_fourier_gC'.measurable.comp measurable_snd
      have h4 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1)
          ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Icc (-aH) aH))) :=
        hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      exact ((h1.mul (h2.mul h3)).aestronglyMeasurable).mul h4
    · rw [Measure.prod_restrict]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Icc)).2
        (Eventually.of_forall fun p hp => ?_)
      have ht : 0 < p.1 := hp.1
      simp only [Function.uncurry, hF, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Real.norm_eq_abs, mul_one]
      have hsr : (s - 1).re = s.re - 1 := by simp
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, hsr]
      have hF0 := norm_fourier_gC_le p.2
      have hg0 := hgb p.1 ht
      have hpow : p.1 ^ (s.re - 1) * p.1 ^ b = p.1 ^ (s.re - 1 + b) := (Real.rpow_add ht _ _).symm
      have hp0 : 0 ≤ p.1 ^ (s.re - 1) := by positivity
      have hgb0 : 0 ≤ C * (p.1 ^ b * Real.exp (-p.1 ^ 2 / 2)) := by positivity
      calc p.1 ^ (s.re - 1) * ‖𝓕 gC p.2‖ * ‖g p.1‖
          ≤ p.1 ^ (s.re - 1) * Cg * (C * (p.1 ^ b * Real.exp (-p.1 ^ 2 / 2))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hF0 hp0) hg0 (norm_nonneg _) (by
              have := Cg_nonneg; positivity)
        _ = Cg * C * ((p.1 ^ (s.re - 1) * p.1 ^ b) * Real.exp (-p.1 ^ 2 / 2)) := by ring
        _ = _ := by rw [hpow]
  rw [hstep1, integral_integral_swap hprod]
  refine setIntegral_congr_fun measurableSet_Icc fun ξ _ => ?_
  rw [mellin, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [hF, smul_eq_mul]
  rw [← cpow_exp_log ht s ξ]; ring

theorem norm_integral_gC_le {F : ℝ → ℂ} {B : ℝ} (hB : ∀ ξ ∈ Icc (-aH) aH, ‖F ξ‖ ≤ B) :
    ‖∫ ξ in Icc (-aH) aH, 𝓕 gC ξ * F ξ‖ ≤ Cg * B * (2 * aH) := by
  have hvol : volume.real (Icc (-aH) aH) = 2 * aH := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [aH_pos])]; ring
  rw [mul_assoc, ← hvol]
  refine (norm_setIntegral_le_of_norm_le_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
    (C := Cg * B) fun ξ hξ => ?_).trans (le_of_eq (by ring))
  rw [norm_mul]
  exact mul_le_mul (norm_fourier_gC_le ξ) (hB ξ hξ) (norm_nonneg _) Cg_nonneg

/-! ## `t² e^{−t²}` -/

/-- `g₀(t) = t² e^{−t²}`. -/
noncomputable def g0 (t : ℝ) : ℂ := ((t ^ 2 * Real.exp (-t ^ 2) : ℝ) : ℂ)

theorem mellin_g0 {s : ℂ} (hs : -2 < s.re) : mellin g0 s = (1 / 2 : ℂ) * Complex.Gamma ((s + 2) / 2) := by
  have e1 : g0 = fun t : ℝ => (t : ℂ) ^ (2 : ℂ) • ((Real.exp (-(t ^ (2 : ℝ))) : ℝ) : ℂ) := by
    ext t
    simp only [g0, smul_eq_mul, Real.rpow_two]
    push_cast
    rw [Complex.cpow_two]
  rw [e1, mellin_cpow_smul, mellin_comp_rpow (fun v : ℝ => ((Real.exp (-v) : ℝ) : ℂ)) _ 2, abs_two,
    ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral (by simp; linarith)]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem cos_12_ge : (0.357 : ℝ) ≤ Real.cos 1.2 := by
  rw [← Real.sin_pi_div_two_sub]
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have hx0 : 0 < π / 2 - 1.2 := by linarith
  have hx1 : π / 2 - 1.2 ≤ 1 := by linarith
  have := Real.sin_gt_sub_cube hx0
  have hx2 : 0.3707 ≤ π / 2 - 1.2 := by linarith
  have hx3 : π / 2 - 1.2 ≤ 0.371 := by linarith
  nlinarith [sq_nonneg (π / 2 - 1.2), mul_pos hx0 hx0]

theorem Gamma_le_two {x : ℝ} (h1 : 1 / 2 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 2 := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc (x := 1 / 2) (y := 2) (z := x)
    (show (1 / 2 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num) ⟨h1, h2⟩
  refine h.trans (max_le ?_ ?_)
  · rw [Real.Gamma_one_half_eq]
    have := Real.sqrt_le_sqrt (show π ≤ 4 by linarith [Real.pi_lt_d2])
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    exact this
  · rw [Real.Gamma_two]; norm_num

/-- `|M(t²e^{−t²})(s)| ≤ 8 e^{−0.6|ℑs|}` on `−1 ≤ ℜs ≤ 2`. -/
theorem norm_mellin_g0_le {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    ‖mellin g0 s‖ ≤ 8 * Real.exp (-(0.6 * |s.im|)) := by
  rw [mellin_g0 (by linarith), norm_mul]
  set a := (s + 2) / 2 with ha
  have hare : a.re = (s.re + 2) / 2 := by simp [ha]
  have haim : a.im = s.im / 2 := by simp [ha]
  have hpi := Real.pi_gt_d2
  have hG := norm_Gamma_le_rot (a := a) (by rw [hare]; linarith) (φ := 1.2) (by norm_num)
    (by linarith)
  have hc := cos_12_ge
  have hc0 : 0 < Real.cos 1.2 := by linarith
  have hc1 : Real.cos 1.2 ≤ 1 := Real.cos_le_one _
  have hΓ : Real.Gamma a.re ≤ 2 := Gamma_le_two (by rw [hare]; linarith) (by rw [hare]; linarith)
  have hΓ0 : 0 ≤ Real.Gamma a.re := (Real.Gamma_pos_of_pos (by rw [hare]; linarith)).le
  have hcp : Real.cos 1.2 ^ (-a.re) ≤ 7.85 := by
    rw [Real.rpow_neg hc0.le, ← Real.inv_rpow hc0.le]
    have hi1 : 1 ≤ (Real.cos 1.2)⁻¹ := one_le_inv₀ hc0 |>.2 hc1
    have hi2 : (Real.cos 1.2)⁻¹ ≤ 1 / 0.357 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hc
    calc (Real.cos 1.2)⁻¹ ^ a.re ≤ (Real.cos 1.2)⁻¹ ^ (2:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hi1 (by rw [hare]; linarith)
      _ = ((Real.cos 1.2)⁻¹) ^ 2 := Real.rpow_two _
      _ ≤ (1 / 0.357) ^ 2 := pow_le_pow_left₀ (by linarith) hi2 2
      _ ≤ 7.85 := by norm_num
  have hcp0 : 0 ≤ Real.cos 1.2 ^ (-a.re) := Real.rpow_nonneg hc0.le _
  have he : Real.exp (-(1.2 * |a.im|)) = Real.exp (-(0.6 * |s.im|)) := by
    rw [haim, abs_div, abs_two]; congr 1; ring
  rw [he] at hG
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by rw [norm_div, norm_one, Complex.norm_ofNat]
  rw [hn]
  have hE := Real.exp_pos (-(0.6 * |s.im|))
  calc 1 / 2 * ‖Complex.Gamma a‖ ≤ 1 / 2 * (Real.exp (-(0.6 * |s.im|)) * Real.Gamma a.re *
        Real.cos 1.2 ^ (-a.re)) := by gcongr
    _ ≤ 1 / 2 * (Real.exp (-(0.6 * |s.im|)) * 2 * 7.85) := by gcongr
    _ ≤ 8 * Real.exp (-(0.6 * |s.im|)) := by nlinarith

/-! ## `η₊²` and `η₊² log` -/

/-- `φ₁ = η₊²`. -/
noncomputable def phi1 (t : ℝ) : ℂ := ((etaPlus t ^ 2 : ℝ) : ℂ)
/-- `φ₂ = η₊² log`. -/
noncomputable def phi2 (t : ℝ) : ℂ := (Real.log t : ℂ) * phi1 t

theorem continuous_g0 : Continuous g0 := by unfold g0; fun_prop

theorem norm_hHc_le {t : ℝ} (ht : 0 < t) : ‖hHc t‖ ≤ 3.15 := by
  rw [← hH_eq_hHc ht, Complex.norm_real, Real.norm_eq_abs]; exact abs_hH_le ht.le

theorem norm_g0 (t : ℝ) : ‖g0 t‖ = t ^ 2 * Real.exp (-t ^ 2) := by
  rw [g0, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem g0_le (t : ℝ) (_ht : 0 < t) : ‖g0 t‖ ≤ 1 * (t ^ (2:ℝ) * Real.exp (-t ^ 2 / 2)) := by
  rw [norm_g0, Real.rpow_two, one_mul]
  have : Real.exp (-t ^ 2) ≤ Real.exp (-t ^ 2 / 2) := Real.exp_le_exp.2 (by nlinarith [sq_nonneg t])
  exact mul_le_mul_of_nonneg_left this (sq_nonneg t)

theorem hg0_le (t : ℝ) (ht : 0 < t) : ‖hHc t * g0 t‖ ≤ 3.15 * (t ^ (2:ℝ) * Real.exp (-t ^ 2 / 2)) := by
  rw [norm_mul]
  have h2 := g0_le t ht
  rw [one_mul] at h2
  exact mul_le_mul (norm_hHc_le ht) h2 (norm_nonneg _) (by norm_num)

theorem continuousOn_hg0 : ContinuousOn (fun t => hHc t * g0 t) (Ioi 0) := fun t ht =>
  ((continuousAt_hHc ht).mul continuous_g0.continuousAt).continuousWithinAt

theorem phi1_eq {t : ℝ} (ht : 0 < t) : phi1 t = hHc t * (hHc t * g0 t) := by
  have he : Real.exp (-t ^ 2 / 2) ^ 2 = Real.exp (-t ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e : (hH 200 t * t * Real.exp (-t ^ 2 / 2)) ^ 2 =
      hH 200 t * (hH 200 t * (t ^ 2 * Real.exp (-t ^ 2))) := by
    rw [mul_pow, mul_pow, he]; ring
  rw [phi1, TernaryGoldbach.Helfgott.etaPlus, e, ← hH_eq_hHc ht, g0]; push_cast; ring

theorem mellin_hg0_eq {w : ℂ} (hw : -2 < w.re) :
    mellin (fun t => hHc t * g0 t) w =
      ∫ ξ in Icc (-aH) aH, 𝓕 gC ξ * mellin g0 (w + ((2 * π * ξ : ℝ) : ℂ) * I) :=
  mellin_hHc_mul continuous_g0.aestronglyMeasurable (C := 1) (b := 2) (by norm_num) g0_le (by linarith)

theorem mellin_phi1_eq {s : ℂ} (hs : -2 < s.re) :
    mellin phi1 s = ∫ ξ in Icc (-aH) aH,
      𝓕 gC ξ * mellin (fun t => hHc t * g0 t) (s + ((2 * π * ξ : ℝ) : ℂ) * I) := by
  have : mellin phi1 s = mellin (fun t => hHc t * (hHc t * g0 t)) s :=
    setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => by simp only; rw [phi1_eq ht]
  rw [this]
  exact mellin_hHc_mul (continuousOn_hg0.aestronglyMeasurable measurableSet_Ioi) (C := 3.15) (b := 2)
    (by norm_num) hg0_le (by linarith)

theorem exp_shift_le {c y u : ℝ} (hc : 0 ≤ c) (hu : |u| ≤ 200) :
    Real.exp (-(c * |y + u|)) ≤ Real.exp (200 * c) * Real.exp (-(c * |y|)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h := abs_add_le (y + u) (-u)
  rw [abs_neg, add_neg_cancel_right] at h
  nlinarith

theorem norm_mellin_hg0_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 0.6) {w : ℂ} (h1 : -1 ≤ w.re)
    (h2 : w.re ≤ 2) :
    ‖mellin (fun t => hHc t * g0 t) w‖ ≤
      Cg * (8 * (Real.exp (200 * c) * Real.exp (-(c * |w.im|)))) * (2 * aH) := by
  rw [mellin_hg0_eq (by linarith)]
  refine norm_integral_gC_le fun ξ hξ => ?_
  have hre : (w + ((2 * π * ξ : ℝ) : ℂ) * I).re = w.re := by simp
  have him : (w + ((2 * π * ξ : ℝ) : ℂ) * I).im = w.im + 2 * π * ξ := by simp
  have h := norm_mellin_g0_le (s := w + ((2 * π * ξ : ℝ) : ℂ) * I) (by rw [hre]; exact h1)
    (by rw [hre]; exact h2)
  rw [him] at h
  have h3 : Real.exp (-(0.6 * |w.im + 2 * π * ξ|)) ≤ Real.exp (-(c * |w.im + 2 * π * ξ|)) :=
    Real.exp_le_exp.2 (by nlinarith [abs_nonneg (w.im + 2 * π * ξ)])
  have h4 := exp_shift_le (y := w.im) hc0 (abs_shift_le hξ)
  calc _ ≤ 8 * Real.exp (-(0.6 * |w.im + 2 * π * ξ|)) := h
    _ ≤ 8 * (Real.exp (200 * c) * Real.exp (-(c * |w.im|))) := by gcongr; exact h3.trans h4

/-- **`|M(η₊²)(s)| ≤ (2a C_g)² · 8 e^{400c} e^{−c|ℑs|}`** on `−1 ≤ ℜs ≤ 2`, `0 ≤ c ≤ 0.6`. -/
theorem norm_mellin_phi1_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 0.6) {s : ℂ} (h1 : -1 ≤ s.re)
    (h2 : s.re ≤ 2) :
    ‖mellin phi1 s‖ ≤ (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * c) * Real.exp (-(c * |s.im|)) := by
  rw [mellin_phi1_eq (by linarith)]
  refine (norm_integral_gC_le (B := Cg * (8 * (Real.exp (200 * c) * (Real.exp (200 * c) *
    Real.exp (-(c * |s.im|))))) * (2 * aH)) fun ξ hξ => ?_).trans (le_of_eq ?_)
  · have hre : (s + ((2 * π * ξ : ℝ) : ℂ) * I).re = s.re := by simp
    have him : (s + ((2 * π * ξ : ℝ) : ℂ) * I).im = s.im + 2 * π * ξ := by simp
    have h := norm_mellin_hg0_le hc0 hc (w := s + ((2 * π * ξ : ℝ) : ℂ) * I) (by rw [hre]; exact h1)
      (by rw [hre]; exact h2)
    rw [him] at h
    refine h.trans ?_
    have h4 := exp_shift_le (y := s.im) hc0 (abs_shift_le hξ)
    have := Cg_nonneg; have := aH_pos
    gcongr
  · have : Real.exp (400 * c) = Real.exp (200 * c) * Real.exp (200 * c) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring

theorem norm_phi1 (t : ℝ) : ‖phi1 t‖ = etaPlus t ^ 2 := by
  rw [phi1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

theorem etaPlus_sq_le {t : ℝ} (ht : 0 ≤ t) : etaPlus t ^ 2 ≤ 9.9225 * (t ^ 2 * Real.exp (-t ^ 2)) := by
  have h := norm_fP_le (δ := 0) ht
  rw [norm_fP] at h
  have := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at this
  refine this.trans (le_of_eq ?_)
  have he : Real.exp (-t ^ 2 / 2) ^ 2 = Real.exp (-t ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, mul_pow, he]; norm_num

theorem phi1_isBigO_top : phi1 =O[atTop] fun t => Real.exp (-1 * t) := by
  refine Asymptotics.IsBigO.of_bound (9.9225 * 2 * Real.exp 1) ?_
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [norm_phi1, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (etaPlus_sq_le ht).trans ?_
  have h1 : t ^ 2 ≤ 2 * Real.exp t := by nlinarith [Real.quadratic_le_exp_of_nonneg ht]
  have h2 : Real.exp t * Real.exp (-t ^ 2) ≤ Real.exp 1 * Real.exp (-1 * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (t - 1)])
  have hE := Real.exp_pos (-t ^ 2)
  calc 9.9225 * (t ^ 2 * Real.exp (-t ^ 2)) ≤ 9.9225 * (2 * Real.exp t * Real.exp (-t ^ 2)) := by
        gcongr
    _ = 9.9225 * 2 * (Real.exp t * Real.exp (-t ^ 2)) := by ring
    _ ≤ 9.9225 * 2 * (Real.exp 1 * Real.exp (-1 * t)) := by gcongr
    _ = _ := by ring

theorem phi1_isBigO_bot : phi1 =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-2 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 9.9225 ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  rw [norm_phi1, neg_neg, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht _), Real.rpow_two]
  refine (etaPlus_sq_le ht.le).trans ?_
  have h1 : Real.exp (-t ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg t])
  have h0 : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith

theorem continuousAt_phi1 {y : ℝ} (hy : 0 < y) : ContinuousAt phi1 y := by
  have hev : phi1 =ᶠ[𝓝 y] fun t => hHc t * (hHc t * g0 t) := by
    filter_upwards [lt_mem_nhds hy] with t ht using phi1_eq ht
  exact ContinuousAt.congr ((continuousAt_hHc hy).mul ((continuousAt_hHc hy).mul
    continuous_g0.continuousAt)) hev.symm

theorem continuousOn_phi1 : ContinuousOn phi1 (Ioi 0) := fun y hy =>
  (continuousAt_phi1 hy).continuousWithinAt

theorem continuousAt_phi2 {y : ℝ} (hy : 0 < y) : ContinuousAt phi2 y :=
  (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hy.ne')).mul (continuousAt_phi1 hy)

theorem differentiableAt_mellin_phi1 {s : ℂ} (hs : -2 < s.re) : DifferentiableAt ℂ (mellin phi1) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) (b := -2) one_pos
    (continuousOn_phi1.locallyIntegrableOn measurableSet_Ioi) phi1_isBigO_top phi1_isBigO_bot hs

theorem hasDerivAt_mellin_phi1 {s : ℂ} (hs : -2 < s.re) :
    MellinConvergent phi2 s ∧ HasDerivAt (mellin phi1) (mellin phi2 s) s := by
  have h := mellin_hasDerivAt_of_isBigO_rpow (b := -2) (f := phi1) (s := s)
    (continuousOn_phi1.locallyIntegrableOn measurableSet_Ioi)
    (phi1_isBigO_top.trans (isLittleO_exp_neg_mul_rpow_atTop one_pos _).isBigO) (lt_add_one _)
    phi1_isBigO_bot hs
  have e : (fun t : ℝ => Real.log t • phi1 t) = phi2 := by ext t; rw [phi2, Complex.real_smul]
  rw [e] at h; exact h

/-- **Cauchy's estimate**: `|M(η₊² log)(s)| ≤ 2 (2a C_g)² 8 e^{400c} e^{c/2} e^{−c|ℑs|}` on
`−1/2 ≤ ℜs ≤ 3/2`. -/
theorem norm_mellin_phi2_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 0.6) {s : ℂ} (h1 : -1 / 2 ≤ s.re)
    (h2 : s.re ≤ 3 / 2) :
    ‖mellin phi2 s‖ ≤ 2 * ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * c) * Real.exp (c / 2)) *
      Real.exp (-(c * |s.im|)) := by
  have hd := (hasDerivAt_mellin_phi1 (s := s) (by linarith)).2
  rw [← hd.deriv]
  set M := (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * c) * Real.exp (c / 2) *
    Real.exp (-(c * |s.im|)) with hM
  have hD : DiffContOnCl ℂ (mellin phi1) (ball s (1 / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball s (by norm_num)]
    intro z hz
    refine (differentiableAt_mellin_phi1 ?_).differentiableWithinAt
    rw [mem_closedBall, dist_eq_norm] at hz
    have h := Complex.abs_re_le_norm (z - s)
    rw [Complex.sub_re] at h
    have := (abs_le.1 (h.trans hz)).1
    linarith
  have hC : ∀ z ∈ sphere s (1 / 2), ‖mellin phi1 z‖ ≤ M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have hre := Complex.abs_re_le_norm (z - s)
    have him := Complex.abs_im_le_norm (z - s)
    rw [hz, Complex.sub_re] at hre
    rw [hz, Complex.sub_im] at him
    have hr := abs_le.1 hre
    refine (norm_mellin_phi1_le hc0 hc (by linarith) (by linarith)).trans ?_
    have hi : |s.im| ≤ |z.im| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub s.im z.im
      rw [abs_sub_comm] at this; linarith
    have : Real.exp (-(c * |z.im|)) ≤ Real.exp (c / 2) * Real.exp (-(c * |s.im|)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have h0 : 0 ≤ (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * c) := by positivity
    calc (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * c) * Real.exp (-(c * |z.im|))
        ≤ (Cg * (2 * aH)) ^ 2 * 8 * Real.exp (400 * c) *
            (Real.exp (c / 2) * Real.exp (-(c * |s.im|))) := mul_le_mul_of_nonneg_left this h0
      _ = M := by rw [hM]; ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ) < 1 / 2) hD hC
  calc ‖deriv (mellin phi1) s‖ ≤ M / (1 / 2) := this
    _ = _ := by rw [hM]; ring

/-- `η₊²` is an admissible smoothing. -/
theorem goodSmoothing_phi1 :
    GoodSmoothing phi1 ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1) (1 / 400) where
  continuousAt := fun y hy => continuousAt_phi1 hy
  conv := mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := -2) one_pos
    (continuousOn_phi1.locallyIntegrableOn measurableSet_Ioi) phi1_isBigO_top phi1_isBigO_bot
    (by norm_num)
  diff := fun s hs => differentiableAt_mellin_phi1 (by linarith)
  c_pos := by norm_num
  strip := fun s h1 h2 => by
    have := norm_mellin_phi1_le (c := 1 / 400) (by norm_num) (by norm_num) (s := s) (by linarith)
      (by linarith)
    rwa [show (400:ℝ) * (1 / 400) = 1 by norm_num] at this

/-- `η₊² log` is an admissible smoothing. -/
theorem goodSmoothing_phi2 :
    GoodSmoothing phi2 (2 * ((Cg * (2 * aH)) ^ 2 * 8 * Real.exp 1 * Real.exp (1 / 800))) (1 / 400) where
  continuousAt := fun y hy => continuousAt_phi2 hy
  conv := (hasDerivAt_mellin_phi1 (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)).1
  diff := fun s hs => by
    set U : Set ℂ := {z : ℂ | -2 < z.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hsU : s ∈ U := show -2 < s.re by linarith
    have hdiff : DifferentiableOn ℂ (mellin phi1) U := fun z hz =>
      (differentiableAt_mellin_phi1 hz).differentiableWithinAt
    have hev : mellin phi2 =ᶠ[𝓝 s] deriv (mellin phi1) := by
      filter_upwards [hUo.mem_nhds hsU] with z hz using ((hasDerivAt_mellin_phi1 hz).2.deriv).symm
    exact (((hdiff.deriv hUo) s hsU).differentiableAt (hUo.mem_nhds hsU)).congr_of_eventuallyEq hev
  c_pos := by norm_num
  strip := fun s h1 h2 => by
    have := norm_mellin_phi2_le (c := 1 / 400) (by norm_num) (by norm_num) (s := s) h1 h2
    rwa [show (400:ℝ) * (1 / 400) = 1 by norm_num, show (1 / 400 : ℝ) / 2 = 1 / 800 by norm_num] at this

/-- `Σ Λ(n) χ(n) φ(n/x)` converges absolutely for an admissible smoothing. -/
theorem summable_SsumG {N : ℕ} (χ : DirichletCharacter ℂ N) {φ : ℝ → ℂ} {K c : ℝ}
    (hφ : GoodSmoothing φ K c) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ => (Λ n : ℂ) * χ n * φ (n / x) := by
  set I0 := ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ with hI0
  have hI00 : 0 ≤ I0 := integral_nonneg fun t => norm_nonneg _
  refine Summable.of_norm_bounded (summable_C3.mul_right (x ^ (3 / 2 : ℝ) * I0 / (2 * π))) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [eq_integral_Fterm hφ hx hn, norm_mul, norm_mul, norm_mul]
    have hΛ : ‖(Λ n : ℂ)‖ = Λ n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2π : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    have hint : ‖∫ t, Fterm φ x n t‖ ≤ ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ)) * I0 := by
      rw [hI0, ← integral_norm_Fterm φ hx hn]; exact norm_integral_le_integral_norm _
    rw [hΛ, h2π]
    have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hn0 : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by positivity
    calc Λ n * ‖χ n‖ * (1 / (2 * π) * ‖∫ t, Fterm φ x n t‖)
        ≤ Λ n * 1 * (1 / (2 * π) * (((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ)) * I0)) := by
          gcongr
      _ = Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (x ^ (3 / 2 : ℝ) * I0 / (2 * π)) := by ring

end TernaryGoldbach.Explicit
