import TernaryGoldbach.MajorArcs.EtaCirc
import TernaryGoldbach.Helfgott.HHBound

/-!
# `η₊ − η◦` in `L²`, via the Fourier transform in logarithmic coordinates

With `g(u) = h(eᵘ)`, `h_H(eᵘ) = ∫ g(u − v) sin(Hv)/(πv) dv` is `g` with its Fourier transform cut
off at `|ξ| ≤ H/2π`. Hence `‖g − g_H‖₂² = ∫_{|ξ| > H/2π} |ĝ|² ≤ ‖g'‖₂²/H²` and
`‖η₊ − η◦‖₂² ≤ sup(s³e^{−s²}) ‖g − g_H‖₂²` ([H, (A.23)] proves `≤ 274.86²/H⁷` by a finer analysis;
we only need a crude bound).

This file: `g`, `g'` and `‖g'‖₂² = ∫₀² t h'(t)² dt ≤ 19.5`.
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (hBase hH F etaPlus sH hP hP' hasDerivAt_hP continuous_hP'
  hBase_eq_hP hP_two measurable_hBase)

/-- `h'`, extended by `0` beyond `2`. -/
noncomputable def hBd (t : ℝ) : ℝ := if t ≤ 2 then hP' t else 0

theorem hP'_two : hP' 2 = 0 := by unfold hP'; norm_num

theorem hBase_of_two_le {s : ℝ} (hs : 2 ≤ s) : hBase s = 0 := by
  unfold hBase
  split_ifs with hm
  · have : s = 2 := le_antisymm hm.2 hs
    subst this; norm_num
  · rfl

/-- `h` is differentiable on `(0, ∞)` (`C¹` across `t = 2`). -/
theorem hasDerivAt_hBase {t : ℝ} (ht : 0 < t) : HasDerivAt hBase (hBd t) t := by
  rcases lt_trichotomy t 2 with h | h | h
  · have : hBase =ᶠ[nhds t] hP := by
      filter_upwards [Ioo_mem_nhds ht h] with s hs using hBase_eq_hP hs.1.le hs.2.le
    rw [hBd, if_pos h.le]
    exact (hasDerivAt_hP t).congr_of_eventuallyEq this
  · subst h
    rw [hBd, if_pos le_rfl, hP'_two]
    have hl : HasDerivWithinAt hBase 0 (Iic 2) 2 := by
      have := (hasDerivAt_hP 2).hasDerivWithinAt (s := Iic 2)
      rw [hP'_two] at this
      refine this.congr_of_eventuallyEq ?_ (hBase_eq_hP (by norm_num) le_rfl)
      filter_upwards [inter_mem_nhdsWithin (Iic 2) (Ioi_mem_nhds (show (0:ℝ) < 2 by norm_num)),
        self_mem_nhdsWithin] with s hs hs'
      exact hBase_eq_hP hs.2.le hs'
    have hr : HasDerivWithinAt hBase 0 (Ici 2) 2 := by
      refine (hasDerivWithinAt_const (2:ℝ) (Ici 2) (0:ℝ)).congr_of_eventuallyEq ?_
        (hBase_of_two_le le_rfl)
      filter_upwards [self_mem_nhdsWithin] with s hs using hBase_of_two_le hs
    have := hl.union hr
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · have : hBase =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds h] with s hs using hBase_of_two_le hs.le
    rw [hBd, if_neg (not_le.2 h)]
    exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq this

/-- `g(u) = h(eᵘ)`. -/
noncomputable def gL (u : ℝ) : ℝ := hBase (Real.exp u)

/-- `g'(u) = eᵘ h'(eᵘ)`. -/
noncomputable def gL' (u : ℝ) : ℝ := hBd (Real.exp u) * Real.exp u

theorem hasDerivAt_gL (u : ℝ) : HasDerivAt gL (gL' u) u :=
  (hasDerivAt_hBase (Real.exp_pos u)).comp u (Real.hasDerivAt_exp u)

theorem measurable_hBd : Measurable hBd := by
  unfold hBd; exact Measurable.ite measurableSet_Iic (by unfold hP'; fun_prop) measurable_const

theorem measurable_gL : Measurable gL := measurable_hBase.comp Real.measurable_exp
theorem measurable_gL' : Measurable gL' := (measurable_hBd.comp Real.measurable_exp).mul Real.measurable_exp

/-- Integrability on `(0, ∞)` of a function agreeing there with `1_{[0,2]} k`, `k` continuous. -/
theorem integrableOn_Ioi_of_eq_indicator {G k : ℝ → ℝ} (hk : Continuous k)
    (h : ∀ t, 0 < t → G t = (Icc (0 : ℝ) 2).indicator k t) : IntegrableOn G (Ioi 0) := by
  have hi : Integrable ((Icc (0 : ℝ) 2).indicator k) :=
    (integrable_indicator_iff measurableSet_Icc).2 hk.integrableOn_Icc
  exact (hi.integrableOn (s := Ioi 0)).congr_fun (fun t ht => (h t ht).symm) measurableSet_Ioi

theorem hBase_div_eq {t : ℝ} (ht : 0 < t) :
    hBase t / t = (Icc (0 : ℝ) 2).indicator (fun t => t * (2 - t) ^ 3 * Real.exp (t - 1 / 2)) t := by
  by_cases h2 : t ≤ 2
  · rw [indicator_of_mem (show t ∈ Icc (0:ℝ) 2 from ⟨ht.le, h2⟩), hBase_eq_hP ht.le h2]; unfold hP; field_simp
  · rw [indicator_of_notMem (fun hm => h2 hm.2), hBase_of_two_le (le_of_not_ge h2), zero_div]

theorem hBd_eq {t : ℝ} (ht : 0 < t) : hBd t = (Icc (0 : ℝ) 2).indicator hP' t := by
  by_cases h2 : t ≤ 2
  · rw [indicator_of_mem (show t ∈ Icc (0:ℝ) 2 from ⟨ht.le, h2⟩), hBd, if_pos h2]
  · rw [indicator_of_notMem (fun hm => h2 hm.2), hBd, if_neg h2]

theorem hBase_sq_div_eq {t : ℝ} (ht : 0 < t) :
    hBase t ^ 2 / t =
      (Icc (0 : ℝ) 2).indicator (fun t => t ^ 3 * (2 - t) ^ 6 * Real.exp (t - 1 / 2) ^ 2) t := by
  by_cases h2 : t ≤ 2
  · rw [indicator_of_mem (show t ∈ Icc (0:ℝ) 2 from ⟨ht.le, h2⟩), hBase_eq_hP ht.le h2]; unfold hP; field_simp
  · rw [indicator_of_notMem (fun hm => h2 hm.2), hBase_of_two_le (le_of_not_ge h2)]; simp

theorem mul_hBd_sq_eq {t : ℝ} (ht : 0 < t) :
    t * hBd t ^ 2 = (Icc (0 : ℝ) 2).indicator (fun t => t * hP' t ^ 2) t := by
  rw [hBd_eq ht]
  by_cases h2 : t ∈ Icc (0 : ℝ) 2
  · rw [indicator_of_mem h2, indicator_of_mem h2]
  · rw [indicator_of_notMem h2, indicator_of_notMem h2]; ring

theorem integrable_gL : Integrable gL := by
  have : gL = fun u => Real.exp u • (hBase (Real.exp u) / Real.exp u) := by
    ext u; rw [smul_eq_mul, gL]; field_simp
  rw [this]
  exact (integrable_comp_exp (fun t => hBase t / t)).2
    (integrableOn_Ioi_of_eq_indicator (by fun_prop) fun t ht => hBase_div_eq ht)

theorem integrable_gL' : Integrable gL' := by
  have : gL' = fun u => Real.exp u • hBd (Real.exp u) := by
    ext u; rw [smul_eq_mul, gL', mul_comm]
  rw [this, integrable_comp_exp]
  exact integrableOn_Ioi_of_eq_indicator continuous_hP' fun t ht => hBd_eq ht

theorem integrable_gL_sq : Integrable fun u => gL u ^ 2 := by
  have : (fun u => gL u ^ 2) = fun u => Real.exp u • (hBase (Real.exp u) ^ 2 / Real.exp u) := by
    ext u; rw [smul_eq_mul, gL]; field_simp
  rw [this]
  exact (integrable_comp_exp (fun t => hBase t ^ 2 / t)).2
    (integrableOn_Ioi_of_eq_indicator (by fun_prop) fun t ht => hBase_sq_div_eq ht)

theorem integrable_gL'_sq : Integrable fun u => gL' u ^ 2 := by
  have : (fun u => gL' u ^ 2) = fun u => Real.exp u • (Real.exp u * hBd (Real.exp u) ^ 2) := by
    ext u; rw [smul_eq_mul, gL']; ring
  rw [this]
  exact (integrable_comp_exp (fun t => t * hBd t ^ 2)).2
    (integrableOn_Ioi_of_eq_indicator (by unfold hP'; fun_prop) fun t ht => mul_hBd_sq_eq ht)

/-! ## `‖g'‖₂² ≤ 19.5` -/

theorem hasDerivAt_A1 (t : ℝ) :
    HasDerivAt (fun t : ℝ => (64 / 1 : ℝ) * t ^ 4 + (-896 / 5 : ℝ) * t ^ 5 + (584 / 3 : ℝ) * t ^ 6 + (-640 / 7 : ℝ) * t ^ 7 + (7 / 1 : ℝ) * t ^ 8 + (80 / 9 : ℝ) * t ^ 9 + (-23 / 10 : ℝ) * t ^ 10 + (-2 / 11 : ℝ) * t ^ 11 + (1 / 12 : ℝ) * t ^ 12)
      (t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2) t := by
  exact ((((((((((hasDerivAt_pow 4 t).const_mul (64 / 1 : ℝ)).add ((hasDerivAt_pow 5 t).const_mul (-896 / 5 : ℝ))).add ((hasDerivAt_pow 6 t).const_mul (584 / 3 : ℝ))).add ((hasDerivAt_pow 7 t).const_mul (-640 / 7 : ℝ))).add ((hasDerivAt_pow 8 t).const_mul (7 / 1 : ℝ))).add ((hasDerivAt_pow 9 t).const_mul (80 / 9 : ℝ))).add ((hasDerivAt_pow 10 t).const_mul (-23 / 10 : ℝ))).add ((hasDerivAt_pow 11 t).const_mul (-2 / 11 : ℝ))).add ((hasDerivAt_pow 12 t).const_mul (1 / 12 : ℝ))).congr_deriv
    (by push_cast; ring)

theorem integral_A1 {a b : ℝ} :
    ∫ t in a..b, t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2 =
      ((64 / 1 : ℝ) * b ^ 4 + (-896 / 5 : ℝ) * b ^ 5 + (584 / 3 : ℝ) * b ^ 6 + (-640 / 7 : ℝ) * b ^ 7 +
        (7 / 1 : ℝ) * b ^ 8 + (80 / 9 : ℝ) * b ^ 9 + (-23 / 10 : ℝ) * b ^ 10 + (-2 / 11 : ℝ) * b ^ 11 +
        (1 / 12 : ℝ) * b ^ 12) -
      ((64 / 1 : ℝ) * a ^ 4 + (-896 / 5 : ℝ) * a ^ 5 + (584 / 3 : ℝ) * a ^ 6 + (-640 / 7 : ℝ) * a ^ 7 +
        (7 / 1 : ℝ) * a ^ 8 + (80 / 9 : ℝ) * a ^ 9 + (-23 / 10 : ℝ) * a ^ 10 + (-2 / 11 : ℝ) * a ^ 11 +
        (1 / 12 : ℝ) * a ^ 12) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_A1 t)
    ((by fun_prop : Continuous fun t : ℝ => t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2).intervalIntegrable _ _)

theorem mul_hP'_sq_eq (t : ℝ) :
    t * hP' t ^ 2 = Real.exp (2 * t - 1) * (t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2) := by
  unfold hP'
  rw [show 2 * t - 1 = (t - 1 / 2) + (t - 1 / 2) by ring, Real.exp_add]; ring

theorem integral_mul_hP'_sq_le_piece {a b c : ℝ} (hab : a ≤ b) (h0 : 0 ≤ a)
    (hc : ∀ t ∈ Icc a b, Real.exp (2 * t - 1) ≤ c) :
    ∫ t in a..b, t * hP' t ^ 2 ≤ c * ∫ t in a..b, t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab
    ((by unfold hP'; fun_prop : Continuous fun t => t * hP' t ^ 2).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ =>
      c * (t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2)).intervalIntegrable _ _) fun t ht => ?_
  rw [mul_hP'_sq_eq]
  have hp : 0 ≤ t ^ 3 * (2 - t) ^ 4 * (1 - t) ^ 2 * (4 + t) ^ 2 := by
    have : 0 ≤ t := le_trans h0 ht.1
    positivity
  exact mul_le_mul_of_nonneg_right (hc t ht) hp

/-- `∫₀² t h'(t)² dt ≤ 19.5` (true value `6.92…`). -/
theorem integral_mul_hP'_sq_le : ∫ t in (0:ℝ)..2, t * hP' t ^ 2 ≤ 19.5 := by
  have hc : Continuous fun t => t * hP' t ^ 2 := by unfold hP'; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have he1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have he3 : Real.exp 3 ≤ 20.1 := by
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; calc Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := by gcongr
      _ ≤ 20.1 := by norm_num
  have h1 := integral_mul_hP'_sq_le_piece (a := 0) (b := 1) (c := Real.exp 1) (by norm_num) le_rfl
    fun t ht => Real.exp_le_exp.2 (by linarith [ht.2])
  have h2 := integral_mul_hP'_sq_le_piece (a := 1) (b := 2) (c := Real.exp 3) (by norm_num)
    (by norm_num) fun t ht => Real.exp_le_exp.2 (by linarith [ht.2])
  rw [integral_A1] at h1 h2
  norm_num at h1 h2
  have he0 := Real.exp_pos 1
  nlinarith

/-- **`‖g'‖₂² ≤ 19.5`**. -/
theorem integral_gL'_sq_le : ∫ u, gL' u ^ 2 ≤ 19.5 := by
  have e1 : (fun u => gL' u ^ 2) = fun u => Real.exp u • (Real.exp u * hBd (Real.exp u) ^ 2) := by
    ext u; rw [smul_eq_mul, gL']; ring
  rw [e1, integral_comp_exp (fun t => t * hBd t ^ 2)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => mul_hBd_sq_eq ht)]
  rw [setIntegral_indicator measurableSet_Icc]
  have : Ioi (0 : ℝ) ∩ Icc 0 2 = Ioc 0 2 := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]; constructor
    · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1.le, h2⟩
  rw [this, ← intervalIntegral.integral_of_le (by norm_num)]
  exact integral_mul_hP'_sq_le

/-! ## `h_H(eᵘ) = ∫_{|ξ| ≤ H/2π} ĝ(ξ) e(ξu) dξ` -/

theorem ae_ne_zero_real : ∀ᵐ x : ℝ, x ≠ 0 := by
  rw [ae_iff]
  have : {a : ℝ | ¬a ≠ 0} = {0} := by ext a; simp
  rw [this]; exact measure_singleton 0

/-- `h_H(t) = ∫ g(log t − v) sin(Hv)/(πv) dv` (substitution `y = eᵛ`). -/
theorem hH_eq_conv {H t : ℝ} (hH0 : 0 < H) (ht : 0 < t) :
    hH H t = ∫ v, gL (Real.log t - v) * sH H v := by
  unfold hH
  have h := integral_comp_exp (fun y => hBase (t / y) * F H y / y)
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero_real] with x hx
  rw [smul_eq_mul, gL, Real.exp_sub, Real.exp_log ht, TernaryGoldbach.Helfgott.sH_eq hH0.ne' hx]
  unfold F
  rw [Real.log_exp]
  have := Real.exp_pos x
  field_simp

/-- `sin(Hv)/(πv) = ∫_{−H/2π}^{H/2π} e(ξv) dξ`. -/
theorem sH_eq_integral {H v : ℝ} (hH0 : 0 < H) (hv : v ≠ 0) :
    (sH H v : ℂ) = ∫ ξ in Icc (-(H / (2 * π))) (H / (2 * π)), Complex.exp (↑(2 * π * ξ * v) * I) := by
  have hπ := Real.pi_pos
  have ha : -(H / (2 * π)) ≤ H / (2 * π) := by
    have : 0 ≤ H / (2 * π) := by positivity
    linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
  have hc : (2 * π * v * I : ℂ) ≠ 0 := by
    have : (2 * π * v : ℂ) ≠ 0 := by
      have : (2 * π * v : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    exact mul_ne_zero this Complex.I_ne_zero
  have e0 : (fun ξ : ℝ => Complex.exp (↑(2 * π * ξ * v) * I)) =
      fun ξ : ℝ => Complex.exp ((2 * π * v * I) * ξ) := by
    ext ξ; push_cast; ring_nf
  rw [e0, integral_exp_mul_complex hc, TernaryGoldbach.Helfgott.sH_eq hH0.ne' hv]
  have e1 : (2 * π * v * I : ℂ) * ↑(H / (2 * π)) = ↑(H * v) * I := by
    push_cast; field_simp
  have e2 : (2 * π * v * I : ℂ) * ↑(-(H / (2 * π))) = (-(↑(H * v) : ℂ)) * I := by
    push_cast; field_simp
  rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_sin]
  push_cast
  field_simp
  ring

/-- `g` as a complex function. -/
noncomputable def gC (u : ℝ) : ℂ := (gL u : ℂ)

theorem integral_shift_char (L ξ : ℝ) :
    ∫ v, (gL (L - v) : ℂ) * Complex.exp (↑(2 * π * ξ * v) * I) =
      Complex.exp (↑(2 * π * ξ * L) * I) * 𝓕 gC ξ := by
  have h1 : (fun v : ℝ => (gL (L - v) : ℂ) * Complex.exp (↑(2 * π * ξ * v) * I)) =
      fun v => (fun u : ℝ => (gL u : ℂ) * Complex.exp (↑(2 * π * ξ * (L - u)) * I)) (L - v) := by
    ext v; simp only [sub_sub_cancel]
  rw [h1, integral_sub_left_eq_self
      (fun u : ℝ => (gL u : ℂ) * Complex.exp (↑(2 * π * ξ * (L - u)) * I)) volume L,
    Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  congr 1; ext u
  rw [smul_eq_mul, gC, mul_comm (gL u : ℂ), ← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- **Fubini**: `h_H(t) = ∫_{|ξ| ≤ H/2π} e(ξ log t) ĝ(ξ) dξ`. -/
theorem hH_eq_fourier {H t : ℝ} (hH0 : 0 < H) (ht : 0 < t) :
    (hH H t : ℂ) = ∫ ξ in Icc (-(H / (2 * π))) (H / (2 * π)),
      Complex.exp (↑(2 * π * ξ * Real.log t) * I) * 𝓕 gC ξ := by
  set a := H / (2 * π)
  set L := Real.log t
  rw [hH_eq_conv hH0 ht, ← integral_complex_ofReal]
  have step1 : ∫ v, ((gL (L - v) * sH H v : ℝ) : ℂ) =
      ∫ v, ∫ ξ in Icc (-a) a, (gL (L - v) : ℂ) * Complex.exp (↑(2 * π * ξ * v) * I) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_real] with v hv
    rw [integral_const_mul, ← sH_eq_integral hH0 hv]; push_cast; ring
  rw [step1, integral_integral_swap]
  · exact setIntegral_congr_fun measurableSet_Icc fun ξ _ => integral_shift_char L ξ
  · have hg : Integrable (fun v => ‖gL (L - v)‖) := (integrable_gL.comp_sub_left L).norm
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc (-a) a)) := integrable_const 1
    refine Integrable.mono' (hg.mul_prod h1) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      exact (Complex.measurable_ofReal.comp (measurable_gL.comp (measurable_const.sub measurable_fst))).mul
        (by fun_prop)
    · rcases p with ⟨v, ξ⟩
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real]
      exact le_rfl

/-- The cut-off `ĝ · 1_{[−H/2π, H/2π]}`. -/
noncomputable def Kc (H : ℝ) (ξ : ℝ) : ℂ := (Icc (-(H / (2 * π))) (H / (2 * π))).indicator (𝓕 gC) ξ

/-- `h_H(t) = (ĝ·1_{[−H/2π,H/2π]})^(−log t)`. -/
theorem hH_eq_fourier_K {H t : ℝ} (hH0 : 0 < H) (ht : 0 < t) :
    (hH H t : ℂ) = 𝓕 (Kc H) (-Real.log t) := by
  have hK : Kc H = (Icc (-(H / (2 * π))) (H / (2 * π))).indicator (𝓕 gC) := rfl
  rw [hH_eq_fourier hH0 ht, Real.fourier_real_eq_integral_exp_smul, hK,
    ← integral_indicator measurableSet_Icc]
  congr 1; ext ξ
  by_cases h : ξ ∈ Icc (-(H / (2 * π))) (H / (2 * π))
  · rw [indicator_of_mem h, indicator_of_mem h, smul_eq_mul]
    congr 3; push_cast; ring
  · rw [indicator_of_notMem h, indicator_of_notMem h, smul_zero]

/-! ## `‖g − g_H‖₂² = ∫_{|ξ| > H/2π} |ĝ|² ≤ ‖g'‖₂²/H²` -/

theorem integrable_gC : Integrable gC := integrable_gL.ofReal

theorem memLp_gC : MemLp gC 2 := by
  refine (memLp_two_iff_integrable_sq_norm integrable_gC.aestronglyMeasurable).2 ?_
  have : (fun u => ‖gC u‖ ^ 2) = fun u => gL u ^ 2 := by
    ext u; rw [gC, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [this]; exact integrable_gL_sq

theorem continuous_fourier_gC : Continuous (𝓕 gC) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) integrable_gC

theorem integrable_Kc (H : ℝ) : Integrable (Kc H) :=
  (integrable_indicator_iff measurableSet_Icc).2 continuous_fourier_gC.integrableOn_Icc

theorem memLp_Kc (H : ℝ) : MemLp (Kc H) 2 := by
  have hK : Kc H = (Icc (-(H / (2 * π))) (H / (2 * π))).indicator (𝓕 gC) := rfl
  rw [hK, memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  exact MemLp.of_bound (μ := volume.restrict (Icc (-(H / (2 * π))) (H / (2 * π))))
    continuous_fourier_gC.aestronglyMeasurable (∫ u, ‖gC u‖)
    (Filter.Eventually.of_forall fun ξ => Real.norm_fourier_le_integral_norm gC ξ)

theorem memLp_gH (H : ℝ) : MemLp (fun u => 𝓕 (Kc H) (-u)) 2 :=
  (TernaryGoldbach.memLp_fourier (integrable_Kc H) (memLp_Kc H)).comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem norm_sq_Kc (H ξ : ℝ) :
    ‖Kc H ξ‖ ^ 2 = (Icc (-(H / (2 * π))) (H / (2 * π))).indicator (fun ξ => ‖𝓕 gC ξ‖ ^ 2) ξ := by
  have hK : Kc H = (Icc (-(H / (2 * π))) (H / (2 * π))).indicator (𝓕 gC) := rfl
  rw [hK]
  by_cases h : ξ ∈ Icc (-(H / (2 * π))) (H / (2 * π))
  · rw [indicator_of_mem h, indicator_of_mem h]
  · rw [indicator_of_notMem h, indicator_of_notMem h]; simp

/-- The cross term `∫ g(u) conj(g_H(u)) du = ∫ conj(K(ξ)) ĝ(ξ) dξ`. -/
theorem integral_cross (H : ℝ) :
    ∫ u, gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u)) =
      ∫ ξ, (starRingEnd ℂ) (Kc H ξ) * 𝓕 gC ξ := by
  have e1 : ∀ u, (starRingEnd ℂ) (𝓕 (Kc H) (-u)) =
      ∫ ξ, Complex.exp (↑(-2 * π * u * ξ) * I) * (starRingEnd ℂ) (Kc H ξ) := by
    intro u
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
    congr 1; ext ξ
    rw [smul_eq_mul, map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2; push_cast; ring
  simp_rw [e1, ← integral_const_mul]
  rw [integral_integral_swap]
  · congr 1; ext ξ
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1; ext u; rw [smul_eq_mul]; ring
  · refine Integrable.mono' (integrable_gC.norm.mul_prod (integrable_Kc H).norm) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · have hK : Measurable (Kc H) :=
        continuous_fourier_gC.measurable.indicator measurableSet_Icc
      refine Measurable.aestronglyMeasurable ?_
      exact (Complex.measurable_ofReal.comp (measurable_gL.comp measurable_fst)).mul
        ((by fun_prop : Measurable fun p : ℝ × ℝ => Complex.exp (↑(-2 * π * p.1 * p.2) * I)).mul
          (Complex.continuous_conj.measurable.comp (hK.comp measurable_snd)))
    · rcases p with ⟨u, ξ⟩
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
        Complex.norm_conj]
      exact le_rfl

theorem continuous_fourier_Kc (H : ℝ) : Continuous (𝓕 (Kc H)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) (integrable_Kc H)

/-- **`‖g − g_H‖₂² = ∫_{|ξ| > H/2π} |ĝ|²`** (Plancherel for `g` and for `ĝ·1`, and the cross term). -/
theorem integral_norm_sq_gC_sub (H : ℝ) :
    ∫ u, ‖gC u - 𝓕 (Kc H) (-u)‖ ^ 2 =
      ∫ ξ in (Icc (-(H / (2 * π))) (H / (2 * π)))ᶜ, ‖𝓕 gC ξ‖ ^ 2 := by
  set S := Icc (-(H / (2 * π))) (H / (2 * π)) with hS
  have hA : Integrable fun u => ‖gC u‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm memLp_gC.aestronglyMeasurable).1 memLp_gC
  have hB : Integrable fun u => ‖𝓕 (Kc H) (-u)‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm (memLp_gH H).aestronglyMeasurable).1 (memLp_gH H)
  have hCi : Integrable fun u => gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u)) := by
    refine Integrable.mono' ((hA.add hB).div_const 2) ?_ (Filter.Eventually.of_forall fun u => ?_)
    · exact integrable_gC.aestronglyMeasurable.mul
        (Complex.continuous_conj.comp ((continuous_fourier_Kc H).comp continuous_neg)).aestronglyMeasurable
    · show ‖gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u))‖ ≤ (‖gC u‖ ^ 2 + ‖𝓕 (Kc H) (-u)‖ ^ 2) / 2
      rw [norm_mul, Complex.norm_conj]
      nlinarith [sq_nonneg (‖gC u‖ - ‖𝓕 (Kc H) (-u)‖)]
  have hpt : ∀ u, ‖gC u - 𝓕 (Kc H) (-u)‖ ^ 2 = ‖gC u‖ ^ 2 + ‖𝓕 (Kc H) (-u)‖ ^ 2 -
      2 * (gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u))).re := by
    intro u; rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
  simp_rw [hpt]
  have hAB : Integrable fun u => ‖gC u‖ ^ 2 + ‖𝓕 (Kc H) (-u)‖ ^ 2 := hA.add hB
  have hC2 : Integrable fun u => 2 * (gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u))).re :=
    hCi.re.const_mul 2
  have hre : ∫ u, (gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u))).re =
      (∫ u, gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u))).re := integral_re hCi
  rw [integral_sub hAB hC2, integral_add hA hB, integral_const_mul, hre]
  have hFgC := TernaryGoldbach.memLp_fourier integrable_gC memLp_gC
  have hFint : Integrable fun ξ => ‖𝓕 gC ξ‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hFgC.aestronglyMeasurable).1 hFgC
  have eA : ∫ u, ‖gC u‖ ^ 2 = ∫ ξ, ‖𝓕 gC ξ‖ ^ 2 :=
    (TernaryGoldbach.integral_norm_sq_fourier integrable_gC memLp_gC).symm
  have eB : ∫ u, ‖𝓕 (Kc H) (-u)‖ ^ 2 = ∫ ξ in S, ‖𝓕 gC ξ‖ ^ 2 := by
    rw [integral_neg_eq_self (fun w => ‖𝓕 (Kc H) w‖ ^ 2) volume,
      TernaryGoldbach.integral_norm_sq_fourier (integrable_Kc H) (memLp_Kc H)]
    simp_rw [norm_sq_Kc]
    rw [integral_indicator measurableSet_Icc]
  have eC : (∫ u, gC u * (starRingEnd ℂ) (𝓕 (Kc H) (-u))).re = ∫ ξ in S, ‖𝓕 gC ξ‖ ^ 2 := by
    rw [integral_cross]
    have : (fun ξ => (starRingEnd ℂ) (Kc H ξ) * 𝓕 gC ξ) =
        fun ξ => ((S.indicator (fun ξ => ‖𝓕 gC ξ‖ ^ 2) ξ : ℝ) : ℂ) := by
      ext ξ
      have hK : Kc H = S.indicator (𝓕 gC) := rfl
      rw [hK]
      by_cases h : ξ ∈ S
      · rw [indicator_of_mem h, indicator_of_mem h, Complex.conj_mul']; push_cast; ring
      · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
    rw [this, integral_complex_ofReal, Complex.ofReal_re, integral_indicator measurableSet_Icc]
  rw [eA, eB, eC]
  have := integral_add_compl (s := S) measurableSet_Icc hFint
  linarith

theorem differentiable_gC : Differentiable ℝ gC :=
  fun u => ((hasDerivAt_gL u).ofReal_comp).differentiableAt

theorem deriv_gC : deriv gC = fun u => (gL' u : ℂ) := by
  ext u; exact ((hasDerivAt_gL u).ofReal_comp).deriv

/-- **`∫_{|ξ| > H/2π} |ĝ|² ≤ ‖g'‖₂²/H² ≤ 19.5/H²`**. -/
theorem tail_fourier_gC_le {H : ℝ} (hH0 : 0 < H) :
    ∫ ξ in (Icc (-(H / (2 * π))) (H / (2 * π)))ᶜ, ‖𝓕 gC ξ‖ ^ 2 ≤ 19.5 / H ^ 2 := by
  set S := Icc (-(H / (2 * π))) (H / (2 * π)) with hS
  have hπ := Real.pi_pos
  set g'C : ℝ → ℂ := fun u => (gL' u : ℂ) with hg'C
  have hint' : Integrable g'C := integrable_gL'.ofReal
  have hL2' : MemLp g'C 2 := by
    refine (memLp_two_iff_integrable_sq_norm hint'.aestronglyMeasurable).2 ?_
    have : (fun u => ‖g'C u‖ ^ 2) = fun u => gL' u ^ 2 := by
      ext u; rw [hg'C, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [this]; exact integrable_gL'_sq
  have hfd := Real.fourier_deriv integrable_gC differentiable_gC (by rw [deriv_gC]; exact hint')
  rw [deriv_gC] at hfd
  have hF' := TernaryGoldbach.memLp_fourier hint' hL2'
  have hint2 : Integrable fun ξ => ‖𝓕 g'C ξ‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hF'.aestronglyMeasurable).1 hF'
  have hpl := TernaryGoldbach.integral_norm_sq_fourier hint' hL2'
  have hle : ∀ ξ ∈ Sᶜ, ‖𝓕 gC ξ‖ ^ 2 ≤ ‖𝓕 g'C ξ‖ ^ 2 / H ^ 2 := by
    intro ξ hξ
    have h1 : H ≤ 2 * π * |ξ| := by
      simp only [hS, mem_compl_iff, mem_Icc, not_and_or, not_le] at hξ
      have : H / (2 * π) ≤ |ξ| := by
        rcases hξ with h | h
        · have h0 : 0 ≤ H / (2 * π) := by positivity
          have hneg : ξ < 0 := by linarith
          rw [abs_of_neg hneg]; linarith
        · exact h.le.trans (le_abs_self ξ)
      rw [div_le_iff₀ (by positivity)] at this; linarith
    have e : 𝓕 g'C ξ = (2 * π * I * ξ) • 𝓕 gC ξ := congrFun hfd ξ
    rw [e, smul_eq_mul, norm_mul, mul_pow, le_div_iff₀ (by positivity)]
    have hn : ‖(2 * π * I * ξ : ℂ)‖ = 2 * π * |ξ| := by
      rw [show (2 * π * I * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) * I by push_cast; ring, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos hπ]
      norm_num
    rw [hn]
    have : H ^ 2 ≤ (2 * π * |ξ|) ^ 2 := pow_le_pow_left₀ hH0.le h1 2
    nlinarith [sq_nonneg ‖𝓕 gC ξ‖]
  have hmeas : MeasurableSet Sᶜ := measurableSet_Icc.compl
  calc ∫ ξ in Sᶜ, ‖𝓕 gC ξ‖ ^ 2 ≤ ∫ ξ in Sᶜ, ‖𝓕 g'C ξ‖ ^ 2 / H ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          (hint2.div_const _).integrableOn ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hle))
    _ ≤ ∫ ξ, ‖𝓕 g'C ξ‖ ^ 2 / H ^ 2 :=
        setIntegral_le_integral (hint2.div_const _) (Filter.Eventually.of_forall fun _ => by positivity)
    _ = (∫ u, ‖g'C u‖ ^ 2) / H ^ 2 := by rw [integral_div, hpl]
    _ ≤ 19.5 / H ^ 2 := by
        gcongr
        have : (fun u => ‖g'C u‖ ^ 2) = fun u => gL' u ^ 2 := by
          ext u; rw [hg'C, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        rw [this]; exact integral_gL'_sq_le

/-! ## `‖η₊ − η◦‖₂² ≤ 19.5/(2·200²)` and regularity of `η₊`, `η◦` -/

theorem hH_of_neg {H t : ℝ} (ht : t < 0) : hH H t = 0 := by
  unfold hH
  refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have : t / y < 0 := div_neg_of_neg_of_pos ht hy0
  have h0 : hBase (t / y) = 0 := by
    unfold hBase; rw [if_neg]; intro h; linarith [h.1]
  rw [h0]; ring

theorem etaPlus_of_nonpos {t : ℝ} (ht : t ≤ 0) : etaPlus t = 0 := by
  rcases ht.lt_or_eq with h | h
  · rw [etaPlus, hH_of_neg h]; ring
  · rw [etaPlus, h]; ring

theorem etaO_of_nonpos {t : ℝ} (ht : t ≤ 0) : etaO t = 0 := by
  rcases ht.lt_or_eq with h | h
  · rw [etaO, indicator_of_notMem]; intro hm; linarith [hm.1]
  · rw [etaO, h, indicator_of_mem (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 2), P0_zero]

theorem etaO_eq {t : ℝ} (ht : 0 < t) : etaO t = hBase t * t * Real.exp (-t ^ 2 / 2) := by
  by_cases h2 : t ≤ 2
  · rw [etaO, indicator_of_mem (show t ∈ Icc (0:ℝ) 2 from ⟨ht.le, h2⟩), hBase_eq_hP ht.le h2]
    unfold P0 hP
    rw [show -(t - 1) ^ 2 / 2 = (t - 1 / 2) + (-t ^ 2 / 2) by ring, Real.exp_add]; ring
  · rw [etaO, indicator_of_notMem (fun hm => h2 hm.2), hBase_of_two_le (le_of_not_ge h2)]; ring

theorem cube_mul_exp_neg_sq_le {s : ℝ} (hs : 0 ≤ s) : s ^ 3 * Real.exp (-s ^ 2) ≤ 1 / 2 := by
  have h := Real.sum_le_exp_of_nonneg (sq_nonneg s) 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one,
    zero_add, div_one] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [mul_nonneg (sq_nonneg (s ^ 2 - 2)) (by positivity : (0:ℝ) ≤ s ^ 2 + 1),
    sq_nonneg (s - s ^ 2)]

/-- **[H, (A.23)]-type bound** (crude): `‖η₊ − η◦‖₂² ≤ 19.5/(2·200²)`. -/
theorem integral_sq_etaPlus_sub_etaO_le :
    ∫ t, (etaPlus t - etaO t) ^ 2 ≤ 19.5 / 2 / 200 ^ 2 := by
  have hz : ∀ t ∉ Ioi (0:ℝ), (etaPlus t - etaO t) ^ 2 = 0 := fun t ht => by
    rw [etaPlus_of_nonpos (not_lt.1 ht), etaO_of_nonpos (not_lt.1 ht)]; ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    ← integral_comp_exp (fun t => (etaPlus t - etaO t) ^ 2)]
  have hpt : ∀ u, Real.exp u • (etaPlus (Real.exp u) - etaO (Real.exp u)) ^ 2 =
      ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 * (Real.exp u ^ 3 * Real.exp (-(Real.exp u) ^ 2)) := by
    intro u
    have he := Real.exp_pos u
    have hK := hH_eq_fourier_K (H := 200) (by norm_num) he
    rw [Real.log_exp] at hK
    rw [← hK, gC, gL, smul_eq_mul, etaPlus, etaO_eq he, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, sq_abs,
      show -(Real.exp u) ^ 2 = (-(Real.exp u) ^ 2 / 2) + (-(Real.exp u) ^ 2 / 2) by ring, Real.exp_add]
    ring
  simp_rw [hpt]
  have hL2 := memLp_gC.sub (memLp_gH 200)
  have hint : Integrable fun u => ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  calc ∫ u, ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 * (Real.exp u ^ 3 * Real.exp (-(Real.exp u) ^ 2))
      ≤ ∫ u, ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2 * (1 / 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by positivity)
          (hint.mul_const _) (Filter.Eventually.of_forall fun u =>
            mul_le_mul_of_nonneg_left (cube_mul_exp_neg_sq_le (Real.exp_pos u).le) (sq_nonneg _))
    _ = (∫ u, ‖gC u - 𝓕 (Kc 200) (-u)‖ ^ 2) * (1 / 2) := integral_mul_const _ _
    _ ≤ 19.5 / 2 / 200 ^ 2 := by
        rw [integral_norm_sq_gC_sub]
        have := tail_fourier_gC_le (H := 200) (by norm_num)
        linarith

theorem etaPlus_eq_indicator (t : ℝ) :
    etaPlus t = (Ioi 0).indicator
      (fun t => (𝓕 (Kc 200) (-Real.log t)).re * t * Real.exp (-t ^ 2 / 2)) t := by
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht), ← hH_eq_fourier_K (by norm_num) ht,
      Complex.ofReal_re, etaPlus]
  · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht), etaPlus_of_nonpos (not_lt.1 ht)]

theorem measurable_etaPlus : Measurable etaPlus := by
  have : etaPlus = (Ioi 0).indicator
      (fun t => (𝓕 (Kc 200) (-Real.log t)).re * t * Real.exp (-t ^ 2 / 2)) := funext etaPlus_eq_indicator
  rw [this]
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact ((Complex.measurable_re.comp ((continuous_fourier_Kc 200).measurable.comp
    (measurable_neg.comp Real.measurable_log))).mul measurable_id).mul (by fun_prop)

theorem abs_etaPlus_le_gauss (t : ℝ) : |etaPlus t| ≤ 3.15 * |t * Real.exp (-(1 / 2) * t ^ 2)| := by
  rcases le_or_gt t 0 with ht | ht
  · rw [etaPlus_of_nonpos ht, abs_zero]; positivity
  · rw [etaPlus, abs_mul, abs_mul, show -(1 / 2) * t ^ 2 = -t ^ 2 / 2 by ring, abs_mul, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (TernaryGoldbach.Helfgott.abs_hH200_le ht.le) (abs_nonneg _))
      (abs_nonneg _)

theorem integrable_etaPlus : Integrable etaPlus :=
  Integrable.mono' ((integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).norm.const_mul 3.15)
    measurable_etaPlus.aestronglyMeasurable (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_etaPlus_le_gauss t)

theorem memLp_etaPlus : MemLp etaPlus 2 := by
  refine (memLp_two_iff_integrable_sq_norm measurable_etaPlus.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (integrable_etaPlus.norm.const_mul 1.94)
    (measurable_etaPlus.norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq]
  have h1 : |etaPlus t| ≤ 1.94 := by
    rcases le_or_gt t 0 with ht | ht
    · rw [etaPlus_of_nonpos ht, abs_zero]; norm_num
    · exact TernaryGoldbach.Helfgott.abs_etaPlus_le_A ht.le
  exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem measurable_etaO : Measurable etaO := continuous_P0.measurable.indicator measurableSet_Icc

theorem integrable_etaO : Integrable etaO :=
  (integrable_indicator_iff measurableSet_Icc).2 continuous_P0.integrableOn_Icc

theorem memLp_etaO : MemLp etaO 2 := by
  have hK : etaO = (Icc (0 : ℝ) 2).indicator P0 := rfl
  rw [hK, memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2)).exists_bound_of_continuousOn
    continuous_P0.continuousOn
  exact MemLp.of_bound (μ := volume.restrict (Icc (0 : ℝ) 2)) continuous_P0.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hC))

end TernaryGoldbach.MajorArcs
