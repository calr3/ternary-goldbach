import TernaryGoldbach.Prelim.PlancherelReal

/-!
# The approximation `η◦` and the tail of its Fourier transform

`η◦(t) = h(t) t e^{-t²/2} = t³(2 - t)³ e^{t - 1/2 - t²/2}` on `[0, 2]` ([H, (11.3)]), i.e.
`(t(2 - t))³ e^{-(t-1)²/2}`. It is `C²` with `η◦ = η◦' = 0` at `0` and `2`, so two integrations by
parts give `η̂◦(ξ) = (2πiξ)⁻² (η◦''·1_{[0,2]})^(ξ)`, and Plancherel with `|η◦''| ≤ 7` gives
`∫_{|ξ| ≥ T} |η̂◦(ξ)|² dξ ≤ 98/(2πT)⁴`.
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)

namespace TernaryGoldbach.MajorArcs

/-- `η◦` on `[0, 2]`: `(t(2 - t))³ e^{-(t-1)²/2}`. -/
noncomputable def P0 (t : ℝ) : ℝ := (t * (2 - t)) ^ 3 * Real.exp (-(t - 1) ^ 2 / 2)

/-- `P0'`. -/
noncomputable def P1 (t : ℝ) : ℝ :=
  -(t - 1) * (t * (2 - t)) ^ 2 * (7 - (t - 1) ^ 2) * Real.exp (-(t - 1) ^ 2 / 2)

/-- `P0'' = Q₂((t-1)²) e^{-(t-1)²/2}`. -/
noncomputable def Q2 (v : ℝ) : ℝ := -7 + 52 * v - 60 * v ^ 2 + 16 * v ^ 3 - v ^ 4

noncomputable def P2 (t : ℝ) : ℝ := Q2 ((t - 1) ^ 2) * Real.exp (-(t - 1) ^ 2 / 2)

/-- **`η◦`** ([H, (11.3)]): `t³(2 - t)³ e^{t - 1/2 - t²/2}` on `[0, 2]`, `0` elsewhere. -/
noncomputable def etaO (t : ℝ) : ℝ := (Icc (0 : ℝ) 2).indicator P0 t

theorem hasDerivAt_gauss1 (t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t - 1) ^ 2 / 2))
      (Real.exp (-(t - 1) ^ 2 / 2) * (-(t - 1))) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(t - 1) ^ 2 / 2) (-(t - 1)) t :=
    ((((hasDerivAt_id' t).sub_const 1).pow 2).neg.div_const 2).congr_deriv (by push_cast; ring)
  exact h1.exp

theorem hasDerivAt_P0 (t : ℝ) : HasDerivAt P0 (P1 t) t := by
  have h1 : HasDerivAt (fun t : ℝ => (t * (2 - t)) ^ 3) (3 * (t * (2 - t)) ^ 2 * (2 - 2 * t)) t :=
    (((hasDerivAt_id' t).mul ((hasDerivAt_const t (2:ℝ)).sub (hasDerivAt_id' t))).pow 3).congr_deriv
      (by simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply]; push_cast; ring)
  unfold P0 P1
  exact (h1.mul (hasDerivAt_gauss1 t)).congr_deriv (by ring)

theorem hasDerivAt_P1 (t : ℝ) : HasDerivAt P1 (P2 t) t := by
  have a := ((hasDerivAt_id' t).sub_const 1).neg
  have b := ((hasDerivAt_id' t).mul ((hasDerivAt_const t (2:ℝ)).sub (hasDerivAt_id' t))).pow 2
  have c := (hasDerivAt_const t (7:ℝ)).sub (((hasDerivAt_id' t).sub_const 1).pow 2)
  unfold P1 P2 Q2
  exact (((a.mul b).mul c).mul (hasDerivAt_gauss1 t)).congr_deriv
    (by simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.neg_apply]; push_cast; ring)

theorem continuous_P0 : Continuous P0 := by unfold P0; fun_prop
theorem continuous_P1 : Continuous P1 := by unfold P1; fun_prop
theorem continuous_P2 : Continuous P2 := by unfold P2 Q2; fun_prop

theorem P0_zero : P0 0 = 0 := by simp [P0]
theorem P0_two : P0 2 = 0 := by simp [P0]
theorem P1_zero : P1 0 = 0 := by simp [P1]
theorem P1_two : P1 2 = 0 := by simp [P1]

theorem abs_Q2_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : |Q2 v| ≤ 7 := by
  unfold Q2
  rw [abs_le]; constructor
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1),
      mul_nonneg (mul_nonneg (mul_nonneg h0 h0) h0) (sub_nonneg.2 h1)]
  · nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1),
      sq_nonneg (v - 0.55), mul_nonneg (sq_nonneg (v - 0.55)) h0,
      mul_nonneg (sq_nonneg (v - 0.55)) (sub_nonneg.2 h1)]

theorem abs_P2_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) : |P2 t| ≤ 7 := by
  obtain ⟨h0, h2⟩ := ht
  have hv0 : 0 ≤ (t - 1) ^ 2 := sq_nonneg _
  have hv1 : (t - 1) ^ 2 ≤ 1 := by nlinarith
  unfold P2
  rw [abs_mul, Real.abs_exp]
  have he : Real.exp (-(t - 1) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  calc |Q2 ((t - 1) ^ 2)| * Real.exp (-(t - 1) ^ 2 / 2) ≤ 7 * 1 :=
        mul_le_mul (abs_Q2_le hv0 hv1) he (Real.exp_pos _).le (by norm_num)
    _ = 7 := by ring

/-! ## Integration by parts against `e(-ξt)` -/

theorem hasDerivAt_cexp_fourier (ξ t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (↑(-2 * π * t * ξ) * I))
      (Complex.exp (↑(-2 * π * t * ξ) * I) * (↑(-2 * π * ξ) * I)) t := by
  have h : HasDerivAt (fun t : ℝ => (↑(-2 * π * t * ξ) : ℂ) * I) (↑(-2 * π * ξ) * I) t := by
    exact ((((hasDerivAt_id' t).const_mul (-2 * π)).mul_const ξ).ofReal_comp.mul_const I).congr_deriv
      (by push_cast; ring)
  exact h.cexp

/-- One integration by parts against `e(-ξt)` on `[a, b]` when `f(a) = f(b) = 0`. -/
theorem ibp_fourier {f f' : ℝ → ℝ} {a b ξ : ℝ} (hξ : ξ ≠ 0) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (ha : f a = 0) (hb : f b = 0) :
    ∫ t in a..b, Complex.exp (↑(-2 * π * t * ξ) * I) * (f t : ℂ) =
      (1 / (2 * π * ξ * I)) * ∫ t in a..b, Complex.exp (↑(-2 * π * t * ξ) * I) * (f' t : ℂ) := by
  set c : ℂ := ↑(-2 * π * ξ) * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine mul_ne_zero (Complex.ofReal_ne_zero.2 ?_) Complex.I_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := fun t => (f t : ℂ)) (u' := fun t => (f' t : ℂ))
    (v := fun t => Complex.exp (↑(-2 * π * t * ξ) * I) / c)
    (v' := fun t => Complex.exp (↑(-2 * π * t * ξ) * I))
    (fun t _ => (hf t).ofReal_comp)
    (fun t _ => by
      have := (hasDerivAt_cexp_fourier ξ t).div_const c
      convert this using 1; rw [← hc]; field_simp)
    ((Complex.continuous_ofReal.comp hf').intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (↑(-2 * π * t * ξ) * I)).intervalIntegrable _ _)
  simp only [ha, hb, Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at key
  calc ∫ t in a..b, Complex.exp (↑(-2 * π * t * ξ) * I) * (f t : ℂ)
      = ∫ t in a..b, (f t : ℂ) * Complex.exp (↑(-2 * π * t * ξ) * I) := by
        congr 1; ext t; ring
    _ = -∫ t in a..b, (f' t : ℂ) * (Complex.exp (↑(-2 * π * t * ξ) * I) / c) := key
    _ = -((1 / c) * ∫ t in a..b, Complex.exp (↑(-2 * π * t * ξ) * I) * (f' t : ℂ)) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1; congr 1; ext t; field_simp
    _ = (1 / (2 * π * ξ * I)) * ∫ t in a..b, Complex.exp (↑(-2 * π * t * ξ) * I) * (f' t : ℂ) := by
        rw [hc]; push_cast
        have : (2 * (π : ℂ) * ξ * I) ≠ 0 := by
          have h2 : (-2 * (π : ℂ) * ξ * I) ≠ 0 := by
            have := hc0; rw [hc] at this; push_cast at this; exact this
          intro h; apply h2; linear_combination -h
        field_simp


/-! ## The Fourier transform of `η◦` -/

/-- `η̂` of a function supported on `[0, 2]` as an interval integral. -/
theorem fourier_indicator_Icc {f : ℝ → ℝ} (ξ : ℝ) :
    𝓕 (fun t => (((Icc (0 : ℝ) 2).indicator f t : ℝ) : ℂ)) ξ =
      ∫ t in (0 : ℝ)..2, Complex.exp (↑(-2 * π * t * ξ) * I) * (f t : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, intervalIntegral.integral_of_le (by norm_num),
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  congr 1; ext t
  by_cases ht : t ∈ Icc (0 : ℝ) 2
  · simp [indicator_of_mem ht, smul_eq_mul, mul_comm]
  · simp [indicator_of_notMem ht]

/-- **Two integrations by parts**: `η̂◦(ξ) = -(2πξ)⁻² (η◦''·1_{[0,2]})^(ξ)`. -/
theorem fourier_etaO_eq {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 (fun t => (etaO t : ℂ)) ξ =
      (1 / (2 * π * ξ * I)) ^ 2 * 𝓕 (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) ξ := by
  unfold etaO
  rw [fourier_indicator_Icc, fourier_indicator_Icc,
    ibp_fourier hξ hasDerivAt_P0 continuous_P1 P0_zero P0_two,
    ibp_fourier hξ hasDerivAt_P1 continuous_P2 P1_zero P1_two]
  ring

theorem norm_fourier_etaO_eq {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (fun t => (etaO t : ℂ)) ξ‖ =
      ‖𝓕 (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) ξ‖ / (2 * π * |ξ|) ^ 2 := by
  rw [fourier_etaO_eq hξ, norm_mul, norm_pow, norm_div, norm_one]
  have : ‖(2 * π * ξ * I : ℂ)‖ = 2 * π * |ξ| := by
    rw [norm_mul, Complex.norm_I, mul_one]
    have : (2 * π * ξ : ℂ) = ((2 * π * ξ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  rw [this]; field_simp

theorem integrable_indicator_P2 :
    Integrable (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) := by
  have : (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) =
      (Icc (0 : ℝ) 2).indicator (fun t => (P2 t : ℂ)) := by
    ext t; by_cases ht : t ∈ Icc (0 : ℝ) 2 <;> simp [ht]
  rw [this, integrable_indicator_iff measurableSet_Icc]
  exact (Complex.continuous_ofReal.comp continuous_P2).integrableOn_Icc

theorem memLp_indicator_P2 :
    MemLp (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) 2 := by
  have : (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) =
      (Icc (0 : ℝ) 2).indicator (fun t => (P2 t : ℂ)) := by
    ext t; by_cases ht : t ∈ Icc (0 : ℝ) 2 <;> simp [ht]
  rw [this, memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet]
  have hc : Continuous fun t => (P2 t : ℂ) := Complex.continuous_ofReal.comp continuous_P2
  refine MemLp.of_bound (μ := volume.restrict (Icc (0 : ℝ) 2)) hc.aestronglyMeasurable 7 ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_P2_le ht

theorem integral_norm_sq_indicator_P2_le :
    ∫ t, ‖(((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)‖ ^ 2 ≤ 98 := by
  have : (fun t => ‖(((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)‖ ^ 2) =
      (Icc (0 : ℝ) 2).indicator (fun t => P2 t ^ 2) := by
    ext t; by_cases ht : t ∈ Icc (0 : ℝ) 2 <;> simp [ht, Complex.norm_real]
  rw [this, integral_indicator measurableSet_Icc]
  calc ∫ t in Icc (0 : ℝ) 2, P2 t ^ 2 ≤ ∫ t in Icc (0 : ℝ) 2, (49 : ℝ) := by
        refine setIntegral_mono_on ((continuous_P2.pow 2).integrableOn_Icc) (by simp)
          measurableSet_Icc fun t ht => ?_
        have := abs_P2_le ht
        nlinarith [abs_nonneg (P2 t), sq_abs (P2 t)]
    _ = 98 := by simp; norm_num

/-- **The tail of `η̂◦`**: `∫_{|ξ| ≥ T} |η̂◦(ξ)|² dξ ≤ 98/(2πT)⁴`. -/
theorem tail_etaO_le {T : ℝ} (hT : 0 < T) :
    ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 (fun t => (etaO t : ℂ)) ξ‖ ^ 2 ≤ 98 / (2 * π * T) ^ 4 := by
  set F2 := fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)
  have hπ := Real.pi_pos
  have hmeas : MeasurableSet {ξ : ℝ | T ≤ |ξ|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hFL2 := TernaryGoldbach.memLp_fourier integrable_indicator_P2 memLp_indicator_P2
  have hint : Integrable (fun ξ => ‖𝓕 F2 ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFL2.aestronglyMeasurable).1 hFL2
  have hpl := TernaryGoldbach.integral_norm_sq_fourier integrable_indicator_P2 memLp_indicator_P2
  have hc : 0 < (2 * π * T) ^ 4 := by positivity
  calc ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 (fun t => (etaO t : ℂ)) ξ‖ ^ 2
      ≤ ∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 F2 ξ‖ ^ 2 / (2 * π * T) ^ 4 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
          (hint.div_const _).integrableOn ?_
        refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun ξ hξ => ?_)
        have hξ0 : ξ ≠ 0 := by
          intro h; simp only [mem_ofPred_eq, h, abs_zero] at hξ; linarith
        dsimp only
        rw [norm_fourier_etaO_eq hξ0, div_pow, ← pow_mul]
        have h1 : (2 * π * T) ^ 4 ≤ (2 * π * |ξ|) ^ (2 * 2) := by
          have : 2 * π * T ≤ 2 * π * |ξ| := by
            have := hξ; simp only [mem_ofPred_eq] at this; nlinarith
          exact pow_le_pow_left₀ (by positivity) this 4
        exact div_le_div_of_nonneg_left (by positivity) hc h1
    _ = (∫ ξ in {ξ : ℝ | T ≤ |ξ|}, ‖𝓕 F2 ξ‖ ^ 2) / (2 * π * T) ^ 4 := integral_div _ _
    _ ≤ (∫ ξ, ‖𝓕 F2 ξ‖ ^ 2) / (2 * π * T) ^ 4 :=
        div_le_div_of_nonneg_right
          (setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => by positivity)) hc.le
    _ ≤ 98 / (2 * π * T) ^ 4 := by
        gcongr
        rw [hpl]; exact integral_norm_sq_indicator_P2_le

end TernaryGoldbach.MajorArcs
