import TernaryGoldbach.MajorArcs.CMain

/-!
# [H, (10.22)]: `∫ η̂◦(t)² η̂_*(t) e(tM) dt = C_{η◦,η_*}(M)`

With `F = (η◦ ⋆ η◦) ⋆ η_*`: `F` is integrable and continuous, `𝓕 F = (𝓕 η◦)² 𝓕 η_*`
(`Real.fourier_mul_convolution_eq`), `𝓕 F` is integrable (`|η̂◦(ξ)| ≤ min(2, 14/(2πξ)²)`), so Fourier
inversion at `M` gives the identity; `F(M) = C_{η◦,η_*}(M)` by a change of variables.
-/

open Real MeasureTheory FourierTransform Set
open Complex (I)
open scoped Convolution

namespace TernaryGoldbach.MajorArcs

open TernaryGoldbach.Helfgott (κ)
open TernaryGoldbach.MinorArcs (etaU)

theorem continuous_etaO : Continuous etaO := by
  have : etaO = fun t => P0 (max 0 (min t 2)) := funext etaO_eq_clamp
  rw [this]
  exact continuous_P0.comp (continuous_const.max (continuous_id.min continuous_const))

/-- `η_*` (on the Fourier side) as a complex function. -/
noncomputable def etaSC (σ : ℝ) : ℂ := (etaS σ : ℂ)

theorem integrable_etaSC : Integrable etaSC := integrable_etaS.ofReal

theorem continuous_etaOC : Continuous etaOC := Complex.continuous_ofReal.comp continuous_etaO

theorem hasCompactSupport_etaOC : HasCompactSupport etaOC :=
  HasCompactSupport.intro (isCompact_Icc (a := (0:ℝ)) (b := 2)) fun t ht => by
    simp only [etaOC, etaO_eq_zero_of_notMem ht, Complex.ofReal_zero]

/-- `η◦ ⋆ η◦` (complex). -/
noncomputable def OO : ℝ → ℂ := etaOC ⋆[ContinuousLinearMap.mul ℂ ℂ] etaOC

theorem OO_apply (ρ : ℝ) : OO ρ = (conv2 ρ : ℂ) := by
  unfold OO conv2
  rw [convolution_mul, ← integral_complex_ofReal]
  congr 1; ext t; simp only [etaOC]; push_cast; ring

theorem continuous_OO : Continuous OO :=
  hasCompactSupport_etaOC.continuous_convolution_left _ continuous_etaOC
    integrable_etaOC.locallyIntegrable

theorem integrable_OO : Integrable OO := integrable_etaOC.integrable_convolution _ integrable_etaOC

/-- `F = (η◦ ⋆ η◦) ⋆ η_*`. -/
noncomputable def FM : ℝ → ℂ := OO ⋆[ContinuousLinearMap.mul ℂ ℂ] etaSC

theorem integrable_FM : Integrable FM := integrable_OO.integrable_convolution _ integrable_etaSC

theorem continuous_FM : Continuous FM := by
  refine BddAbove.continuous_convolution_left_of_integrable _ ?_ continuous_OO integrable_etaSC
  refine ⟨2, ?_⟩
  rintro _ ⟨ρ, rfl⟩
  simp only [OO_apply, Complex.norm_real, Real.norm_eq_abs]
  exact abs_conv2_le ρ

theorem FM_apply (M : ℝ) : FM M = (Cmain M : ℂ) := by
  unfold FM Cmain
  rw [convolution_mul, ← integral_complex_ofReal]
  rw [← integral_sub_left_eq_self (fun σ => ((conv2 (M - σ) * etaS σ : ℝ) : ℂ)) volume M]
  congr 1; ext t
  simp only [OO_apply, etaSC, sub_sub_cancel]; push_cast; ring

theorem fourier_FM (ξ : ℝ) : 𝓕 FM ξ = 𝓕 etaOC ξ * 𝓕 etaOC ξ * 𝓕 etaSC ξ := by
  unfold FM
  rw [Real.fourier_mul_convolution_eq integrable_OO integrable_etaSC]
  unfold OO
  rw [Real.fourier_mul_convolution_eq integrable_etaOC integrable_etaOC]

theorem norm_fourier_etaOC_le_two (ξ : ℝ) : ‖𝓕 etaOC ξ‖ ≤ 2 := by
  refine (Real.norm_fourier_le_integral_norm etaOC ξ).trans ?_
  have hi : Integrable ((Icc (0 : ℝ) 2).indicator (1 : ℝ → ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  calc ∫ t, ‖etaOC t‖ ≤ ∫ t, (Icc (0 : ℝ) 2).indicator 1 t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
          (Filter.Eventually.of_forall fun t => ?_)
        simp only [etaOC, Complex.norm_real, Real.norm_eq_abs]
        by_cases h : t ∈ Icc (0 : ℝ) 2
        · rw [indicator_of_mem h, Pi.one_apply]; exact etaO_le_one t
        · rw [indicator_of_notMem h, etaO_eq_zero_of_notMem h]; simp
    _ = 2 := by
        rw [integral_indicator_one measurableSet_Icc]
        simp only [Real.volume_Icc, measureReal_def]
        rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num

theorem norm_fourier_indicator_P2_le (ξ : ℝ) :
    ‖𝓕 (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) ξ‖ ≤ 14 := by
  refine (Real.norm_fourier_le_integral_norm _ ξ).trans ?_
  have hi : Integrable ((Icc (0 : ℝ) 2).indicator (fun _ => (7 : ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  calc ∫ t, ‖(((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)‖ ≤ ∫ t, (Icc (0 : ℝ) 2).indicator (fun _ => (7 : ℝ)) t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hi
          (Filter.Eventually.of_forall fun t => ?_)
        simp only [Complex.norm_real, Real.norm_eq_abs]
        by_cases h : t ∈ Icc (0 : ℝ) 2
        · rw [indicator_of_mem h, indicator_of_mem h]; exact abs_P2_le h
        · rw [indicator_of_notMem h, indicator_of_notMem h]; simp
    _ = 14 := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const]
        simp only [Real.volume_Icc, measureReal_def, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by norm_num)]; norm_num

theorem norm_sq_fourier_etaOC_le (ξ : ℝ) : ‖𝓕 etaOC ξ‖ ^ 2 ≤ 8 * (1 + ξ ^ 2)⁻¹ := by
  have h2 := norm_fourier_etaOC_le_two ξ
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  have ha0 := norm_nonneg (𝓕 etaOC ξ)
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  rcases le_or_gt |ξ| 1 with h | h
  · have : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg ξ]
    nlinarith
  · have hξ0 : ξ ≠ 0 := by intro h0; rw [h0, abs_zero] at h; linarith
    have e := norm_fourier_etaO_eq hξ0
    have h14 := norm_fourier_indicator_P2_le ξ
    have hπ := Real.pi_gt_d2
    have hsq : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
    have hξ2 : 1 < ξ ^ 2 := by rw [← hsq]; nlinarith [abs_nonneg ξ]
    have hD : 39 * ξ ^ 2 ≤ (2 * π * |ξ|) ^ 2 := by
      have h39 : (39 : ℝ) ≤ (2 * π) ^ 2 := by nlinarith
      rw [mul_pow, hsq]; nlinarith [mul_le_mul_of_nonneg_right h39 (sq_nonneg ξ)]
    have hD0 : 0 < (2 * π * |ξ|) ^ 2 := by positivity
    have ha : ‖𝓕 etaOC ξ‖ * (39 * ξ ^ 2) ≤ 14 := by
      have : ‖𝓕 etaOC ξ‖ * (2 * π * |ξ|) ^ 2 ≤ 14 := by
        have e' : ‖𝓕 etaOC ξ‖ * (2 * π * |ξ|) ^ 2 =
            ‖𝓕 (fun t => (((Icc (0 : ℝ) 2).indicator P2 t : ℝ) : ℂ)) ξ‖ := by
          rw [show 𝓕 etaOC ξ = 𝓕 (fun t => (etaO t : ℂ)) ξ from rfl, e]; field_simp
        rw [e']; exact h14
      exact le_trans (mul_le_mul_of_nonneg_left hD ha0) this
    -- `a ≤ 14/(39 ξ²)`, so `a² (1 + ξ²) ≤ 8`
    have ha' : ‖𝓕 etaOC ξ‖ ≤ 14 / (39 * ξ ^ 2) := by rw [le_div_iff₀ (by positivity)]; exact ha
    have hb : 14 / (39 * ξ ^ 2) ≤ 14 / 39 := div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by nlinarith)
    have hsq2 : ‖𝓕 etaOC ξ‖ ^ 2 * (39 * ξ ^ 2) ≤ 14 * (14 / 39) := by
      have := mul_le_mul ha (ha'.trans hb) ha0 (by norm_num)
      nlinarith
    nlinarith

theorem continuous_fourier_FM : Continuous (𝓕 FM) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) integrable_FM

theorem norm_fourier_etaSC_le (ξ : ℝ) : ‖𝓕 etaSC ξ‖ ≤ 1 := by
  refine (Real.norm_fourier_le_integral_norm etaSC ξ).trans ?_
  have : ∫ σ, ‖etaSC σ‖ = √(π / 2) / κ := by
    rw [← integral_etaS]; congr 1; ext σ
    simp only [etaSC, Complex.norm_real, Real.norm_eq_abs]; exact abs_of_nonneg (etaU_nonneg _)
  rw [this, div_le_one hκpos]
  have : √(π / 2) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; have := Real.pi_lt_d2; linarith
  rw [TernaryGoldbach.Helfgott.κ]; linarith

theorem integrable_fourier_FM : Integrable (𝓕 FM) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 8)
    continuous_fourier_FM.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [fourier_FM, norm_mul, norm_mul, ← sq]
  calc ‖𝓕 etaOC ξ‖ ^ 2 * ‖𝓕 etaSC ξ‖ ≤ (8 * (1 + ξ ^ 2)⁻¹) * 1 :=
        mul_le_mul (norm_sq_fourier_etaOC_le ξ) (norm_fourier_etaSC_le ξ) (norm_nonneg _)
          (by positivity)
    _ = 8 * (1 + ξ ^ 2)⁻¹ := mul_one _

/-- **[H, (10.22)]**: `∫ η̂◦(ξ)² η̂_*(ξ) e(ξM) dξ = C_{η◦,η_*}(M)`. -/
theorem fourier_identity (M : ℝ) :
    ∫ ξ, Complex.exp (↑(2 * π * ξ * M) * I) * (𝓕 etaOC ξ * 𝓕 etaOC ξ * 𝓕 etaSC ξ) = (Cmain M : ℂ) := by
  have h := integrable_FM.fourierInv_fourier_eq integrable_fourier_FM continuous_FM.continuousAt
    (v := M)
  rw [FM_apply, fourierInv_eq'] at h
  rw [← h]
  congr 1; ext ξ
  rw [fourier_FM, smul_eq_mul, Real.inner_apply, mul_assoc (2 * π) ξ M]

end TernaryGoldbach.MajorArcs
