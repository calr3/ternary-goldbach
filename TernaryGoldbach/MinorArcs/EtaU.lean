import TernaryGoldbach.MinorArcs.InnerSums
import TernaryGoldbach.MinorArcs.EtaStar
import TernaryGoldbach.MinorArcs.PhiIntegrals
import TernaryGoldbach.Helfgott.Eta2

variable [Fact TernaryGoldbach.RHUpTo] [Fact TernaryGoldbach.ButhePsi]
  [Fact TernaryGoldbach.RamareMoebius]

/-!
# The unscaled `η_*` and its Fourier transform

`η(u) = (η₂ *_M φ)(u) = ∫_0^∞ η₂(u/w) φ(w) dw/w` (`etaU`; `0` for `u ≤ 0`). Then
`η_*(t) = η(κt)` (`etaStar_eq_etaU`). This is the `η` of [H, Cor 7.1.3].

`η̂(t) = ∫_0^∞ φ(w) η̂₂(wt) dw` (Fubini). The trusted (B.6), `(2πs)² |η̂₂(s)| ≤ c₀`, then gives
`|η̂(t)| ≤ c₀ √(π/2) / (2πt)²` (**`norm_fourier_etaU_le`**).

Proved, modulo the trusted (B.6) (`eta2_fourier_bound'`).
-/

open Real Set MeasureTheory FourierTransform Filter
open TernaryGoldbach (e)

namespace TernaryGoldbach.MinorArcs

open TernaryGoldbach.Helfgott (eta2 etaStar phi κ mellinConv)

/-- `η(u) = ∫_0^∞ η₂(u/w) φ(w) dw/w`. -/
noncomputable def etaU (u : ℝ) : ℝ := ∫ w in Ioi (0:ℝ), eta2 (u / w) * phi w / w

theorem etaStar_eq_etaU {t : ℝ} (ht : 0 < t) : etaStar t = etaU (κ * t) := by
  unfold etaStar etaU
  have hκ : (0:ℝ) < κ := by rw [Helfgott.κ]; norm_num
  rw [mellinConv_eq_swap _ _ (by positivity)]

/-- `∫_u e(-ut) η₂(u/w) du` has norm `w |η̂₂(wt)|` for `w > 0`. -/
theorem norm_inner_fourier {w : ℝ} (hw : 0 < w) (t : ℝ) :
    ‖∫ u, e (-(u * t)) * (eta2 (u / w) : ℂ)‖ = w * ‖𝓕 (fun u => (eta2 u : ℂ)) (w * t)‖ := by
  have h := TernaryGoldbach.norm_fourier_comp_affine (fun u => (eta2 u : ℂ)) (inv_pos.2 hw) 0 t
  rw [TernaryGoldbach.fourier_eq_integral_e] at h
  simp only [add_zero, inv_inv] at h
  rw [show t / w⁻¹ = w * t by field_simp] at h
  rw [← h]
  congr 2; ext u; rw [div_eq_inv_mul]

theorem integrable_eta2 : Integrable eta2 :=
  Helfgott.continuous_eta2.integrable_of_hasCompactSupport Helfgott.hasCompactSupport_eta2

theorem integrable_eta2_div {w : ℝ} (hw : w ≠ 0) : Integrable fun u => eta2 (u / w) :=
  integrable_eta2.comp_div hw

theorem integral_abs_eta2_div {w : ℝ} (hw : 0 < w) : ∫ u, |eta2 (u / w)| = w := by
  have := MeasureTheory.Measure.integral_comp_div (fun v => |eta2 v|) w
  rw [this, Helfgott.integral_abs_eta2, abs_of_pos hw, smul_eq_mul, mul_one]

/-- **`|η̂(t)| ≤ c₀ √(π/2)/(2πt)²`** (via `η̂(t) = ∫ φ(w) η̂₂(wt) dw` and (B.6)). -/
theorem norm_fourier_etaU_le {t : ℝ} (ht : t ≠ 0) :
    ‖𝓕 (fun u => (etaU u : ℂ)) t‖ ≤ c₀ * (√(π / (1 / 2)) / 2) / (2 * π * t) ^ 2 := by
  set F : ℝ → ℝ → ℂ := fun u w => e (-(u * t)) * ((eta2 (u / w) * phi w / w : ℝ) : ℂ) with hF
  have hφc : Continuous phi := by unfold phi; fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (Continuous.measurable ?_ |>.mul ?_).aestronglyMeasurable
    · exact continuous_e.comp ((continuous_fst.mul continuous_const).neg)
    · refine Complex.measurable_ofReal.comp ?_
      exact ((Helfgott.continuous_eta2.measurable.comp (measurable_fst.div measurable_snd)).mul
        (hφc.measurable.comp measurable_snd)).div measurable_snd
  have hnorm : ∀ u, ∀ w, 0 < w → ‖F u w‖ = |eta2 (u / w)| * (phi w / w) := fun u w hw => by
    simp only [hF, norm_mul, TernaryGoldbach.norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_div, abs_mul, abs_of_nonneg (phi_nonneg w), abs_of_pos hw, mul_div_assoc]
  have hint : Integrable (Function.uncurry F)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w (hw : 0 < w) => ?_)
      refine Integrable.mono' ((integrable_eta2_div hw.ne').abs.mul_const (phi w / w)) ?_
        (Eventually.of_forall fun u => (hnorm u w hw).le)
      have hc : Continuous fun u : ℝ => F u w := by
        simp only [hF]
        exact (continuous_e.comp ((continuous_id.mul continuous_const).neg)).mul
          (Complex.continuous_ofReal.comp
            (((Helfgott.continuous_eta2.comp (continuous_id.div_const w)).mul continuous_const).div_const w))
      exact hc.aestronglyMeasurable
    · have h : ∀ w ∈ Ioi (0:ℝ), ∫ u, ‖Function.uncurry F (u, w)‖ = phi w := by
        intro w (hw : 0 < w)
        simp only [Function.uncurry_apply_pair]
        rw [integral_congr_ae (Eventually.of_forall fun u => hnorm u w hw), integral_mul_const,
          integral_abs_eta2_div hw]
        field_simp
      exact (integrable_phi.integrableOn (s := Ioi 0)).congr_fun (fun w hw => (h w hw).symm)
        measurableSet_Ioi
  have h1 : 𝓕 (fun u => (etaU u : ℂ)) t = ∫ u, ∫ w in Ioi (0:ℝ), F u w := by
    rw [TernaryGoldbach.fourier_eq_integral_e]
    congr 1; ext u
    simp only [hF, etaU]
    rw [integral_const_mul, integral_complex_ofReal]
  rw [h1, integral_integral_swap hint]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hB6 : ∀ s : ℝ, s ≠ 0 → ‖𝓕 (fun u => (eta2 u : ℂ)) s‖ ≤ c₀ / (2 * π * s) ^ 2 := by
    intro s hs
    have := eta2_fourier_bound' s
    rw [le_div_iff₀ (by have := Real.pi_pos; positivity)]
    linarith
  have h2 : ∀ w ∈ Ioi (0:ℝ), ‖∫ u, F u w‖ ≤ c₀ / (2 * π * t) ^ 2 * rexp (-w ^ 2 / 2) := by
    intro w (hw : 0 < w)
    have e1 : ∫ u, F u w = ((phi w / w : ℝ) : ℂ) * ∫ u, e (-(u * t)) * (eta2 (u / w) : ℂ) := by
      rw [← integral_const_mul]; congr 1; ext u; simp only [hF]; push_cast; ring
    rw [e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (phi_nonneg w)
      hw.le), norm_inner_fourier hw t]
    have := hB6 (w * t) (mul_ne_zero hw.ne' ht)
    calc phi w / w * (w * ‖𝓕 (fun u => (eta2 u : ℂ)) (w * t)‖)
        = phi w * ‖𝓕 (fun u => (eta2 u : ℂ)) (w * t)‖ := by field_simp
      _ ≤ phi w * (c₀ / (2 * π * (w * t)) ^ 2) := mul_le_mul_of_nonneg_left this (phi_nonneg w)
      _ = c₀ / (2 * π * t) ^ 2 * rexp (-w ^ 2 / 2) := by
          unfold phi; field_simp
  have hg := integral_gaussian_Ioi (1 / 2)
  have hg' : ∫ w in Ioi (0:ℝ), rexp (-w ^ 2 / 2) = √(π / (1 / 2)) / 2 := by
    rw [← hg]; congr 1; ext w; ring_nf
  have hint2 : IntegrableOn (fun w => c₀ / (2 * π * t) ^ 2 * rexp (-w ^ 2 / 2)) (Ioi 0) :=
    (integrable_exp_neg_sq_half.const_mul _).integrableOn
  refine (integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _) hint2
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall h2))).trans (le_of_eq ?_)
  rw [integral_const_mul, hg']
  ring

end TernaryGoldbach.MinorArcs
