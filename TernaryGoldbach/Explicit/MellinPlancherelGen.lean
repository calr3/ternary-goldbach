import TernaryGoldbach.Explicit.LineZeros

/-!
# Mellin–Plancherel on `ℜs = 1/2`, for a general smoothing

If `Φ(u) = e^{−u/2} φ(e^{−u})` is continuous with `|Φ(u)| ≤ C e^{−c|u|}`, then `F(t) = M φ(1/2 + it)`
is `C¹` with `∫|F|² = 2π ∫₀^∞ |φ|²` and `∫|F'|² = 2π ∫₀^∞ (log v)² |φ(v)|² dv` (as `MellinPlancherel` for
`η(t) e(δt)`).
-/

open Complex MeasureTheory Set Filter FourierTransform
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `Φ(u) = e^{−u/2} φ(e^{−u})`. -/
noncomputable def PhiG (φ : ℝ → ℂ) (u : ℝ) : ℂ := Real.exp (-(1 / 2) * u) • φ (Real.exp (-u))

/-- The hypotheses of Mellin–Plancherel. -/
structure PlancherelData (φ : ℝ → ℂ) (C c : ℝ) : Prop where
  cont : Continuous (PhiG φ)
  c_pos : 0 < c
  bound : ∀ u : ℝ, ‖PhiG φ u‖ ≤ C * Real.exp (-(c * |u|))

variable {φ : ℝ → ℂ} {C c : ℝ}

theorem norm_smul_PhiG_le (hp : PlancherelData φ C c) (x : ℝ) :
    ‖x • PhiG φ x‖ ≤ (2 * C / c) * Real.exp (-((c / 2) * |x|)) := by
  have hc := hp.c_pos
  rw [norm_smul, Real.norm_eq_abs]
  have h1 := hp.bound x
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hp.bound 0); simp at this; exact this
  have h2 : |x| ≤ 2 / c * Real.exp ((c / 2) * |x|) := by
    have := Real.add_one_le_exp ((c / 2) * |x|)
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; nlinarith [abs_nonneg x]
  have h3 : Real.exp ((c / 2) * |x|) * Real.exp (-(c * |x|)) = Real.exp (-((c / 2) * |x|)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |x| * ‖PhiG φ x‖ ≤ (2 / c * Real.exp ((c / 2) * |x|)) * (C * Real.exp (-(c * |x|))) :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = (2 * C / c) * (Real.exp ((c / 2) * |x|) * Real.exp (-(c * |x|))) := by ring
    _ = _ := by rw [h3]

theorem integrable_PhiG (hp : PlancherelData φ C c) : Integrable (PhiG φ) :=
  (integrable_memLp_of_exp hp.cont hp.c_pos hp.bound).1

theorem memLp_PhiG (hp : PlancherelData φ C c) : MemLp (PhiG φ) 2 :=
  (integrable_memLp_of_exp hp.cont hp.c_pos hp.bound).2

theorem integrable_smul_PhiG (hp : PlancherelData φ C c) : Integrable fun x : ℝ => x • PhiG φ x :=
  (integrable_memLp_of_exp (continuous_id.smul hp.cont) (half_pos hp.c_pos) (norm_smul_PhiG_le hp)).1

/-- `F(t) = M φ(1/2 + it)`. -/
noncomputable def flineG (φ : ℝ → ℂ) (t : ℝ) : ℂ := 𝓕 (PhiG φ) (t / (2 * π))

/-- The integrand of `F'`. -/
noncomputable def PhiDG (φ : ℝ → ℂ) (x : ℝ) : ℂ := (-2 * π * I * x) • PhiG φ x

/-- `F'(t)`. -/
noncomputable def flineDG (φ : ℝ → ℂ) (t : ℝ) : ℂ := (1 / (2 * π) : ℝ) • 𝓕 (PhiDG φ) (t / (2 * π))

theorem mellin_half_eq (φ : ℝ → ℂ) (t : ℝ) :
    mellin φ (((1 / 2 : ℝ) : ℂ) + t * I) = flineG φ t := by
  rw [mellin_eq_fourier, flineG]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add]
  rfl

theorem norm_PhiDG_le (hp : PlancherelData φ C c) (x : ℝ) :
    ‖PhiDG φ x‖ ≤ 2 * π * (2 * C / c) * Real.exp (-((c / 2) * |x|)) := by
  have e : PhiDG φ x = (-2 * π * I) * (x • PhiG φ x) := by
    rw [PhiDG, smul_eq_mul, Complex.real_smul]; ring
  rw [e, norm_mul]
  have : ‖-2 * π * I‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [this, mul_assoc (2 * π)]
  exact mul_le_mul_of_nonneg_left (norm_smul_PhiG_le hp x) (by positivity)

theorem integrable_memLp_PhiDG (hp : PlancherelData φ C c) :
    Integrable (PhiDG φ) ∧ MemLp (PhiDG φ) 2 := by
  have hc : Continuous (PhiDG φ) := by
    have := hp.cont
    unfold PhiDG
    exact (by fun_prop : Continuous fun x : ℝ => (-2 * π * I * x)).smul this
  exact integrable_memLp_of_exp hc (half_pos hp.c_pos) (norm_PhiDG_le hp)

theorem hasDerivAt_flineG (hp : PlancherelData φ C c) (t : ℝ) :
    HasDerivAt (flineG φ) (flineDG φ t) t := by
  have h := Real.hasDerivAt_fourier (integrable_PhiG hp) (integrable_smul_PhiG hp) (t / (2 * π))
  have h2 : HasDerivAt (fun t : ℝ => t / (2 * π)) (1 / (2 * π)) t := by
    simpa using (hasDerivAt_id t).div_const (2 * π)
  exact h.scomp t h2

theorem continuous_flineG (hp : PlancherelData φ C c) : Continuous (flineG φ) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_flineG hp t).continuousAt

theorem continuous_flineDG (hp : PlancherelData φ C c) : Continuous (flineDG φ) := by
  have hc : Continuous (𝓕 (PhiDG φ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop)
      (integrable_memLp_PhiDG hp).1
  have h2 : Continuous fun t : ℝ => t / (2 * π) := by fun_prop
  unfold flineDG
  exact (hc.comp h2).const_smul (1 / (2 * π) : ℝ)

theorem norm_PhiG_sq (φ : ℝ → ℂ) (u : ℝ) :
    ‖PhiG φ u‖ ^ 2 = Real.exp (-u) * ‖φ (Real.exp (-u))‖ ^ 2 := by
  rw [PhiG, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  congr 2; push_cast; ring

theorem integral_norm_sq_PhiG (φ : ℝ → ℂ) :
    ∫ u, ‖PhiG φ u‖ ^ 2 = ∫ v in Ioi (0:ℝ), ‖φ v‖ ^ 2 := by
  simp_rw [norm_PhiG_sq]; exact integral_exp_neg_comp (fun v => ‖φ v‖ ^ 2)

theorem integral_sq_mul_norm_sq_PhiG (φ : ℝ → ℂ) :
    ∫ u, u ^ 2 * ‖PhiG φ u‖ ^ 2 = ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * ‖φ v‖ ^ 2 := by
  rw [← integral_exp_neg_comp (fun v => Real.log v ^ 2 * ‖φ v‖ ^ 2)]
  congr 1; ext u
  rw [norm_PhiG_sq, Real.log_exp]; ring

theorem integrable_norm_sq_flineG (hp : PlancherelData φ C c) :
    Integrable fun t => ‖flineG φ t‖ ^ 2 := by
  have hM := TernaryGoldbach.memLp_fourier (integrable_PhiG hp) (memLp_PhiG hp)
  have h := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).1 hM
  exact h.comp_div (show (2 * π : ℝ) ≠ 0 by positivity)

theorem integrable_norm_sq_flineDG (hp : PlancherelData φ C c) :
    Integrable fun t => ‖flineDG φ t‖ ^ 2 := by
  have hM := TernaryGoldbach.memLp_fourier (integrable_memLp_PhiDG hp).1 (integrable_memLp_PhiDG hp).2
  have h := (memLp_two_iff_integrable_sq_norm hM.aestronglyMeasurable).1 hM
  have h2 := (h.comp_div (show (2 * π : ℝ) ≠ 0 by positivity)).const_mul ((1 / (2 * π)) ^ 2)
  refine h2.congr (Eventually.of_forall fun t => ?_)
  simp only [flineDG, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]

theorem integral_norm_sq_flineG (hp : PlancherelData φ C c) :
    ∫ t, ‖flineG φ t‖ ^ 2 = 2 * π * ∫ v in Ioi (0:ℝ), ‖φ v‖ ^ 2 := by
  simp only [flineG]
  have h1 := Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (PhiG φ) ξ‖ ^ 2) (2 * π)
  rw [h1, abs_of_pos (by positivity), smul_eq_mul,
    TernaryGoldbach.integral_norm_sq_fourier (integrable_PhiG hp) (memLp_PhiG hp),
    integral_norm_sq_PhiG]

theorem integral_norm_sq_flineDG (hp : PlancherelData φ C c) :
    ∫ t, ‖flineDG φ t‖ ^ 2 = 2 * π * ∫ v in Ioi (0:ℝ), Real.log v ^ 2 * ‖φ v‖ ^ 2 := by
  have hpi : 0 < 2 * π := by positivity
  have e1 : ∀ t, ‖flineDG φ t‖ ^ 2 = (1 / (2 * π)) ^ 2 * ‖𝓕 (PhiDG φ) (t / (2 * π))‖ ^ 2 := by
    intro t
    rw [flineDG, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simp_rw [e1]
  rw [integral_const_mul]
  have h1 := Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (PhiDG φ) ξ‖ ^ 2) (2 * π)
  rw [h1, abs_of_pos hpi, smul_eq_mul, TernaryGoldbach.integral_norm_sq_fourier
    (integrable_memLp_PhiDG hp).1 (integrable_memLp_PhiDG hp).2]
  have e2 : ∀ x, ‖PhiDG φ x‖ ^ 2 = (2 * π) ^ 2 * (x ^ 2 * ‖PhiG φ x‖ ^ 2) := by
    intro x
    have e : PhiDG φ x = (-2 * π * I) * (x • PhiG φ x) := by
      rw [PhiDG, smul_eq_mul, Complex.real_smul]; ring
    rw [e, norm_mul, norm_smul, Real.norm_eq_abs]
    have : ‖-2 * π * I‖ = 2 * π := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [this, mul_pow, mul_pow (|x|), sq_abs]
  simp_rw [e2]
  rw [integral_const_mul, integral_sq_mul_norm_sq_PhiG]
  field_simp

end TernaryGoldbach.Explicit
