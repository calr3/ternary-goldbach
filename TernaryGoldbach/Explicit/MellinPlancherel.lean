import TernaryGoldbach.Explicit.ExplicitFormula
import TernaryGoldbach.Prelim.PlancherelReal

/-!
# Mellin–Plancherel on `ℜs = 1/2` for `G_δ`

`∫ |G_δ(1/2 + it)|² dt = 2π ∫₀^∞ |η(u)|² du` (`η(u) = u² e^{−u²/2}`): `mellin_eq_fourier` writes
`G_δ(1/2 + it) = 𝓕F(t/2π)` with `F(u) = e^{−u/2} fδ(e^{−u})`, and Plancherel (`PlancherelReal`).
-/

open Complex MeasureTheory Set Filter FourierTransform
open scoped Real

namespace TernaryGoldbach.Explicit

/-- `F_δ(u) = e^{−u/2} fδ(e^{−u})`. -/
noncomputable def Fhalf (δ u : ℝ) : ℂ := Real.exp (-(1 / 2) * u) • fδ δ (Real.exp (-u))

theorem norm_Fhalf (δ u : ℝ) :
    ‖Fhalf δ u‖ = Real.exp (-(5 / 2) * u) * Real.exp (-(Real.exp (-u)) ^ 2 / 2) := by
  rw [Fhalf, norm_smul, norm_fδ, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have e2 : Real.exp (-u) ^ 2 = Real.exp (-(2 * u)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e2, ← mul_assoc]
  congr 1
  rw [← Real.exp_add]; congr 1; ring

theorem exp_three_halves_le : Real.exp (3 / 2) ≤ 6 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]
  have : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [Real.exp_pos (1 / 2)]

theorem norm_Fhalf_le (δ u : ℝ) : ‖Fhalf δ u‖ ≤ 6 * Real.exp (-|u|) := by
  rw [norm_Fhalf]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    have h1 : Real.exp (-(5 / 2) * u) ≤ Real.exp (-u) := Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-(Real.exp (-u)) ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have := sq_nonneg (Real.exp (-u)); linarith
    calc Real.exp (-(5 / 2) * u) * Real.exp (-(Real.exp (-u)) ^ 2 / 2) ≤ Real.exp (-u) * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ 6 * Real.exp (-u) := by linarith [Real.exp_pos (-u)]
  · rw [abs_of_nonpos hu]
    set a := -u with ha
    have ha0 : 0 ≤ a := by linarith
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * a by linarith)
    have hsq : Real.exp (-u) ^ 2 = Real.exp (2 * a) := by
      rw [← Real.exp_nat_mul]; congr 1
    rw [hsq, ← Real.exp_add]
    have hle' : (5 / 2) * a - Real.exp (2 * a) / 2 ≤ 3 / 2 - a := by nlinarith [sq_nonneg (a - 5 / 4)]
    have hle : -(5 / 2) * u + -(Real.exp (2 * a)) / 2 ≤ 3 / 2 + -a := by
      have hu' : u = -a := by rw [ha]; ring
      rw [hu']; linarith
    calc Real.exp (-(5 / 2) * u + -(Real.exp (2 * a)) / 2) ≤ Real.exp (3 / 2 + -a) :=
          Real.exp_le_exp.2 hle
      _ = Real.exp (3 / 2) * Real.exp (-a) := Real.exp_add _ _
      _ ≤ 6 * Real.exp (-a) := by gcongr; exact exp_three_halves_le

theorem continuous_Fhalf (δ : ℝ) : Continuous (Fhalf δ) := by
  unfold Fhalf; exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-(1 / 2) * u)).smul
    ((continuous_fδ δ).comp (by fun_prop))

theorem integrable_Fhalf (δ : ℝ) : Integrable (Fhalf δ) :=
  ((integrable_exp_neg_abs (c := 1) one_pos).const_mul 6).mono'
    (continuous_Fhalf δ).aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa using norm_Fhalf_le δ u)

theorem memLp_Fhalf (δ : ℝ) : MemLp (Fhalf δ) 2 := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_Fhalf δ).aestronglyMeasurable).2 ?_
  refine ((integrable_exp_neg_abs (c := 2) two_pos).const_mul 36).mono'
    ((continuous_Fhalf δ).norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := norm_Fhalf_le δ u
  have h0 := norm_nonneg (Fhalf δ u)
  have : (6 * Real.exp (-|u|)) ^ 2 = 36 * Real.exp (-(2 * |u|)) := by
    rw [mul_pow, ← Real.exp_nat_mul]; norm_num
  nlinarith [pow_le_pow_left₀ h0 h 2]

theorem G_half_eq_fourier (δ t : ℝ) :
    Gr (((1 / 2 : ℝ) : ℂ) + t * I) δ 0 = 𝓕 (Fhalf δ) (t / (2 * π)) := by
  rw [← mellin_fδ, mellin_eq_fourier]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add]
  congr 1

/-- **Mellin–Plancherel**: `∫ |G_δ(1/2 + it)|² dt = 2π ∫₀^∞ (u² e^{−u²/2})² du`. -/
theorem integral_norm_sq_G_half (δ : ℝ) :
    ∫ t : ℝ, ‖Gr (((1 / 2 : ℝ) : ℂ) + t * I) δ 0‖ ^ 2 =
      2 * π * ∫ u in Ioi (0:ℝ), (u ^ 2 * Real.exp (-u ^ 2 / 2)) ^ 2 := by
  simp_rw [G_half_eq_fourier]
  have h1 := Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 (Fhalf δ) ξ‖ ^ 2) (2 * π)
  rw [h1, abs_of_pos (by positivity), smul_eq_mul,
    TernaryGoldbach.integral_norm_sq_fourier (integrable_Fhalf δ) (memLp_Fhalf δ)]
  congr 1
  -- `∫ e^{−u} |fδ(e^{−u})|² du = ∫₀^∞ |fδ|²` via `mellin_eq_fourier` at `s = 1`
  set g : ℝ → ℂ := fun v => (((v ^ 2 * Real.exp (-v ^ 2 / 2)) ^ 2 : ℝ) : ℂ) with hg
  have hm := mellin_eq_fourier g (s := (1 : ℂ))
  simp only [Complex.one_re, Complex.one_im, zero_div] at hm
  rw [Real.fourier_eq] at hm
  simp only [inner_zero_right, neg_zero, Real.fourierChar_apply, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, Circle.smul_def] at hm
  simp only [one_smul] at hm
  rw [mellin] at hm
  have hL : ∫ t in Ioi (0:ℝ), (t : ℂ) ^ ((1:ℂ) - 1) • g t =
      ((∫ u in Ioi (0:ℝ), (u ^ 2 * Real.exp (-u ^ 2 / 2)) ^ 2 : ℝ) : ℂ) := by
    simp only [sub_self, Complex.cpow_zero, one_smul, hg]; exact integral_ofReal
  have hpt : ∀ v : ℝ, Real.exp (-1 * v) • g (Real.exp (-v)) = ((‖Fhalf δ v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    rw [Complex.real_smul, hg, ← Complex.ofReal_mul]
    congr 1
    rw [norm_Fhalf]
    have h5 : Real.exp (-(5 / 2) * v) ^ 2 = Real.exp (-v) ^ 5 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h1 : Real.exp (-1 * v) = Real.exp (-v) := by ring_nf
    rw [h1, mul_pow (Real.exp (-(5 / 2) * v)), h5]
    ring
  have hR : ∫ v, Real.exp (-1 * v) • g (Real.exp (-v)) = ((∫ x, ‖Fhalf δ x‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]; exact integral_ofReal
  rw [hL, hR] at hm
  exact_mod_cast hm.symm

end TernaryGoldbach.Explicit
