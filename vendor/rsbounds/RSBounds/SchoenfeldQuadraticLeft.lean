import RSBounds.SchoenfeldQuadraticPsi
import RSBounds.MertensIntervalLeftBound

/-!
# An explicit bound for the actual quadratic left-contour remainder

The primitive remainder is bounded directly on Re(s) = -1/2. The
three-point second difference then gives a common upper/lower allowance.
All contour integrals and kernels are the actual ones in the quadratic
explicit formula; no remainder estimate is assumed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Complex Set MeasureTheory
open scoped Real

namespace TernaryGoldbach.RSBounds.SchoenfeldQuadraticLeft

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroKernel
open QuadraticMellin QuadraticZeta QuadraticZeroKernel
open MertensIntervalLeftBound

/-- An integrable majorant obtained from the already proved left-line bounds. -/
theorem norm_left_integrand_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖contourIntegrand riemannZeta kernel x (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (13500 * x ^ (-1 / 2 : ℝ)) * (1 + |t|) ^ (-3 / 2 : ℝ) := by
  have hu : 0 < 1 + |t| := by positivity
  have hu1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow : (1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ (3 : ℕ) =
      (1 + |t|) ^ (-5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (1 + |t|) 3, ← Real.rpow_sub hu]
    norm_num
  have hdecay : (1 + |t|) ^ (-5 / 2 : ℝ) ≤ (1 + |t|) ^ (-3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
  rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : ((((-1 / 2 : ℝ) : ℂ) + t * I) : ℂ).re = -1 / 2 := by simp
  rw [hre]
  calc
    _ ≤ (500 * (1 + |t|) ^ (1 / 2 : ℝ)) *
        ((27 / (1 + |t|) ^ (3 : ℕ)) * x ^ (-1 / 2 : ℝ)) := by
      exact mul_le_mul (norm_logDeriv_zeta_left_le_sqrt t)
        (mul_le_mul_of_nonneg_right
          (QuadraticKernel.norm_kernel_line_le_cube (-1 / 2) t (Or.inl rfl))
          (by positivity)) (by positivity) (by positivity)
    _ = (13500 * x ^ (-1 / 2 : ℝ)) *
        ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ (3 : ℕ)) := by ring
    _ = (13500 * x ^ (-1 / 2 : ℝ)) * (1 + |t|) ^ (-5 / 2 : ℝ) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

/-- The genuine second-primitive left integral, with an unconditional bound. -/
theorem norm_primitive_left_le {x : ℝ} (hx : 0 < x) :
    ‖psi2LeftRemainder x‖ ≤ 9000 * x * Real.sqrt x := by
  have hi : ‖∫ t : ℝ, contourIntegrand riemannZeta kernel x
      (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 54000 * x ^ (-1 / 2 : ℝ) := by
    calc
      _ ≤ ∫ t : ℝ, (13500 * x ^ (-1 / 2 : ℝ)) *
          (1 + |t|) ^ (-3 / 2 : ℝ) :=
        norm_integral_le_of_norm_le
          (integrable_one_add_abs_neg_three_halves.const_mul _)
          (Filter.Eventually.of_forall (norm_left_integrand_le hx))
      _ = _ := by rw [integral_const_mul, integral_one_add_abs_neg_three_halves]; ring
  have hfac : ‖(x : ℂ) ^ 2 / (2 * Real.pi)‖ = x ^ 2 / (2 * Real.pi) := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    norm_num [norm_mul, Real.pi_pos.le]
  have hp : x ^ (2 : ℕ) * x ^ (-1 / 2 : ℝ) = x * Real.sqrt x := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx, Real.sqrt_eq_rpow]
    calc
      x ^ ((2 : ℝ) + (-1 / 2 : ℝ)) = x ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by norm_num
      _ = x * x ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hx, Real.rpow_one]
  have hc : (54000 : ℝ) / (2 * Real.pi) ≤ 9000 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    linarith [Real.pi_gt_three]
  rw [psi2LeftRemainder, norm_mul, hfac]
  calc
    _ ≤ (x ^ 2 / (2 * Real.pi)) * (54000 * x ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (54000 / (2 * Real.pi)) * (x ^ 2 * x ^ (-1 / 2 : ℝ)) := by ring
    _ ≤ 9000 * (x ^ 2 * x ^ (-1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [hp]; ring

/-- One bound covers all three arguments of either smoothing stencil. -/
theorem norm_primitive_left_le_uniform {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyx : y ≤ 2 * x) :
    ‖psi2LeftRemainder y‖ ≤ 36000 * x * Real.sqrt x := by
  have hs : Real.sqrt y ≤ 2 * Real.sqrt x := by
    nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt hy.le,
      Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  have hp := mul_le_mul hyx hs (Real.sqrt_nonneg y) (by positivity : 0 ≤ 2 * x)
  calc
    _ ≤ 9000 * y * Real.sqrt y := norm_primitive_left_le hy
    _ = 9000 * (y * Real.sqrt y) := by ring
    _ ≤ 9000 * ((2 * x) * (2 * Real.sqrt x)) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

/-- A generic three-term bound before inserting the relative smoothing step. -/
theorem norm_averaged_left_le {x y h : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hh : 0 < h) (hyx : y + 2 * h ≤ 2 * x) :
    ‖QuadraticAveraged.leftRemainder y h‖ ≤
      (144000 * x * Real.sqrt x) / h ^ 2 := by
  have h0 := norm_primitive_left_le_uniform hx hy (by linarith : y ≤ 2 * x)
  have h1 := norm_primitive_left_le_uniform hx (by linarith : 0 < y + h)
    (by linarith : y + h ≤ 2 * x)
  have h2 := norm_primitive_left_le_uniform hx (by linarith : 0 < y + 2 * h) hyx
  have hd : ‖forwardDiff h 2 psi2LeftRemainder y‖ ≤ 144000 * x * Real.sqrt x := by
    rw [forwardDiff_two]
    calc
      _ ≤ ‖psi2LeftRemainder (y + 2 * h) - 2 * psi2LeftRemainder (y + h)‖ +
          ‖psi2LeftRemainder y‖ := norm_add_le _ _
      _ ≤ (‖psi2LeftRemainder (y + 2 * h)‖ + ‖2 * psi2LeftRemainder (y + h)‖) +
          ‖psi2LeftRemainder y‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = (‖psi2LeftRemainder (y + 2 * h)‖ + 2 * ‖psi2LeftRemainder (y + h)‖) +
          ‖psi2LeftRemainder y‖ := by rw [norm_mul]; norm_num
      _ ≤ _ := by linarith
  rw [QuadraticAveraged.leftRemainder, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  exact div_le_div_of_nonneg_right hd (sq_nonneg h)

theorem normalized_bound_eq {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) :
    (144000 * x * Real.sqrt x) / (δ * x) ^ 2 =
      144000 / (δ ^ 2 * Real.sqrt x) := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hfac : δ ^ 2 * x = δ ^ 2 * Real.sqrt x * Real.sqrt x := by
    rw [mul_assoc, Real.mul_self_sqrt hx.le]
  calc
    _ = (144000 * Real.sqrt x) / (δ ^ 2 * x) := by
      field_simp [hx.ne', hδ.ne']
      <;> ring
    _ = _ := by
      rw [hfac]
      field_simp [hδ.ne', hs]
      <;> ring

/-- An unconditional quantitative bound on both actual averaged left integrals. -/
theorem leftAllowance_le {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1) :
    SchoenfeldQuadraticPsi.leftAllowance x δ ≤ 150000 / (δ ^ 2 * Real.sqrt x) := by
  have hh : 0 < δ * x := mul_pos hδ hx
  have hshift : 2 * (δ * x) < x := by
    have h := mul_lt_mul_of_pos_right hδ2 hx
    nlinarith only [h]
  have hu := norm_averaged_left_le hx hx hh
    (by linarith : x + 2 * (δ * x) ≤ 2 * x)
  have hl := norm_averaged_left_le hx (by linarith : 0 < x - 2 * (δ * x)) hh
    (by linarith : x - 2 * (δ * x) + 2 * (δ * x) ≤ 2 * x)
  rw [normalized_bound_eq hx hδ] at hu hl
  have hc : (144000 : ℝ) / (δ ^ 2 * Real.sqrt x) ≤
      150000 / (δ ^ 2 * Real.sqrt x) :=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  exact max_le (hu.trans hc) (hl.trans hc)

/-- The actual psi bound now has no unevaluated left-contour allowance. -/
theorem psi_error_le_envelope (hRH : Goals.FiniteRH 1894438.5122)
    {x δ U : ℝ} (hx : 1 < x) (hδ : 0 < δ) (hδ2 : 2 * δ < 1)
    (hAU : 1894438.5122 ≤ U)
    (hnear : Real.log (U / 17) ^ 2 ≤ Real.log x / 9.645908801)
    (hfar : Real.log x / 9.645908801 < 2 * Real.log (U / 17) ^ 2) :
    |Chebyshev.psi x - x| ≤ SchoenfeldQuadraticEnvelope.envelope x δ U +
      150000 / (δ ^ 2 * Real.sqrt x) + Real.log (2 * Real.pi) + δ * x := by
  have h := SchoenfeldQuadraticPsi.psi_error_le_envelope hRH hx hδ hδ2 hAU hnear hfar
  have hl := leftAllowance_le (by linarith : 0 < x) hδ hδ2
  linarith

end TernaryGoldbach.RSBounds.SchoenfeldQuadraticLeft
