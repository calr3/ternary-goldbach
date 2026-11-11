import RSBounds.SchoenfeldSexticExplicit
import RSBounds.PolynomialZeroKernel
import RSBounds.PolynomialPsiFromZeroSums

/-!
# The sixfold averaged explicit formula

The order-6 analogue of `PolynomialAveragedFormula` and of the first part of
`PolynomialPsiFromZeroSums`. All seven primitive formulas use one sequence of good contour heights.
Their sixth finite difference, divided by `h⁶`, gives the upper sextic smoothing of `ψ`, with main
term `x + 3h`, constant `−log(2π)` and an explicit left remainder.
-/

open Complex Finset Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticAveraged

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroKernel
open SchoenfeldSexticExplicit SchoenfeldSexticPsi

theorem forwardDiff_six (h : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    forwardDiff h 6 f x = f (x + 6 * h) - 6 * f (x + 5 * h) + 15 * f (x + 4 * h) -
      20 * f (x + 3 * h) + 15 * f (x + 2 * h) - 6 * f (x + h) + f x := by
  simp only [forwardDiff]
  rw [show x + h + h + h + h + h + h = x + 6 * h by ring,
    show x + h + h + h + h + h = x + 5 * h by ring,
    show x + h + h + h + h = x + 4 * h by ring,
    show x + h + h + h = x + 3 * h by ring,
    show x + h + h = x + 2 * h by ring]
  ring

/-- The zero coefficient after sixfold averaging and normalization. -/
noncomputable def zeroCoefficient (x h : ℝ) (ρ : ℂ) : ℂ :=
  forwardDiff h 6 (antiderivative ρ 6) x / (h : ℂ) ^ 6

/-- The left contour remainder after the same averaging operation. -/
noncomputable def leftRemainder (x h : ℝ) : ℂ :=
  forwardDiff h 6 psi6LeftRemainder x / (h : ℂ) ^ 6

theorem antiderivative_six_eq (ρ : ℂ) (x : ℝ) :
    antiderivative ρ 6 x =
      (x : ℂ) ^ (ρ + 6) /
        (ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4) * (ρ + 5) * (ρ + 6)) := by
  norm_num [antiderivative, rising]

private theorem forwardDiff_six_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 6 (fun t => ∑ i ∈ s, f i t) x =
      ∑ i ∈ s, forwardDiff h 6 (f i) x := by
  simp only [forwardDiff_six, sum_add_distrib, sum_sub_distrib, mul_sum]

private theorem forwardDiff_six_mul (c : ℂ) (f : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 6 (fun t => c * f t) x = c * forwardDiff h 6 f x := by
  simp only [forwardDiff_six]
  ring

private theorem forwardDiff_six_sub (f g : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 6 (fun t => f t - g t) x =
      forwardDiff h 6 f x - forwardDiff h 6 g x := by
  simp only [forwardDiff_six]
  ring

/-- The finite difference of the integrated main term. -/
theorem normalized_main_term {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    forwardDiff h 6 (fun t : ℝ => (t : ℂ) ^ 7 / 5040) x / (h : ℂ) ^ 6 =
      ((x + 3 * h : ℝ) : ℂ) := by
  have hc := congrArg (fun t : ℝ => (t : ℂ))
    (SchoenfeldSexticSmoothing.sixth_difference_main_term hh x)
  push_cast at hc
  rw [forwardDiff_six]
  push_cast
  convert hc using 1 <;> ring

/-- Sixfold averaging leaves the constant at the zero pole unchanged. -/
theorem normalized_zero_pole {h : ℝ} (hh : h ≠ 0) (x : ℝ) (c : ℂ) :
    forwardDiff h 6 (fun t : ℝ => (t : ℂ) ^ 6 * c / 720) x / (h : ℂ) ^ 6 = c := by
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  rw [forwardDiff_six]
  push_cast
  field_simp [hh0]
  ring

/-- Casting the finite arithmetic smoothing identity into the complex formula. -/
theorem normalized_Psi6 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 6 * h ≤ N) :
    forwardDiff h 6 (fun t => (Psi6 t : ℂ)) x / (h : ℂ) ^ 6 =
      (psiUpper N x h : ℂ) := by
  have hc := congrArg (fun t : ℝ => (t : ℂ))
    (sixthDifference_Psi6 hx hh hN)
  simpa only [forwardDiff_six, sixthDifference, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using hc

private theorem tendsto_normalized_forwardDiff_six
    {F : ℕ → ℝ → ℂ} {G : ℝ → ℂ} (x h : ℝ)
    (h0 : Tendsto (fun k => F k x) atTop (𝓝 (G x)))
    (h1 : Tendsto (fun k => F k (x + h)) atTop (𝓝 (G (x + h))))
    (h2 : Tendsto (fun k => F k (x + 2 * h)) atTop (𝓝 (G (x + 2 * h))))
    (h3 : Tendsto (fun k => F k (x + 3 * h)) atTop (𝓝 (G (x + 3 * h))))
    (h4 : Tendsto (fun k => F k (x + 4 * h)) atTop (𝓝 (G (x + 4 * h))))
    (h5 : Tendsto (fun k => F k (x + 5 * h)) atTop (𝓝 (G (x + 5 * h))))
    (h6 : Tendsto (fun k => F k (x + 6 * h)) atTop (𝓝 (G (x + 6 * h)))) :
    Tendsto (fun k => forwardDiff h 6 (F k) x / (h : ℂ) ^ 6) atTop
      (𝓝 (forwardDiff h 6 G x / (h : ℂ) ^ 6)) := by
  simpa only [forwardDiff_six] using
    ((((((h6.sub (h5.const_mul 6)).add (h4.const_mul 15)).sub (h3.const_mul 20)).add
      (h2.const_mul 15)).sub (h1.const_mul 6)).add h0).div_const ((h : ℂ) ^ 6)

/-- The upper sixfold averaged explicit formula along a common sequence of good heights. -/
theorem explicit_formula_upper_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 6 * h ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
      (𝓝 (((x + 3 * h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi))) := by
  let F : ℕ → ℝ → ℂ := fun k t => ∑ ρ ∈ zerosRectD zetaF (T k),
    (multRectD zetaF (T k) ρ : ℂ) * antiderivative ρ 6 t
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ 7 / 5040 - (Psi6 t : ℂ) -
    psi6LeftRemainder t - (t : ℂ) ^ 6 * Complex.log (2 * Real.pi) / 720
  have hlim (t : ℝ) (ht : 0 < t) : Tendsto (fun k => F k t) atTop (𝓝 (G t)) := by
    simpa only [F, G, antiderivative_six_eq] using
      explicit_formula_Psi6_at_heights hT ht
  have havg := tendsto_normalized_forwardDiff_six x h (hlim x hx)
    (hlim (x + h) (by linarith)) (hlim (x + 2 * h) (by linarith))
    (hlim (x + 3 * h) (by linarith)) (hlim (x + 4 * h) (by linarith))
    (hlim (x + 5 * h) (by linarith)) (hlim (x + 6 * h) (by linarith))
  have hsum (k : ℕ) : forwardDiff h 6 (F k) x / (h : ℂ) ^ 6 =
      ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ := by
    dsimp only [F]
    rw [forwardDiff_six_sum, sum_div]
    apply sum_congr rfl
    intro ρ _
    rw [forwardDiff_six_mul, mul_div_assoc]
    rfl
  have hvalue : forwardDiff h 6 G x / (h : ℂ) ^ 6 =
      ((x + 3 * h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi) := by
    dsimp only [G]
    rw [forwardDiff_six_sub, forwardDiff_six_sub, forwardDiff_six_sub,
      sub_div, sub_div, sub_div, normalized_main_term hh.ne',
      normalized_Psi6 hx.le hh hN, normalized_zero_pole hh.ne']
    rfl
  simpa only [hsum, hvalue] using havg

/-- The same formula shifted to give the lower polynomial smoothing. -/
theorem explicit_formula_lower_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h : ℝ} (hx : 6 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 6 * h) h ρ) atTop
      (𝓝 (((x - 3 * h : ℝ) : ℂ) - (psiLower N x h : ℂ) -
        leftRemainder (x - 6 * h) h - Complex.log (2 * Real.pi))) := by
  have hv := explicit_formula_upper_at_heights hT (x := x - 6 * h)
    (by linarith) hh (show x - 6 * h + 6 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel,
    show x - 6 * h + 3 * h = x - 3 * h by ring] using hv

/-! ## From eventual bounds on the zero sums to `ψ` -/

/-- The upper smoothed error from an eventual bound on its actual finite zero sums. -/
theorem upper_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h B C : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 6 * h ≤ N)
    (hzero : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ‖ ≤ B)
    (hr : ‖leftRemainder x h‖ ≤ C) :
    |psiUpper N x h - (x + 3 * h)| ≤ B + C + Real.log (2 * Real.pi) := by
  have hlim := explicit_formula_upper_at_heights hT hx hh hN
  exact PolynomialPsiFromZeroSums.smoothing_error_of_norm_bound
    (le_of_tendsto hlim.norm hzero) hr

/-- The lower smoothed error from an eventual bound on its actual finite zero sums. -/
theorem lower_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h B C : ℝ} (hx : 6 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N)
    (hzero : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 6 * h) h ρ‖ ≤ B)
    (hr : ‖leftRemainder (x - 6 * h) h‖ ≤ C) :
    |psiLower N x h - (x - 3 * h)| ≤ B + C + Real.log (2 * Real.pi) := by
  have hlim := explicit_formula_lower_at_heights hT hx hh hN
  exact PolynomialPsiFromZeroSums.smoothing_error_of_norm_bound
    (le_of_tendsto hlim.norm hzero) hr

/-- `|ψ(x) − x| ≤ zero-sum bound + left remainder + log 2π + 3h` from both smoothings. -/
theorem psi_error_of_eventually_bounded_zero_sums {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h B C : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hshift : 6 * h < x)
    (hupper : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ‖ ≤ B)
    (hlower : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 6 * h) h ρ‖ ≤ B)
    (hru : ‖leftRemainder x h‖ ≤ C) (hrl : ‖leftRemainder (x - 6 * h) h‖ ≤ C) :
    |Chebyshev.psi x - x| ≤ B + C + Real.log (2 * Real.pi) + 3 * h := by
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 6 * h)
  have hNx : x ≤ (N : ℝ) := by linarith
  have hup := upper_error_of_eventually_bounded_zero_sums hT hx hh hN hupper hru
  have hlo := lower_error_of_eventually_bounded_zero_sums hT hshift hh hNx hlower hrl
  exact psi_error_of_polynomial_errors hx.le hh hN hup hlo

end TernaryGoldbach.RSBounds.SchoenfeldSexticAveraged
