import RSBounds.SchoenfeldSexticAveraged
import RSBounds.PolynomialLowerKernel

/-!
# Single-zero bounds for the sixfold averaged coefficient

The order-6 analogue of `PolynomialKernelScaling`, of the high-zero parts of `PolynomialZeroKernel`,
`PolynomialLowerKernel` and `PolynomialZeroPairing`, and of `PolynomialLeftKernel`.

The zero coefficient dilates exactly:
`zeroCoefficient (x y) (δ x) ρ = x^ρ · Δ_δ⁶ A_ρ(y) / δ⁶` with `A_ρ(t) = t^{ρ+6}/(ρ(ρ+1)⋯(ρ+6))`.
Every bound below comes from `PolynomialLowerKernel.norm_forwardDiff_le_const_on`
(`‖Δ_δⁿ f(y)‖ ≤ 2ⁿ sup_{[y, y+nδ]} ‖f‖`) and `‖ρ(ρ+1)⋯(ρ+6)‖ ≥ |Im ρ|⁷`:

* upper average, `Re ρ ≤ 1`: `‖zeroCoefficient x (δx) ρ‖ ≤ (R6 δ/δ⁶) x^{Re ρ}/|Im ρ|⁷`, with
  `R6 δ = 64 (1 + 6δ)⁷`;
* lower average, `0 ≤ Re ρ`, `6δ < 1`: the same bound for `zeroCoefficient (x − 6δx) (δx) ρ`;
* left line `Re s = −1/2`, `δ ≤ 0.01`, `1 − 6δ ≤ y ≤ 1`:
  `‖zeroCoefficient (x y) (δx) s‖ ≤ x^{−1/2} · 91/(δ⁶ ‖s(s+1)⋯(s+6)‖)`.

`R6` is cruder than RS75's `((1+δ)⁷ + 1)⁶`; for the steps used (`δ < 10⁻⁵`) the two agree to
`3·10⁻⁴` relative.
-/

open Complex Set

namespace TernaryGoldbach.RSBounds.SchoenfeldSexticKernel

open PolynomialZeroKernel SchoenfeldSexticAveraged

/-- The numerator constant of the sextic high-zero bound. -/
def R6 (δ : ℝ) : ℝ := 64 * (1 + 6 * δ) ^ 7

theorem R6_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ R6 δ := by unfold R6; positivity

theorem sixtyfour_le_R6 {δ : ℝ} (hδ : 0 ≤ δ) : 64 ≤ R6 δ := by
  unfold R6
  have h : 1 ≤ (1 + 6 * δ) ^ 7 := one_le_pow₀ (by linarith)
  linarith

/-! ## Dilation -/

theorem antiderivative_six_mul {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (ρ : ℂ) :
    antiderivative ρ 6 (x * y) =
      (x : ℂ) ^ (ρ + 6) * antiderivative ρ 6 y := by
  simp only [antiderivative, Nat.cast_ofNat, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hx.le hy]
  ring

theorem forwardDiff_six_dilate (f : ℝ → ℂ) (x y δ : ℝ) :
    forwardDiff (δ * x) 6 f (x * y) =
      forwardDiff δ 6 (fun t => f (x * t)) y := by
  rw [forwardDiff_six, forwardDiff_six]
  rw [show x * y + 6 * (δ * x) = x * (y + 6 * δ) by ring,
    show x * y + 5 * (δ * x) = x * (y + 5 * δ) by ring,
    show x * y + 4 * (δ * x) = x * (y + 4 * δ) by ring,
    show x * y + 3 * (δ * x) = x * (y + 3 * δ) by ring,
    show x * y + 2 * (δ * x) = x * (y + 2 * δ) by ring,
    show x * y + δ * x = x * (y + δ) by ring]

/-- Dilation is exact before any zero-location estimate is used. -/
theorem zeroCoefficient_dilate {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    zeroCoefficient (x * y) (δ * x) ρ =
      (x : ℂ) ^ ρ *
        (forwardDiff δ 6 (antiderivative ρ 6) y / (δ : ℂ) ^ 6) := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hδc : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ.ne'
  rw [zeroCoefficient, forwardDiff_six_dilate, forwardDiff_six, forwardDiff_six]
  rw [antiderivative_six_mul hx (by linarith),
    antiderivative_six_mul hx (by linarith),
    antiderivative_six_mul hx (by linarith),
    antiderivative_six_mul hx (by linarith),
    antiderivative_six_mul hx (by linarith),
    antiderivative_six_mul hx (by linarith), antiderivative_six_mul hx hy.le]
  rw [Complex.cpow_add _ _ hxc, Complex.cpow_ofNat]
  push_cast
  field_simp [hxc, hδc]
  <;> ring

theorem norm_zeroCoefficient_dilate {x y δ : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    ‖zeroCoefficient (x * y) (δ * x) ρ‖ =
      x ^ ρ.re * (‖forwardDiff δ 6 (antiderivative ρ 6) y‖ / δ ^ 6) := by
  rw [zeroCoefficient_dilate hx hy hδ, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_div, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hδ]

/-! ## The denominator -/

theorem abs_im_pow_le_norm_rising_six (ρ : ℂ) :
    |ρ.im| ^ 7 ≤ ‖rising ρ 6‖ := by
  have hn (n : ℕ) : |ρ.im| ≤ ‖ρ + n‖ := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (ρ + n)
  have h0 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  norm_num [rising, norm_mul]
  calc
    |ρ.im| ^ 7 = |ρ.im| * |ρ.im| * |ρ.im| * |ρ.im| * |ρ.im| * |ρ.im| * |ρ.im| := by ring
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ * ‖ρ + 5‖ * ‖ρ + 6‖ := by
      gcongr
      · simpa using hn 1
      · simpa using hn 2
      · simpa using hn 3
      · simpa using hn 4
      · simpa using hn 5
      · simpa using hn 6

/-- On the line `Re s = −1/2`, `‖s(s+1)⋯(s+6)‖ ≥ (1/2)(1/2)(3/2)⋯(11/2) > 81`. -/
theorem norm_rising_six_ge_left {s : ℂ} (hs : s.re = -1 / 2) : (81 : ℝ) ≤ ‖rising s 6‖ := by
  have hn (n : ℕ) : |(n : ℝ) - 1 / 2| ≤ ‖s + n‖ := by
    have h := Complex.abs_re_le_norm (s + n)
    simp only [Complex.add_re, Complex.natCast_re, hs] at h
    convert h using 2
    ring
  have h0 : (1 / 2 : ℝ) ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    rw [hs] at h
    norm_num at h
    exact h
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  norm_num at h1 h2 h3 h4 h5 h6
  norm_num [rising, norm_mul]
  calc
    (81 : ℝ) ≤ (1 / 2) * (1 / 2) * (3 / 2) * (5 / 2) * (7 / 2) * (9 / 2) * (11 / 2) := by
      norm_num
    _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ * ‖s + 5‖ * ‖s + 6‖ := by
      gcongr

/-! ## A generic bound for the sixth difference -/

theorem norm_difference_le {δ y C : ℝ} (hδ : 0 ≤ δ) {ρ : ℂ}
    (hb : ∀ t ∈ Icc y (y + 6 * δ), 0 < t ∧ t ^ (ρ.re + 6) ≤ C) :
    ‖forwardDiff δ 6 (antiderivative ρ 6) y‖ ≤ 64 * C / ‖rising ρ 6‖ := by
  have h := PolynomialLowerKernel.norm_forwardDiff_le_const_on hδ (antiderivative ρ 6)
    (C / ‖rising ρ 6‖) 6 y (by
      intro t ht
      have ht' : t ∈ Icc y (y + 6 * δ) := by simpa using ht
      obtain ⟨ht0, htC⟩ := hb t ht'
      rw [antiderivative, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      have hre : (ρ + ((6 : ℕ) : ℂ)).re = ρ.re + 6 := by simp
      rw [hre]
      exact htC)
  calc
    _ ≤ 2 ^ 6 * (C / ‖rising ρ 6‖) := h
    _ = 64 * C / ‖rising ρ 6‖ := by ring

/-- The upper average: `t ∈ [1, 1 + 6δ]`, `t^{Re ρ + 6} ≤ t⁷ ≤ (1 + 6δ)⁷`. -/
theorem norm_upper_difference_le {δ : ℝ} (hδ : 0 ≤ δ) {ρ : ℂ} (hρ : ρ.re ≤ 1) :
    ‖forwardDiff δ 6 (antiderivative ρ 6) 1‖ ≤ R6 δ / ‖rising ρ 6‖ := by
  have h := norm_difference_le (y := 1) (C := (1 + 6 * δ) ^ 7) hδ (ρ := ρ) (by
    intro t ht
    have ht1 : 1 ≤ t := ht.1
    have ht0 : 0 < t := by linarith
    refine ⟨ht0, ?_⟩
    calc
      t ^ (ρ.re + 6) ≤ t ^ (7 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = t ^ (7 : ℕ) := by rw [Real.rpow_ofNat]
      _ ≤ (1 + 6 * δ) ^ 7 := pow_le_pow_left₀ ht0.le ht.2 7)
  simpa only [R6, mul_div_assoc] using h

/-- The lower average: `t ∈ [1 − 6δ, 1]`, `t^{Re ρ + 6} ≤ 1`. -/
theorem norm_lower_difference_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ6 : 6 * δ < 1) {ρ : ℂ}
    (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 6 (antiderivative ρ 6) (1 - 6 * δ)‖ ≤ R6 δ / ‖rising ρ 6‖ := by
  have h := norm_difference_le (y := 1 - 6 * δ) (C := 1) hδ (ρ := ρ) (by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : t ≤ 1 := by linarith [ht.2]
    exact ⟨ht0, Real.rpow_le_one ht0.le ht1 (by linarith)⟩)
  refine h.trans ?_
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  linarith [sixtyfour_le_R6 hδ]

private theorem high_denominator_le {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (him : ρ.im ≠ 0) :
    R6 δ / ‖rising ρ 6‖ / δ ^ 6 ≤ (R6 δ / δ ^ 6) / |ρ.im| ^ 7 := by
  have hp : 0 < |ρ.im| ^ 7 := pow_pos (abs_pos.mpr him) 7
  have hr := abs_im_pow_le_norm_rising_six ρ
  rw [div_div, div_div, mul_comm (δ ^ 6)]
  exact div_le_div_of_nonneg_left (R6_nonneg hδ.le) (by positivity)
    (mul_le_mul_of_nonneg_right hr (by positivity))

/-- **High zeros, upper average.** -/
theorem norm_zeroCoefficient_upper_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    {ρ : ℂ} (hr : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient x (δ * x) ρ‖ ≤ (R6 δ / δ ^ 6) * x ^ ρ.re / |ρ.im| ^ 7 := by
  have hd := norm_zeroCoefficient_dilate hx one_pos hδ ρ
  rw [mul_one] at hd
  rw [hd]
  have h1 : ‖forwardDiff δ 6 (antiderivative ρ 6) 1‖ / δ ^ 6 ≤ R6 δ / ‖rising ρ 6‖ / δ ^ 6 :=
    div_le_div_of_nonneg_right (norm_upper_difference_le hδ.le hr) (by positivity)
  have h2 := h1.trans (high_denominator_le hδ him)
  have hxp : 0 ≤ x ^ ρ.re := Real.rpow_nonneg hx.le _
  calc
    x ^ ρ.re * (‖forwardDiff δ 6 (antiderivative ρ 6) 1‖ / δ ^ 6) ≤
        x ^ ρ.re * ((R6 δ / δ ^ 6) / |ρ.im| ^ 7) := mul_le_mul_of_nonneg_left h2 hxp
    _ = _ := by ring

/-- **High zeros, lower average.** -/
theorem norm_zeroCoefficient_lower_le_high {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ)
    (hδ6 : 6 * δ < 1) {ρ : ℂ} (hr : 0 ≤ ρ.re) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x - 6 * (δ * x)) (δ * x) ρ‖ ≤
      (R6 δ / δ ^ 6) * x ^ ρ.re / |ρ.im| ^ 7 := by
  rw [show x - 6 * (δ * x) = x * (1 - 6 * δ) by ring,
    norm_zeroCoefficient_dilate hx (by linarith) hδ ρ]
  have h1 : ‖forwardDiff δ 6 (antiderivative ρ 6) (1 - 6 * δ)‖ / δ ^ 6 ≤
      R6 δ / ‖rising ρ 6‖ / δ ^ 6 :=
    div_le_div_of_nonneg_right (norm_lower_difference_le hδ.le hδ6 hr) (by positivity)
  have h2 := h1.trans (high_denominator_le hδ him)
  have hxp : 0 ≤ x ^ ρ.re := Real.rpow_nonneg hx.le _
  calc
    x ^ ρ.re * (‖forwardDiff δ 6 (antiderivative ρ 6) (1 - 6 * δ)‖ / δ ^ 6) ≤
        x ^ ρ.re * ((R6 δ / δ ^ 6) / |ρ.im| ^ 7) := mul_le_mul_of_nonneg_left h2 hxp
    _ = _ := by ring

/-! ## The left line `Re s = −1/2` -/

/-- `t ∈ [0.94, 1.06]` gives `t^{11/2} ≤ 1.06⁶ < 1.42`. -/
theorem norm_left_difference_le {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 6 * δ ≤ y) (hy1 : y ≤ 1) {s : ℂ} (hs : s.re = -1 / 2) :
    ‖forwardDiff δ 6 (antiderivative s 6) y‖ ≤ 91 / ‖rising s 6‖ := by
  have h := norm_difference_le (y := y) (C := 1.42) hδ.le (ρ := s) (by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have ht1 : t ≤ 1.06 := by linarith [ht.2]
    refine ⟨ht0, ?_⟩
    rw [hs]
    rcases le_or_gt t 1 with h1 | h1
    · exact (Real.rpow_le_one ht0.le h1 (by norm_num)).trans (by norm_num)
    · calc
        t ^ (-1 / 2 + 6 : ℝ) ≤ t ^ (6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1.le (by norm_num)
        _ = t ^ (6 : ℕ) := by rw [Real.rpow_ofNat]
        _ ≤ (1.06 : ℝ) ^ (6 : ℕ) := pow_le_pow_left₀ ht0.le ht1 6
        _ ≤ 1.42 := by norm_num)
  refine h.trans ?_
  apply div_le_div_of_nonneg_right (by norm_num) (norm_nonneg _)

theorem norm_zeroCoefficient_left {x δ y : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 6 * δ ≤ y) (hy1 : y ≤ 1) {s : ℂ} (hs : s.re = -1 / 2) :
    ‖zeroCoefficient (x * y) (δ * x) s‖ ≤
      x ^ (-1 / 2 : ℝ) * (91 / (δ ^ 6 * ‖rising s 6‖)) := by
  rw [norm_zeroCoefficient_dilate hx (by linarith) hδ, hs]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx.le _)
  have h := div_le_div_of_nonneg_right (norm_left_difference_le hδ hδ1 hy0 hy1 hs)
    (by positivity : (0 : ℝ) ≤ δ ^ 6)
  refine h.trans_eq ?_
  rw [div_div, mul_comm]

end TernaryGoldbach.RSBounds.SchoenfeldSexticKernel
