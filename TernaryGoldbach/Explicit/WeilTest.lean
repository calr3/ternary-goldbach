import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The test function for the Weil explicit formula

`B(z) = (2 sin(ℓz)/z)^m = (2ℓ · sinc(ℓz))^m` (with `sinc = dslope sin 0`, entire) and
`H_T(s) = B(−i(s − ½) − T)²`. On the critical line `H_T(½ + ir) = B(r − T)² ≥ 0`, and
`|H_T(σ + it)| ≤ ((2ℓ)^m e^{mℓ|σ − ½|})²`, `≤ (2e^{ℓ|σ − ½|}/|t − T|)^{2m}`.

The Fourier transform of `B²` is supported in `[−2mℓ, 2mℓ]`; with `2mℓ < log 2` the prime side of
the explicit formula vanishes (`Explicit/WeilPrime.lean`).
-/

open Complex
open scoped Real

namespace TernaryGoldbach.Explicit

/-! ### `sin`, `cos` and `sinc` -/

theorem norm_sin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h2 := Complex.two_sin (x := w)
  have hn : ‖2 * Complex.sin w‖ ≤ Real.exp w.im + Real.exp (-w.im) := by
    rw [h2, norm_mul, Complex.norm_I, mul_one]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1 <;> simp
  rw [norm_mul, Complex.norm_two] at hn
  have h1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h3 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

theorem norm_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h2 := Complex.two_cos (x := w)
  have hn : ‖2 * Complex.cos w‖ ≤ Real.exp (-w.im) + Real.exp w.im := by
    rw [h2]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1 <;> simp
  rw [norm_mul, Complex.norm_two] at hn
  have h1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  have h3 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  linarith

/-- `|sin w| ≤ |w| e^{|ℑw|}`, from `sin w = ∫₀¹ w cos(tw) dt`. -/
theorem norm_sin_le_mul_exp (w : ℂ) : ‖Complex.sin w‖ ≤ ‖w‖ * Real.exp |w.im| := by
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => Complex.sin ((t : ℂ) * w))
      (Complex.cos ((t : ℂ) * w) * w) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * w) w t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const w
    exact (Complex.hasDerivAt_sin _).comp t h1
  have hc : Continuous fun t : ℝ => Complex.cos ((t : ℂ) * w) * w := by fun_prop
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.sin_zero,
    sub_zero] at hI
  rw [← hI]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖Complex.cos ((t : ℂ) * w) * w‖ ≤ ‖w‖ * Real.exp |w.im| := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ((norm_cos_le_exp _).trans (Real.exp_le_exp.2 ?_)) (norm_nonneg _)
    have : ((t : ℂ) * w).im = t * w.im := by simp
    rw [this, abs_mul, abs_of_pos ht.1]
    exact mul_le_of_le_one_left (abs_nonneg _) ht.2
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

/-- The entire function `sinc w = sin w / w` (`= 1` at `0`). -/
noncomputable def sincC (w : ℂ) : ℂ := dslope Complex.sin 0 w

theorem differentiable_sincC : Differentiable ℂ sincC := by
  have h := (differentiableOn_dslope (f := Complex.sin) (s := Set.univ) (c := 0)
    Filter.univ_mem).2 Complex.differentiable_sin.differentiableOn
  exact fun w => (h w (Set.mem_univ w)).differentiableAt Filter.univ_mem

theorem sincC_of_ne {w : ℂ} (hw : w ≠ 0) : sincC w = Complex.sin w / w := by
  rw [sincC, dslope_of_ne _ hw, slope_def_field, Complex.sin_zero, sub_zero, sub_zero]

theorem sincC_zero : sincC 0 = 1 := by
  rw [sincC, dslope_same, Complex.deriv_sin, Complex.cos_zero]

theorem norm_sincC_le (w : ℂ) : ‖sincC w‖ ≤ Real.exp |w.im| := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [sincC_zero]
  · rw [sincC_of_ne hw, norm_div]
    have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
    rw [div_le_iff₀ hw0, mul_comm]
    exact norm_sin_le_mul_exp w

theorem norm_sincC_le_div {w : ℂ} (hw : w ≠ 0) : ‖sincC w‖ ≤ Real.exp |w.im| / ‖w‖ := by
  rw [sincC_of_ne hw, norm_div]
  exact div_le_div_of_nonneg_right (norm_sin_le_exp w) (norm_nonneg _)

theorem sincC_ofReal_im (x : ℝ) : (sincC x).im = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [sincC_zero]
  · have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    rw [sincC_of_ne hx', ← Complex.ofReal_sin, ← Complex.ofReal_div]
    exact Complex.ofReal_im _

/-! ### `B` and `H` -/

/-- `B(z) = (2ℓ · sinc(ℓz))^m = (2 sin(ℓz)/z)^m`. -/
noncomputable def WB (ℓ : ℝ) (m : ℕ) (z : ℂ) : ℂ := (2 * ℓ * sincC (ℓ * z)) ^ m

/-- `H_T(s) = B(−i(s − ½) − T)²`. -/
noncomputable def WH (ℓ : ℝ) (m : ℕ) (T : ℝ) (s : ℂ) : ℂ := WB ℓ m (-I * (s - 1 / 2) - T) ^ 2

theorem differentiable_WB (ℓ : ℝ) (m : ℕ) : Differentiable ℂ (WB ℓ m) := by
  unfold WB
  exact ((differentiable_const _).mul (differentiable_sincC.comp
    ((differentiable_const _).mul differentiable_id))).pow m

theorem differentiable_WH (ℓ : ℝ) (m : ℕ) (T : ℝ) : Differentiable ℂ (WH ℓ m T) := by
  unfold WH
  exact ((differentiable_WB ℓ m).comp (((differentiable_const _).mul
    (differentiable_id.sub (differentiable_const _))).sub (differentiable_const _))).pow 2

theorem norm_WB_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (m : ℕ) (z : ℂ) :
    ‖WB ℓ m z‖ ≤ (2 * ℓ * Real.exp (ℓ * |z.im|)) ^ m := by
  rw [WB, norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
  rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hℓ]
  refine mul_le_mul_of_nonneg_left ((norm_sincC_le _).trans (le_of_eq ?_)) (by positivity)
  congr 1
  rw [show ((ℓ : ℂ) * z).im = ℓ * z.im by simp, abs_mul, abs_of_nonneg hℓ]

theorem norm_WB_le_div {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖WB ℓ m z‖ ≤ (2 * Real.exp (ℓ * |z.im|) / ‖z‖) ^ m := by
  rw [WB, norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
  have hℓz : (ℓ : ℂ) * z ≠ 0 := mul_ne_zero (by exact_mod_cast hℓ.ne') hz
  rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
  have h1 := norm_sincC_le_div hℓz
  rw [show ((ℓ : ℂ) * z).im = ℓ * z.im by simp, abs_mul, abs_of_pos hℓ, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hℓ.le] at h1
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  calc 2 * ℓ * ‖sincC (ℓ * z)‖ ≤ 2 * ℓ * (Real.exp (ℓ * |z.im|) / (ℓ * ‖z‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * Real.exp (ℓ * |z.im|) / ‖z‖ := by field_simp

/-- `B` is real on the real line. -/
theorem WB_ofReal_im (ℓ : ℝ) (m : ℕ) (x : ℝ) : (WB ℓ m x).im = 0 := by
  have hc : (ℓ : ℂ) * x = ((ℓ * x : ℝ) : ℂ) := by push_cast; ring
  have hs : sincC ((ℓ * x : ℝ) : ℂ) = (((sincC ((ℓ * x : ℝ) : ℂ)).re : ℝ) : ℂ) :=
    Complex.ext (by rw [Complex.ofReal_re]) (by rw [sincC_ofReal_im, Complex.ofReal_im])
  rw [WB, hc, hs, show (2 : ℂ) * ℓ * (((sincC ((ℓ * x : ℝ) : ℂ)).re : ℝ) : ℂ) =
    ((2 * ℓ * (sincC ((ℓ * x : ℝ) : ℂ)).re : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_pow]
  exact Complex.ofReal_im _

/-- The argument of `B` in `H_T`: `−i(s − ½) − T = (t − T) + i(½ − σ)`. -/
theorem WH_arg_re (T : ℝ) (s : ℂ) : (-I * (s - 1 / 2) - T).re = s.im - T := by simp

theorem WH_arg_im (T : ℝ) (s : ℂ) : (-I * (s - 1 / 2) - T).im = 1 / 2 - s.re := by simp

/-- **On the critical line**, `H_T(½ + ir) = B(r − T)²`, a nonnegative real. -/
theorem WH_line (ℓ : ℝ) (m : ℕ) (T r : ℝ) :
    WH ℓ m T (1 / 2 + r * I) = WB ℓ m ((r - T : ℝ) : ℂ) ^ 2 := by
  rw [WH]
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem WH_line_im (ℓ : ℝ) (m : ℕ) (T r : ℝ) : (WH ℓ m T (1 / 2 + r * I)).im = 0 := by
  rw [WH_line, sq, Complex.mul_im, WB_ofReal_im]; ring

theorem WH_line_re_nonneg (ℓ : ℝ) (m : ℕ) (T r : ℝ) : 0 ≤ (WH ℓ m T (1 / 2 + r * I)).re := by
  rw [WH_line, sq, Complex.mul_re, WB_ofReal_im]
  nlinarith [sq_nonneg (WB ℓ m ((r - T : ℝ) : ℂ)).re]

/-- `|H_T(s)| ≤ ((2ℓ)^m e^{mℓ|σ − ½|})²`. -/
theorem norm_WH_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (m : ℕ) (T : ℝ) (s : ℂ) :
    ‖WH ℓ m T s‖ ≤ ((2 * ℓ * Real.exp (ℓ * |s.re - 1 / 2|)) ^ m) ^ 2 := by
  rw [WH, norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_WB_le hℓ m _).trans (le_of_eq ?_)) 2
  rw [WH_arg_im, abs_sub_comm]

/-- `|H_T(σ + it)| ≤ (2e^{ℓ|σ − ½|}/|t − T|)^{2m}` for `t ≠ T`. -/
theorem norm_WH_le_div {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℕ) (T : ℝ) {s : ℂ} (hs : s.im ≠ T) :
    ‖WH ℓ m T s‖ ≤ ((2 * Real.exp (ℓ * |s.re - 1 / 2|) / |s.im - T|) ^ m) ^ 2 := by
  set z := -I * (s - 1 / 2) - T with hz
  have hzre : z.re = s.im - T := WH_arg_re T s
  have hz0 : z ≠ 0 := by
    intro h; apply hs; have := congrArg Complex.re h; rw [hzre] at this; simp at this; linarith
  have hnz : |s.im - T| ≤ ‖z‖ := hzre ▸ Complex.abs_re_le_norm z
  have hpos : 0 < |s.im - T| := abs_pos.2 (sub_ne_zero.2 hs)
  rw [WH, norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_WB_le_div hℓ m hz0).trans ?_) 2
  refine pow_le_pow_left₀ (by positivity) ?_ m
  rw [WH_arg_im, abs_sub_comm]
  exact div_le_div_of_nonneg_left (by positivity) hpos hnz

end TernaryGoldbach.Explicit
