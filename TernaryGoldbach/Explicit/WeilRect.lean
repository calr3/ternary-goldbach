import TernaryGoldbach.Explicit.WeilPrime
import TernaryGoldbach.Explicit.XiPartial
import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# The Weil identity on a rectangle

On `[−1/2, 3/2] × [−T, T]` at a good height `T ∈ [k, k+1]` (`k ≥ 8`), for `h` entire:
`∮ (ξ'/ξ) h = 2πi Σ_{ρ inside} m_ρ h(ρ)` (`rectInt_xi_eq`). The left side folds onto the right side by
`ξ'/ξ(1 − w) = −ξ'/ξ(w)` (`left_fold`), so with `h̃(s) = h(s) + h(1 − s)`:
`2π Σ m_ρ h(ρ) = ∫_{−T}^{T} ξ'/ξ(3/2 + iy) h̃(3/2 + iy) dy + E`, where `E` comes from the horizontal
sides (`weil_rect`). For `h = H_{T₀}`, `|E| ≤ 4·MX(k)·4^m e^{2mℓ}(L(T − T₀) + L(T + T₀))`.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real Interval Topology

namespace TernaryGoldbach.Explicit

/-- The zeros of `ξ` strictly inside `[−1/2, 3/2] × [−T, T]` (counted with `mult T`). -/
noncomputable def rectZerosXi (T : ℝ) : Finset ℂ :=
  (zerosIn xiF (1 / 2) (6 * T) (6 * T / 2)).filter
    (fun u => (zT T).re < u.re ∧ u.re < (wT T).re ∧ (zT T).im < u.im ∧ u.im < (wT T).im)

/-- The good-height hypothesis of `xiF_sq_bound`. -/
def GoodH (k : ℕ) (T : ℝ) : Prop :=
  ∀ σ ∈ [[(-1 / 2 : ℝ), 3 / 2]],
    (zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0 ∧ zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0) ∧
    (‖logDeriv zetaF ((σ : ℂ) + ((T : ℝ) : ℂ) * I)‖ ≤ HkD BPz2 k ∧
      ‖logDeriv zetaF ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ HkD BPz2 k)

/-- `ξ ≠ 0` and `|ξ'/ξ| ≤ MX(k)` on the horizontal sides `σ ± iT`, `σ ∈ [−1/2, 3/2]`. -/
theorem xi_horiz {k : ℕ} (hk : 8 ≤ k) {T : ℝ} (hT : T ∈ Icc (k : ℝ) (k + 1)) (hg : GoodH k T)
    {x : ℝ} (hx : x ∈ Icc (-1 / 2 : ℝ) (3 / 2)) {y : ℝ} (hy : |y| = T) :
    xiF ((x : ℂ) + (y : ℂ) * I) ≠ 0 ∧ ‖logDeriv xiF ((x : ℂ) + (y : ℂ) * I)‖ ≤ MX k := by
  have hk' : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hT8 : 8 ≤ T := hk'.trans hT.1
  refine xiF_sq_bound hk hT hg ?_ ?_ (Or.inl ?_)
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero]
    exact hy.le
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, mul_zero,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_add, add_zero]
    exact hy

/-- **Residue theorem on the rectangle** for `ξ'/ξ · h`, `h` entire. -/
theorem rectInt_xi_eq {k : ℕ} (hk : 8 ≤ k) {T : ℝ} (hT : T ∈ Icc (k : ℝ) (k + 1)) (hg : GoodH k T)
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    rectInt (fun s => logDeriv xiF s * h s) (zT T) (wT T) =
      2 * π * I * ∑ u ∈ rectZerosXi T, (mult T u : ℂ) * h u := by
  have hk' : (8 : ℝ) ≤ k := by exact_mod_cast hk
  have hT8 : 8 ≤ T := hk'.trans hT.1
  have hR : 0 < 6 * T := by linarith
  have hrect : [[(zT T).re, (wT T).re]] ×ℂ [[(zT T).im, (wT T).im]] ⊆ ball (1 / 2 : ℂ) (6 * T / 2) := by
    intro u hu
    rw [Complex.mem_reProdIm, zT_re, wT_re, zT_im, wT_im, uIcc_of_le (by norm_num),
      uIcc_of_le (by linarith)] at hu
    rw [mem_ball, dist_eq_norm]
    have h1 : |(u - 1 / 2).re| ≤ 1 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re]
      rw [abs_le]; constructor <;> linarith [hu.1.1, hu.1.2]
    have h2 : |(u - 1 / 2).im| ≤ T := by
      simp only [Complex.sub_im, Complex.one_im, Complex.div_ofNat_im, zero_div, sub_zero]
      rw [abs_le]; constructor <;> linarith [hu.2.1, hu.2.2]
    calc ‖u - 1 / 2‖ ≤ |(u - 1 / 2).re| + |(u - 1 / 2).im| := Complex.norm_le_abs_re_add_abs_im _
      _ < 6 * T / 2 := by linarith
  have hbd : NoZerosOnSides xiF (zT T) (wT T) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun y _ => ?_, fun y _ => ?_⟩
    · rw [zT_re, wT_re, uIcc_of_le (by norm_num)] at hx
      rw [zT_im]
      have := (xi_horiz hk hT hg hx (y := -T) (by rw [abs_neg, abs_of_pos (by linarith)])).1
      simpa using this
    · rw [zT_re, wT_re, uIcc_of_le (by norm_num)] at hx
      rw [wT_im]
      exact (xi_horiz hk hT hg hx (y := T) (abs_of_pos (by linarith))).1
    · rw [wT_re]
      exact xiF_ne_zero_of_one_le_re (by simp; norm_num)
    · rw [zT_re]
      exact xiF_ne_zero_of_re_nonpos (by simp; norm_num)
  have hc : xiF (1 / 2) ≠ 0 := xiF_half_ne_zero
  have := rectInt_logDeriv_mul differentiable_xiF hR hc (z := zT T) (w := wT T)
    (by rw [zT_re, wT_re]; norm_num) (by rw [zT_im, wT_im]; linarith) hrect hbd isOpen_univ
    (subset_univ _) hh.differentiableOn
  rw [this]
  rfl

/-- The four sides of `rectInt` on `[−1/2, 3/2] × [−T, T]`. -/
theorem rectInt_zT_wT (F : ℂ → ℂ) (T : ℝ) :
    rectInt F (zT T) (wT T) =
      (∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2), F (x + ((-T : ℝ) : ℂ) * I)) -
        (∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2), F (x + (T : ℂ) * I)) +
        I * (∫ y : ℝ in (-T)..T, F (((3 / 2 : ℝ) : ℂ) + y * I)) -
        I * (∫ y : ℝ in (-T)..T, F (((-1 / 2 : ℝ) : ℂ) + y * I)) := by
  unfold rectInt
  rw [zT_re, zT_im, wT_re, wT_im, smul_eq_mul, smul_eq_mul]

/-- **The left side folds onto the right side**: `ξ'/ξ(−1/2 + iy) = −ξ'/ξ(3/2 − iy)`, `y ↦ −y`. -/
theorem left_fold (h : ℂ → ℂ) (T : ℝ) :
    ∫ y : ℝ in (-T)..T, logDeriv xiF (((-1 / 2 : ℝ) : ℂ) + y * I) * h (((-1 / 2 : ℝ) : ℂ) + y * I) =
      -∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * h (1 - (((3 / 2 : ℝ) : ℂ) + y * I)) := by
  set f : ℝ → ℂ := fun y => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * h (1 - (((3 / 2 : ℝ) : ℂ) + y * I))
    with hf
  have hc := intervalIntegral.integral_comp_neg (a := -T) (b := T) f
  rw [neg_neg] at hc
  rw [← hc, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun y _ => ?_
  simp only [hf]
  have e1 : (1 : ℂ) - (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = ((-1 / 2 : ℝ) : ℂ) + y * I := by
    push_cast; ring
  have e2 : (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = 1 - (((-1 / 2 : ℝ) : ℂ) + y * I) := by
    push_cast; ring
  rw [e1, e2, logDeriv_xiF_one_sub]
  ring

/-- `ξ'/ξ` is continuous on `ℜs = 3/2`. -/
theorem continuous_logDeriv_xiF_line : Continuous fun y : ℝ => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have h : xiF (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := xiF_ne_zero_of_one_le_re (by simp; norm_num)
  exact (continuousAt_logDeriv_xiF h).comp (f := fun y : ℝ => ((3 / 2 : ℝ) : ℂ) + y * I) (by fun_prop)

/-- **The Weil identity on a rectangle**, before the limit `T → ∞`. -/
theorem weil_rect {k : ℕ} (hk : 8 ≤ k) {T : ℝ} (hT : T ∈ Icc (k : ℝ) (k + 1)) (hg : GoodH k T)
    {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    2 * π * ∑ u ∈ rectZerosXi T, (mult T u : ℂ) * h u -
        ∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) *
          (h (((3 / 2 : ℝ) : ℂ) + y * I) + h (1 - (((3 / 2 : ℝ) : ℂ) + y * I))) =
      -I * ((∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2), logDeriv xiF (x + ((-T : ℝ) : ℂ) * I) * h (x + ((-T : ℝ) : ℂ) * I)) -
        ∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2), logDeriv xiF (x + (T : ℂ) * I) * h (x + (T : ℂ) * I)) := by
  have hR := rectInt_xi_eq hk hT hg hh
  rw [rectInt_zT_wT, left_fold] at hR
  have hc1 : IntervalIntegrable (fun y : ℝ => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) *
      h (((3 / 2 : ℝ) : ℂ) + y * I)) volume (-T) T :=
    (continuous_logDeriv_xiF_line.mul (hh.continuous.comp (by fun_prop))).intervalIntegrable _ _
  have hc2 : IntervalIntegrable (fun y : ℝ => logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) *
      h (1 - (((3 / 2 : ℝ) : ℂ) + y * I))) volume (-T) T :=
    (continuous_logDeriv_xiF_line.mul (hh.continuous.comp (by fun_prop))).intervalIntegrable _ _
  have hsplit : (∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) *
      (h (((3 / 2 : ℝ) : ℂ) + y * I) + h (1 - (((3 / 2 : ℝ) : ℂ) + y * I)))) =
      (∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * h (((3 / 2 : ℝ) : ℂ) + y * I)) +
      ∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * h (1 - (((3 / 2 : ℝ) : ℂ) + y * I)) := by
    rw [← intervalIntegral.integral_add hc1 hc2]
    exact intervalIntegral.integral_congr fun y _ => by ring
  rw [hsplit]
  set Sg := ∑ u ∈ rectZerosXi T, (mult T u : ℂ) * h u
  set A := ∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * h (((3 / 2 : ℝ) : ℂ) + y * I)
  set B := ∫ y : ℝ in (-T)..T, logDeriv xiF (((3 / 2 : ℝ) : ℂ) + y * I) * h (1 - (((3 / 2 : ℝ) : ℂ) + y * I))
  have hI2 : I * I = -1 := Complex.I_mul_I
  linear_combination I * hR + (2 * π * Sg - A - B) * hI2

/-- **The horizontal sides** for `h = H_{T₀}`: each is at most `2·MX(k)·4^m e^{2mℓ} L(±T − T₀)`. -/
theorem norm_horiz_le {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {m : ℕ} (hm : 1 ≤ m) (T₀ : ℝ)
    {k : ℕ} (hk : 8 ≤ k) {T : ℝ} (hT : T ∈ Icc (k : ℝ) (k + 1)) (hg : GoodH k T) {y : ℝ} (hy : |y| = T) :
    ‖∫ x : ℝ in (-1 / 2 : ℝ)..(3 / 2), logDeriv xiF (x + (y : ℂ) * I) * WH ℓ m T₀ (x + (y : ℂ) * I)‖ ≤
      2 * (MX k * (4 ^ m * Real.exp (2 * m * ℓ) * lor (y - T₀))) := by
  have hb : ∀ x ∈ Ι (-1 / 2 : ℝ) (3 / 2), ‖logDeriv xiF (x + (y : ℂ) * I) * WH ℓ m T₀ (x + (y : ℂ) * I)‖ ≤
      MX k * (4 ^ m * Real.exp (2 * m * ℓ) * lor (y - T₀)) := by
    intro x hx
    rw [uIoc_of_le (by norm_num)] at hx
    have hx' : x ∈ Icc (-1 / 2 : ℝ) (3 / 2) := ⟨hx.1.le, hx.2⟩
    rw [norm_mul]
    refine mul_le_mul (xi_horiz hk hT hg hx' hy).2 ?_ (norm_nonneg _) (MX_nonneg k)
    refine (norm_WH_le_exp hℓ0 hℓ1 hm T₀ _).trans ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
      zero_add]
    have habs : |x - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have he : Real.exp (2 * m * ℓ * |x - 1 / 2|) ≤ Real.exp (2 * m * ℓ) :=
      Real.exp_le_exp.2 (mul_le_of_le_one_right (by positivity) habs)
    have hl := (lor_pos (y - T₀)).le
    calc 4 ^ m * Real.exp (2 * m * ℓ * |x - 1 / 2|) * lor (y - T₀) ≤
        4 ^ m * Real.exp (2 * m * ℓ) * lor (y - T₀) := by gcongr
      _ = _ := rfl
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show |(3 / 2 : ℝ) - -1 / 2| = 2 by norm_num] at this
  linarith

end TernaryGoldbach.Explicit
