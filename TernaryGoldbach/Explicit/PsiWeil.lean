import TernaryGoldbach.Explicit.PsiLarge
import TernaryGoldbach.Explicit.WeilNumC

variable [Fact TernaryGoldbach.RHUpTo]

/-!
# `ψ(x)` from the explicit formula with the Weil-window line bound

As `SsumG_gsm_err`, but the line zeros `|γ| ≤ 3·10¹⁰` are bounded by `line_sum_num`:
`|Σ Λ(n) φ(n/x) − M(1) x| ≤ ErrW = √x·LineW + x·TailB + x^{−1/2} V/(2π)` for `φ = gsm a b δ` and
`3·10⁻¹⁰ ≤ δ ≤ 1/208`, where `LineW = e^{δ²/8}(e^{a/2} + e^{b/2})(JW(δ) + e^{−δ²10²⁰/2} LW)`.
The sandwiches `psi_upper_of_err`, `psi_lower_of_err` (`PsiLarge.lean`) take any such error bound;
`psi_upper_W`, `psi_lower_W` apply them.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-- The Weil-window line constant. -/
noncomputable def LineW (a b δ : ℝ) : ℝ :=
  Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) * (JW δ + Real.exp (-(δ ^ 2 * 1e20 / 2)) * LW)

/-- The total explicit-formula error with the Weil-window line bound. -/
noncomputable def ErrW (a b δ x : ℝ) : ℝ :=
  √x * LineW a b δ + x * TailB a δ + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π)

/-- **The explicit-formula bound for the smoothed sum**, Weil-window version. -/
theorem SsumG_gsm_errW {a b δ x : ℝ} (hδ0 : 3e-10 ≤ δ) (hδ1 : δ ≤ 1 / 208) (hab : b ≤ a) (hb : b ≤ 0)
    (hx : 1 ≤ x) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤ ErrW a b δ x := by
  have hδ : 0 < δ := lt_of_lt_of_le (by norm_num) hδ0
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineW a b δ + x * TailB a δ := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ 3e10)]
    refine add_le_add ?_ ?_
    · -- the line zeros
      set S := Z.filter (fun u => |u.im| ≤ 3e10) with hS
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact rh_upto u hz hr1 hr2 hu2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (line_sum_num hδ0 hδ1 a b T) (Real.sqrt_nonneg _)
    · -- zeros above `3·10¹⁰`
      set S := Z.filter (fun u => ¬ |u.im| ≤ 3e10) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have him : ∀ u ∈ S, 3e10 < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by norm_num) hδ hb hx S hSZ him
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineW a b δ + x * TailB a δ :=
    le_of_tendsto' ((continuous_norm.tendsto _).comp hlim) fun k => hbound (Tk k)
  have h2 : ‖(1 / (2 * π) : ℂ) * I0‖ ≤ x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π) := by
    rw [norm_mul]
    have : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [this, div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (norm_integral_hZeta_gsm hδ hab hx0) (by positivity)
  have e : SsumG (1 : DirichletCharacter ℂ 1) φ x - Mg a b δ 1 * x =
      -((mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0) +
        (1 / (2 * π) : ℂ) * I0) := by rw [hM]; ring
  rw [e, norm_neg, ErrW]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem tsum_gsm_leW {a b δ x : ℝ} (hδ0 : 3e-10 ≤ δ) (hδ1 : δ ≤ 1 / 208) (hab : b ≤ a) (hb : b ≤ 0)
    (hx : 1 ≤ x) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤
      ErrW a b δ x := by
  have h := SsumG_gsm_errW hδ0 hδ1 hab hb hx
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **Upper bound for `ψ`**, Weil-window version. -/
theorem psi_upper_W {δ K y0 x : ℝ} (hδ0 : 3e-10 ≤ δ) (hδ1 : δ ≤ 1 / 208) (hK : 0 ≤ K)
    (hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1) (hy0 : 0 < y0) (hx : 1 ≤ x) (hYx : y0 * Real.exp (K * δ) ≤ x) :
    psiR x ≤ 4 * (y0 * Real.exp (K * δ)) +
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrW (K * δ) (Real.log (y0 / x)) δ x) /
        (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
  have hδ : 0 < δ := lt_of_lt_of_le (by norm_num) hδ0
  have hx0 : 0 < x := by linarith
  have hb : Real.log (y0 / x) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hx0).2
    (le_trans (le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))) hYx))
  have hab : Real.log (y0 / x) ≤ K * δ := hb.trans (by positivity)
  exact psi_upper_of_err hδ hK hK1 hy0 hx hYx (tsum_gsm_leW hδ0 hδ1 hab hb hx)

/-- **Lower bound for `ψ`**, Weil-window version. -/
theorem psi_lower_W {δ K y0 x : ℝ} (hδ0 : 3e-10 ≤ δ) (hδ1 : δ ≤ 1 / 208) (hKδ : δ ≤ K) (hy0 : 0 < y0)
    (hx : 1 ≤ x) (hb : Real.log (y0 / x) ≤ -(K * δ)) :
    Real.exp (-(K * δ)) * x - 2 * y0 - ErrW (-(K * δ)) (Real.log (y0 / x)) δ x -
      4 * x * Real.exp (-(K ^ 2 / 2)) ≤ psiR x := by
  have hδ : 0 < δ := lt_of_lt_of_le (by norm_num) hδ0
  have hx0 : 0 < x := by linarith
  have hb0 : Real.log (y0 / x) ≤ 0 := hb.trans (by
    have : 0 ≤ K * δ := mul_nonneg (hδ.le.trans hKδ) hδ.le
    linarith)
  exact psi_lower_of_err hδ (hδ1.trans (by norm_num)) hKδ hy0 hx hb (tsum_gsm_leW hδ0 hδ1 hb hb0 hx)

end TernaryGoldbach.Explicit
