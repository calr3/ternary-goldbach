import TernaryGoldbach.Explicit.PsiLarge
import TernaryGoldbach.Explicit.WeilNumC

/-!
# `ψ(x)` from the explicit formula with the Weil-window line bound

As `SsumG_gsm_errH`, but the line zeros `|γ| ≤ Y₁` are bounded by Weil windows (`line_sum_numH`) and
those in `(Y₁, H]` by Jensen windows times `e^{−δ²Y₁²/2}`, given `RHBelow H`:
`|Σ Λ(n) φ(n/x) − M(1) x| ≤ ErrWH = √x·LineWH + x·TailBH + x^{−1/2} V/(2π)` for `φ = gsm a b δ`
(`SsumG_gsm_errWH`). The sandwiches `psi_upper_of_err`, `psi_lower_of_err` (`PsiLarge.lean`) take
any such error bound; `psi_upper_WH`, `psi_lower_WH` apply them.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

/-- The Weil-window line constant at RH height `H`, windows up to `Y₁`. -/
noncomputable def LineWH (a b δ Y₁ H : ℝ) : ℝ :=
  Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + Real.exp (b / 2)) *
    (JW δ + Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H)

/-- The total explicit-formula error with the Weil-window line bound, at RH height `H`. -/
noncomputable def ErrWH (a b δ Y₁ H x : ℝ) : ℝ :=
  √x * LineWH a b δ Y₁ H + x * TailBH a δ H + x ^ (-(1 / 2) : ℝ) * Vg a b δ / (2 * π)

/-- **The explicit-formula bound for the smoothed sum**, Weil-window version, under RH up to
`H ∈ [10⁸, 3·10¹⁰]` (windows for `|γ| ≤ Y₁`, `1/2 ≤ Y₁`, `Y₁ + 13 ≤ H/2`, `3/Y₁ ≤ δ ≤ 1/208`). -/
theorem SsumG_gsm_errWH {a b δ x H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10)
    (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + 13 ≤ H / 2) (hδ0 : 3 / Y₁ ≤ δ) (hδ1 : δ ≤ 1 / 208) (hab : b ≤ a)
    (hb : b ≤ 0) (hx : 1 ≤ x) :
    ‖SsumG (1 : DirichletCharacter ℂ 1) (fun u => (gsm a b δ u : ℂ)) x - Mg a b δ 1 * x‖ ≤
      ErrWH a b δ Y₁ H x := by
  have hδ : 0 < δ := lt_of_lt_of_le (by have : 0 < Y₁ := by linarith
                                        positivity) hδ0
  have hx0 : 0 < x := by linarith
  set φ : ℝ → ℂ := fun u => (gsm a b δ u : ℂ) with hφ
  have hgood := goodSmoothing_gsm hδ hab
  have hM : mellin φ = Mg a b δ := funext (mellin_gsm hδ hab)
  obtain ⟨Tk, -, hlim⟩ := explicit_formula_zeta hgood hx0
  set I0 := ∫ y : ℝ, hZeta φ x (((-1 / 2 : ℝ) : ℂ) + y * I) with hI0
  have hbound : ∀ T : ℝ, ‖∑ u ∈ zerosRectD zetaF T, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
      √x * LineWH a b δ Y₁ H + x * TailBH a δ H := by
    intro T
    set Z := zerosRectD zetaF T with hZ
    set m : ℂ → ℝ := fun u => (multRectD zetaF T u : ℝ) with hm
    have h1 : ‖∑ u ∈ Z, (multRectD zetaF T u : ℂ) * (mellin φ u * (x : ℂ) ^ u)‖ ≤
        ∑ u ∈ Z, m u * (‖Mg a b δ u‖ * x ^ u.re) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_natCast, norm_cpow_x hx0, hM]
    refine h1.trans ?_
    rw [← Finset.sum_filter_add_sum_filter_not Z (fun u => |u.im| ≤ H)]
    refine add_le_add ?_ ?_
    · -- the line zeros
      set S := Z.filter (fun u => |u.im| ≤ H) with hS
      have hre : ∀ u ∈ S, u.re = 1 / 2 := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.1 hu
        obtain ⟨hz, hr1, hr2, -⟩ := zerosRectD_zetaF_strip hu1
        exact hRH u hz hr1 hr2 hu2
      have heq : ∀ u ∈ S, m u * (‖Mg a b δ u‖ * x ^ u.re) = √x * (m u * ‖Mg a b δ u‖) := by
        intro u hu
        rw [hre u hu, ← Real.sqrt_eq_rpow]; ring
      rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (line_sum_numH hRH hH1 hH2 hY₁0 hY₁ hδ0 hδ1 a b T) (Real.sqrt_nonneg _)
    · -- zeros above `3·10¹⁰`
      set S := Z.filter (fun u => ¬ |u.im| ≤ H) with hS
      have hSZ : S ⊆ Z := Finset.filter_subset _ _
      have him : ∀ u ∈ S, H < |u.im| := fun u hu => not_le.1 (Finset.mem_filter.1 hu).2
      exact tail_sum_gauss (by linarith) hδ hb hx S hSZ him
  have h1 : ‖mellin φ 1 * x - SsumG (1 : DirichletCharacter ℂ 1) φ x - (1 / (2 * π) : ℂ) * I0‖ ≤
      √x * LineWH a b δ Y₁ H + x * TailBH a δ H :=
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
  rw [e, norm_neg, ErrWH]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem tsum_gsm_leWH {a b δ x H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10)
    (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + 13 ≤ H / 2) (hδ0 : 3 / Y₁ ≤ δ) (hδ1 : δ ≤ 1 / 208) (hab : b ≤ a)
    (hb : b ≤ 0) (hx : 1 ≤ x) :
    |∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x| ≤
      ErrWH a b δ Y₁ H x := by
  have h := SsumG_gsm_errWH hRH hH1 hH2 hY₁0 hY₁ hδ0 hδ1 hab hb hx
  rw [SsumG_one_ofReal, Mg_one] at h
  rw [show ((∑' n : ℕ, Λ n * gsm a b δ (n / x) : ℝ) : ℂ) -
      ((Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) : ℝ) : ℂ) * (x : ℂ) =
      ((∑' n : ℕ, Λ n * gsm a b δ (n / x) - Real.exp (δ ^ 2 / 2) * (Real.exp a - Real.exp b) * x : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **Upper bound for `ψ`**, Weil-window version, under RH up to `H`. -/
theorem psi_upper_WH {δ K y0 x H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10)
    (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + 13 ≤ H / 2) (hδ0 : 3 / Y₁ ≤ δ) (hδ1 : δ ≤ 1 / 208) (hK : 0 ≤ K)
    (hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1) (hy0 : 0 < y0) (hx : 1 ≤ x) (hYx : y0 * Real.exp (K * δ) ≤ x) :
    psiR x ≤ 4 * (y0 * Real.exp (K * δ)) +
      (Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrWH (K * δ) (Real.log (y0 / x)) δ Y₁ H x) /
        (1 - 2 * Real.exp (-(K ^ 2 / 2))) := by
  have hδ : 0 < δ := lt_of_lt_of_le (by have : 0 < Y₁ := by linarith
                                        positivity) hδ0
  have hx0 : 0 < x := by linarith
  have hb : Real.log (y0 / x) ≤ 0 := Real.log_nonpos (by positivity) ((div_le_one hx0).2
    (le_trans (le_mul_of_one_le_right hy0.le (Real.one_le_exp (by positivity))) hYx))
  have hab : Real.log (y0 / x) ≤ K * δ := hb.trans (by positivity)
  exact psi_upper_of_err hδ hK hK1 hy0 hx hYx (tsum_gsm_leWH hRH hH1 hH2 hY₁0 hY₁ hδ0 hδ1 hab hb hx)

/-- **Lower bound for `ψ`**, Weil-window version, under RH up to `H`. -/
theorem psi_lower_WH {δ K y0 x H Y₁ : ℝ} (hRH : RHBelow H) (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10)
    (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + 13 ≤ H / 2) (hδ0 : 3 / Y₁ ≤ δ) (hδ1 : δ ≤ 1 / 208) (hKδ : δ ≤ K)
    (hy0 : 0 < y0) (hx : 1 ≤ x) (hb : Real.log (y0 / x) ≤ -(K * δ)) :
    Real.exp (-(K * δ)) * x - 2 * y0 - ErrWH (-(K * δ)) (Real.log (y0 / x)) δ Y₁ H x -
      4 * x * Real.exp (-(K ^ 2 / 2)) ≤ psiR x := by
  have hδ : 0 < δ := lt_of_lt_of_le (by have : 0 < Y₁ := by linarith
                                        positivity) hδ0
  have hx0 : 0 < x := by linarith
  have hb0 : Real.log (y0 / x) ≤ 0 := hb.trans (by
    have : 0 ≤ K * δ := mul_nonneg (hδ.le.trans hKδ) hδ.le
    linarith)
  exact psi_lower_of_err hδ (hδ1.trans (by norm_num)) hKδ hy0 hx hb
    (tsum_gsm_leWH hRH hH1 hH2 hY₁0 hY₁ hδ0 hδ1 hb hb0 hx)

end TernaryGoldbach.Explicit
