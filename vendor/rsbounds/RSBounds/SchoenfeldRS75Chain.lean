import RSBounds.SchoenfeldRS75BudgetBounds
import RSBounds.RosserSchoenfeld1975

/-!
# The RS75 `b = 23` chain at every `x ≥ 1`

`RosserSchoenfeld1975` proves `|ψ(x) − x| < 0.00020211 x` for `x ≥ e^23` in three steps: the
quartic explicit formula with the actual finite zero sums (`PolynomialPsiFromZeroSums`), the bound
for those sums (`QuarticZeroSumBound.norm_sum_le_budget`, valid for every `x ≥ 1`), and a scalar
evaluation at `√x = 98715`. The threshold `e^23` enters only through the left-remainder bound
`< 0.1` (`PolynomialRemainderBound.norm_upper_leftRemainder_lt`). The underlying bound
`25000/(π√x)` (`PolynomialRemainderBound.norm_leftRemainder_le`) holds for every `x > 0`.

Keeping that bound gives, for every `x ≥ 1` (`psi_relative_le`),

    |ψ(x) − x| / x ≤ 2δ + K + Q/√x + (K + log 2π + 25000/(π√x))/x,     δ = 0.0000211,

with `K = highWeight < 3.21·10⁻⁶` and `Q = sqrtCoefficient < 15.47`
(`SchoenfeldRS75BudgetBounds`). For `√x ≥ L > 0` (`psi_error_le`):

    |ψ(x) − x| ≤ (0.0000422 + 3.21·10⁻⁶ + 15.47/L + 6/L² + 8000/L³) x.

The proofs repeat those of `PolynomialPsiFromZeroSums.psi_error_of_eventually_bounded_zero_sums`
and `PsiTable1975.psi_error_lt` with this remainder bound; no RS75 file is changed. Zeros above
`1894438.5122` enter only through `K`, as in RS75; no zero-free region is used.
-/

open Complex Finset Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.SchoenfeldRS75Chain

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialAveraged QuarticFirst29BudgetNumerics
open PolynomialPsi PolynomialRemainderBound PolynomialPsiFromZeroSums

/-- `PolynomialPsiFromZeroSums.psi_error_of_eventually_bounded_zero_sums` for every `x > 0`, with
the left remainders bounded by `25000/(π√x)` instead of `0.1`. -/
theorem psi_error_of_eventually_bounded_zero_sums_pos {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x zeroBudget : ℝ} (hx0 : 0 < x)
    (hupper : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) *
          zeroCoefficient x (0.0000211 * x) ρ‖ ≤ x * zeroBudget)
    (hlower : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) *
          zeroCoefficient (x - 4 * (0.0000211 * x)) (0.0000211 * x) ρ‖ ≤
            x * zeroBudget) :
    |Chebyshev.psi x - x| / x ≤
      2 * (0.0000211 : ℝ) +
        (Real.log (2 * Real.pi) + 25000 / (Real.pi * Real.sqrt x)) / x + zeroBudget := by
  have hh : 0 < (0.0000211 : ℝ) * x := by positivity
  have hshift : 4 * ((0.0000211 : ℝ) * x) < x := by linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 4 * ((0.0000211 : ℝ) * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hrem : ∀ y : ℝ, 1 - 4 * (0.0000211 : ℝ) ≤ y → y ≤ 1 →
      ‖leftRemainder (x * y) (0.0000211 * x)‖ ≤ 25000 / (Real.pi * Real.sqrt x) := by
    intro y hy0 hy1
    rw [Real.sqrt_eq_rpow]
    exact norm_leftRemainder_le hx0 hy0 hy1
  have hru : ‖leftRemainder x (0.0000211 * x)‖ ≤ 25000 / (Real.pi * Real.sqrt x) := by
    simpa only [mul_one] using hrem 1 (by norm_num) le_rfl
  have hrl : ‖leftRemainder (x - 4 * (0.0000211 * x)) (0.0000211 * x)‖ ≤
      25000 / (Real.pi * Real.sqrt x) := by
    rw [show x - 4 * (0.0000211 * x) = x * (1 - 4 * (0.0000211 : ℝ)) by ring]
    exact hrem _ le_rfl (by norm_num)
  have hup := upper_error_of_eventually_bounded_zero_sums hT hx0 hh hN hupper hru
  have hlo := lower_error_of_eventually_bounded_zero_sums hT hshift hh hNx hlower hrl
  have hpsi := psi_error_of_polynomial_errors hx0.le hh hN hup hlo
  calc
    _ ≤ (x * zeroBudget + 25000 / (Real.pi * Real.sqrt x) + Real.log (2 * Real.pi) +
          2 * (0.0000211 * x)) / x :=
      div_le_div_of_nonneg_right hpsi hx0.le
    _ = _ := by
      generalize 25000 / (Real.pi * Real.sqrt x) = r
      field_simp [hx0.ne']
      ring

/-- **The RS75 `b = 23` chain at every `x ≥ 1`**, before any numerical evaluation. -/
theorem psi_relative_le (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx1 : 1 ≤ x) :
    |Chebyshev.psi x - x| / x ≤
      2 * (0.0000211 : ℝ) + highWeight + sqrtCoefficient / Real.sqrt x +
        (highWeight + Real.log (2 * Real.pi) + 25000 / (Real.pi * Real.sqrt x)) / x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  have hlarge : ∀ᶠ k : ℕ in atTop, (A : ℝ) < T k := by
    filter_upwards [eventually_ge_atTop (1894439 : ℕ)] with k hk
    have hkR : (1894439 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have ht := (hT.mem k).1
    have hA' : (A : ℝ) < 1894439 := by norm_num [A]
    linarith
  let zeroBudget : ℝ := highWeight + sqrtCoefficient / Real.sqrt x + highWeight / x
  have hnorm (lower : Bool) : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * PolynomialZeroMajorants.coefficient lower x ρ‖ ≤
          x * zeroBudget := by
    filter_upwards [hlarge] with k hk
    exact QuarticZeroSumBound.norm_sum_le_budget lower hx1 hRH hk
      (PolynomialZeroCountBridge.zetaGoodHeight_of_goodHeights hT k)
  have hpsi := psi_error_of_eventually_bounded_zero_sums_pos hT hx0
    (by simpa [PolynomialZeroMajorants.coefficient, PolynomialZeroMajorants.delta] using
      hnorm false)
    (by simpa [PolynomialZeroMajorants.coefficient, PolynomialZeroMajorants.delta] using
      hnorm true)
  calc
    _ ≤ 2 * (0.0000211 : ℝ) +
          (Real.log (2 * Real.pi) + 25000 / (Real.pi * Real.sqrt x)) / x + zeroBudget := hpsi
    _ = _ := by
      dsimp only [zeroBudget]
      ring

/-- `K + log 2π + 0.1 ≤ 6`, crudely from `log y ≤ y − 1`. -/
theorem constant_le : highWeight + Real.log (2 * Real.pi) + 0.1 ≤ 6 := by
  have hK := SchoenfeldRS75BudgetBounds.highWeight_lt
  have hl := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)
  have hp := Real.pi_lt_d2
  linarith

/-- **The RS75 `b = 23` chain with `√x ≥ L`**: for `x ≥ 1` and `0 < L ≤ √x`,
`|ψ(x) − x| ≤ (2δ + 3.21·10⁻⁶ + 15.47/L + 6/L² + 8000/L³) x`, `2δ = 0.0000422`. -/
theorem psi_error_le (hRH : Goals.FiniteRH 1894438.5122) {x L : ℝ} (hx1 : 1 ≤ x)
    (hL : 0 < L) (hLx : L ≤ Real.sqrt x) :
    |Chebyshev.psi x - x| ≤
      (0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3) * x := by
  have hx0 : 0 < x := by linarith
  have hrel := psi_relative_le hRH hx1
  have hK := SchoenfeldRS75BudgetBounds.highWeight_lt
  have hQ := SchoenfeldRS75BudgetBounds.sqrtCoefficient_lt
  have hQ0 := sqrtCoefficient_pos
  have hK0 := QuarticFirst29BudgetApplication.highWeight_nonneg
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hc := constant_le
  have hs0 : 0 < Real.sqrt x := hL.trans_le hLx
  have hLx2 : L ^ 2 ≤ x := by
    have := pow_le_pow_left₀ hL.le hLx 2
    rwa [Real.sq_sqrt hx0.le] at this
  -- `Q/√x ≤ 15.47/L`
  have h1 : sqrtCoefficient / Real.sqrt x ≤ 15.47 / L :=
    (div_le_div_of_nonneg_left hQ0.le hL hLx).trans
      (div_le_div_of_nonneg_right hQ.le hL.le)
  -- `(K + log 2π)/x ≤ 6/L²`
  have h2 : (highWeight + Real.log (2 * Real.pi)) / x ≤ 6 / L ^ 2 :=
    (div_le_div_of_nonneg_left (by linarith) (by positivity) hLx2).trans
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
  -- `25000/(π√x)/x ≤ 8000/L³`
  have hr : 25000 / (Real.pi * Real.sqrt x) ≤ 8000 / L := by
    rw [div_le_div_iff₀ (by positivity) hL]
    nlinarith [Real.pi_gt_d2, Real.sqrt_nonneg x]
  have h3 : 25000 / (Real.pi * Real.sqrt x) / x ≤ 8000 / L ^ 3 := by
    calc
      _ ≤ 8000 / L / x := div_le_div_of_nonneg_right hr hx0.le
      _ ≤ 8000 / L / L ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hLx2
      _ = 8000 / L ^ 3 := by rw [div_div]; congr 1; ring
  have hsplit : (highWeight + Real.log (2 * Real.pi) + 25000 / (Real.pi * Real.sqrt x)) / x =
      (highWeight + Real.log (2 * Real.pi)) / x + 25000 / (Real.pi * Real.sqrt x) / x := by
    ring
  have hfin : |Chebyshev.psi x - x| / x ≤
      0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3 := by
    rw [hsplit] at hrel
    linarith
  rwa [div_le_iff₀ hx0] at hfin

/-- `ψ(y) ≤ (1 + ε) y` from the chain, for `y ≥ 1` and `0 < L ≤ √y`. -/
theorem psi_le (hRH : Goals.FiniteRH 1894438.5122) {y L : ℝ} (hy1 : 1 ≤ y) (hL : 0 < L)
    (hLy : L ≤ Real.sqrt y) :
    Chebyshev.psi y ≤ (1 + (0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3)) * y := by
  have h := psi_error_le hRH hy1 hL hLy
  have ha := le_abs_self (Chebyshev.psi y - y)
  set E : ℝ := 0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3 with hE
  have he : (1 + E) * y = y + E * y := by ring
  linarith

end TernaryGoldbach.RSBounds.SchoenfeldRS75Chain
