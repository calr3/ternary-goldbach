import RSBounds.SchoenfeldRS75Chain
import RSBounds.Schoenfeld1976Rows23
import RSBounds.Schoenfeld1976Rows4

/-!
# Schoenfeld (1976), (5.6b*) for `e^38.3 ≤ x ≤ e^170`, from the RS75 `b = 23` chain

`SchoenfeldRS75Chain.psi_error_le` keeps the RS75 `b = 23` budget as a function of `x`:
for `√x ≥ L`, `|ψ(x) − x| ≤ (0.0000422 + 3.21·10⁻⁶ + 15.47/L + 6/L² + 8000/L³) x`. At
`x ≥ e^38.3` (`L = 2·10⁸`) that is below `4.6·10⁻⁵ x`, so one row covers (5.6b*) up to
`log x = 170` (`psiThetaLog_383_170`). The `θ` transfer is the crude `6.5√x` of
`SchoenfeldTheorem11B23.theta_err_le`.

Combined with `Schoenfeld1976Rows23` and `Schoenfeld1976Rows4`, (5.6b*) holds on
`[e^23, e^313]` (`psiThetaLog_23_313`).
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Rows38

/-- One row: if `bl ≤ log x ≤ bh` with `bl ≥ 23`, `L ≤ e^{bl/2}` and the stated numerical
inequality holds, then (5.6b*) holds at `x` for `ψ` and `θ`. -/
theorem piece (hRH : Goals.FiniteRH 1894438.5122) {x bl bh L : ℝ} (hbl : 23 ≤ bl)
    (hx1 : Real.exp bl ≤ x) (hx2 : x ≤ Real.exp bh) (hL : 0 < L)
    (hE : Real.exp (-(bl / 2)) ≤ 1 / L)
    (hnum : (0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3 + 6.5 / L) * bh <
      0.0077629) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hlo : bl ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx1
  have hhi : Real.log x ≤ bh := (Real.log_le_iff_le_exp hxp).mpr hx2
  have hl0 : 0 < Real.log x := by linarith
  have hx23 : Real.exp 23 ≤ x := le_trans (Real.exp_le_exp.mpr hbl) hx1
  have h5 : (100000 : ℝ) ≤ x := le_trans SchoenfeldTheorem11B23.exp23_ge hx23
  have hx1' : 1 ≤ x := by linarith
  -- `√x ≥ e^{bl/2} ≥ L`
  have hLe : L ≤ Real.exp (bl / 2) := by
    have h := hE
    rw [Real.exp_neg, inv_eq_one_div] at h
    have hp : 0 < Real.exp (bl / 2) := Real.exp_pos _
    rw [div_le_div_iff₀ hp hL] at h
    linarith
  have hs : Real.exp (bl / 2) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (Real.exp_pos _).le hxp.le).mpr
    have e : Real.exp (bl / 2) ^ 2 = Real.exp bl := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e]
    exact hx1
  have hLs : L ≤ Real.sqrt x := hLe.trans hs
  have hψ := SchoenfeldRS75Chain.psi_error_le hRH hx1' hL hLs
  have hθ := SchoenfeldTheorem11B23.theta_err_le h5
  have hsq : 6.5 * Real.sqrt x ≤ 6.5 / L * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    calc 6.5 * Real.sqrt x * L ≤ 6.5 * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hLs (by positivity)
      _ = 6.5 * x := by rw [mul_assoc, Real.mul_self_sqrt hxp.le]
  set ε : ℝ := 0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3 + 6.5 / L with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεx : ε * x =
      (0.0000422 + 3.21e-6 + 15.47 / L + 6 / L ^ 2 + 8000 / L ^ 3) * x + 6.5 / L * x := by
    rw [hε]; ring
  have h65 : 0 ≤ 6.5 / L * x := by positivity
  have hθε : |Chebyshev.theta x - x| ≤ ε * x := by rw [hεx]; linarith
  have hψε : |Chebyshev.psi x - x| ≤ ε * x := by rw [hεx]; linarith
  -- From `ε x` with `ε · bh < 0.0077629` to the (5.6b*) form.
  have key : ε * x < 0.0077629 * x / Real.log x := by
    rw [lt_div_iff₀ hl0]
    have h1 : ε * Real.log x ≤ ε * bh := mul_le_mul_of_nonneg_left hhi hε0
    have h2 : x * (ε * Real.log x) ≤ x * (ε * bh) := mul_le_mul_of_nonneg_left h1 hxp.le
    have h3 : x * (ε * bh) < x * 0.0077629 := mul_lt_mul_of_pos_left hnum hxp
    nlinarith
  exact ⟨hψε.trans_lt key, hθε.trans_lt key⟩

/-- **(5.6b*) for `e^38.3 ≤ x ≤ e^170`**, under finite RH, from the RS75 `b = 23` chain at the
threshold `√x ≥ 2·10⁸`. -/
theorem psiThetaLog_383_170 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 38.3 ≤ x)
    (hx' : x ≤ Real.exp 170) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x :=
  piece hRH (bl := 38.3) (bh := 170) (L := 200000000) (by norm_num) hx hx' (by norm_num)
    (Schoenfeld1976Rows2.exp_neg_le (f := 0.15) 19 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))
    (by norm_num)

/-- **(5.6b*) for `e^23 ≤ x ≤ e^313`**, under finite RH: `Schoenfeld1976Rows23` on
`[e^23, e^38.3]`, `psiThetaLog_383_170` on `[e^38.3, e^170]`, `Schoenfeld1976Rows4` on
`[e^100, e^313]`. -/
theorem psiThetaLog_23_313 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x)
    (hx' : x ≤ Real.exp 313) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases le_or_gt x (Real.exp 38.3) with h1 | h1
  · exact Schoenfeld1976Rows23.psiThetaLog_23_383 hRH hx h1
  rcases le_or_gt x (Real.exp 170) with h2 | h2
  · exact psiThetaLog_383_170 hRH h1.le h2
  · have h100 : Real.exp 100 ≤ x :=
      le_trans (Real.exp_le_exp.mpr (by norm_num)) h2.le
    exact Schoenfeld1976Rows4.psiThetaLog_100_313 hRH h100 hx'

end TernaryGoldbach.RSBounds.Schoenfeld1976Rows38
