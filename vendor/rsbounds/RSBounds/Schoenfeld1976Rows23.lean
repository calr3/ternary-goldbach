import RSBounds.Schoenfeld1976Rows2

/-!
# Schoenfeld (1976), (5.6b*) for `e^23 ≤ x ≤ e^38.3`, from the RS75 `b = 23` bound

Rosser and Schoenfeld's `b = 23` bound `|ψ(x) − x| < 0.00020211 x` for `x ≥ e^23`
(`RosserSchoenfeld1975.psi_error_b23`, under the same finite-RH hypothesis) already gives
(5.6b*) while `0.00020211 · log x < 0.0077629`, that is up to `log x ≈ 38.4`. For `θ` the extra
`6.5 √x` of `SchoenfeldTheorem11B23.theta_err_le` is absorbed on four ranges of `log x`:
`[23, 28]`, `[28, 33]`, `[33, 37]`, `[37, 38.3]`.
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Rows23

/-- One range: if `bl ≤ log x ≤ bh` with `bl ≥ 23` and `L ≤ e^{bl/2}`, the RS75 bound gives
(5.6b*) for `ψ` and `θ` as soon as the two stated numerical inequalities hold. -/
theorem rs75_piece (hRH : Goals.FiniteRH 1894438.5122) {x bl bh L : ℝ} (hbl : 23 ≤ bl)
    (hx1 : Real.exp bl ≤ x) (hx2 : x ≤ Real.exp bh) (hL : 0 < L)
    (hE : Real.exp (-(bl / 2)) ≤ 1 / L)
    (hnum1 : 0.00020211 * bh < 0.0077629) (hnum2 : (0.00020211 + 6.5 / L) * bh < 0.0077629) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hlo : bl ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx1
  have hhi : Real.log x ≤ bh := (Real.log_le_iff_le_exp hxp).mpr hx2
  have hl0 : 0 < Real.log x := by linarith
  have hx23 : Real.exp 23 ≤ x := le_trans (Real.exp_le_exp.mpr hbl) hx1
  have h5 : (100000 : ℝ) ≤ x := le_trans SchoenfeldTheorem11B23.exp23_ge hx23
  have hψ := RosserSchoenfeld1975.psi_error_b23 hRH x hx23
  have hθ := SchoenfeldTheorem11B23.theta_err_le h5
  -- `√x ≥ e^{bl/2} ≥ L`, so `6.5 √x ≤ 6.5 x / L`.
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
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxp
  have hsq : 6.5 * Real.sqrt x ≤ 6.5 / L * x := by
    have hLs : L ≤ Real.sqrt x := hLe.trans hs
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    calc 6.5 * Real.sqrt x * L ≤ 6.5 * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hLs (by positivity)
      _ = 6.5 * x := by rw [mul_assoc, Real.mul_self_sqrt hxp.le]
  -- From `ε x` with `ε · bh < 0.0077629` to the (5.6b*) form.
  have key : ∀ ε : ℝ, 0 ≤ ε → ε * bh < 0.0077629 → ε * x < 0.0077629 * x / Real.log x := by
    intro ε hε hεb
    rw [lt_div_iff₀ hl0]
    have h1 : ε * Real.log x ≤ ε * bh := mul_le_mul_of_nonneg_left hhi hε
    have h2 : x * (ε * Real.log x) ≤ x * (ε * bh) := mul_le_mul_of_nonneg_left h1 hxp.le
    have h3 : x * (ε * bh) < x * 0.0077629 := mul_lt_mul_of_pos_left hεb hxp
    nlinarith
  have k1 := key 0.00020211 (by norm_num) hnum1
  have k2 := key (0.00020211 + 6.5 / L) (by positivity) hnum2
  constructor
  · linarith
  · have : |Chebyshev.theta x - x| < (0.00020211 + 6.5 / L) * x := by nlinarith
    linarith

/-- **(5.6b*) for `e^23 ≤ x ≤ e^38.3`**, under finite RH, from the RS75 `b = 23` bound. -/
theorem psiThetaLog_23_383 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x)
    (hx' : x ≤ Real.exp 38.3) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases le_or_gt x (Real.exp 28) with h1 | h1
  · exact rs75_piece hRH (bl := 23) (bh := 28) (L := 98500) (by norm_num) hx h1 (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.5) 11 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num) (by norm_num)
  rcases le_or_gt x (Real.exp 33) with h2 | h2
  · exact rs75_piece hRH (bl := 28) (bh := 33) (L := 1200000) (by norm_num) h1.le h2
      (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0) 14 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num) (by norm_num)
  rcases le_or_gt x (Real.exp 37) with h3 | h3
  · exact rs75_piece hRH (bl := 33) (bh := 37) (L := 14600000) (by norm_num) h2.le h3
      (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.5) 16 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num) (by norm_num)
  · exact rs75_piece hRH (bl := 37) (bh := 38.3) (L := 108000000) (by norm_num) h3.le hx'
      (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.5) 18 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num) (by norm_num)

end TernaryGoldbach.RSBounds.Schoenfeld1976Rows23
