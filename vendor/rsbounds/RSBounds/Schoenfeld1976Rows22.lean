import RSBounds.Schoenfeld1976Rows38

/-!
# Schoenfeld (1976), (5.6b*) for `e^22 ≤ x ≤ e^23`

`SchoenfeldRS75Chain.psi_error_le` holds for every `x ≥ 1`. At `√x ≥ 59800` (so for
`x ≥ e^22`) it gives `|ψ(x) − x| < 3.05·10⁻⁴ x`, and `3.05·10⁻⁴ · 23 < 0.0077629`.

For `θ` the crude `ψ − θ ≤ 6.5√x` (`PsiThetaElementary.psi_sub_theta_le`) is too weak here. Mathlib's
`Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi`,
`ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})`, together with the chain at `y = √x`
(`√y ≥ 244`, so `ψ(√x) ≤ 1.065 √x`) and Mathlib's `ψ(y) ≤ (log 4 + 4) y` for the other two
terms, gives `ψ(x) − θ(x) ≤ 1.212 √x` for `x ≥ 3.58·10⁹` (`psi_sub_theta_le_sharp`).

With `Schoenfeld1976Rows38.psiThetaLog_23_313` this gives (5.6b*) on `[e^22, e^313]`
(`psiThetaLog_22_313`).
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Rows22

/-- `e^22 ≥ 3.58·10⁹`. -/
theorem exp22_ge : (3580000000 : ℝ) ≤ Real.exp 22 := by
  calc
    (3580000000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 22 * (1 + 0 + 0 ^ 2 / 2 + 0 ^ 3 / 6) := by norm_num
    _ ≤ Real.exp ((22 : ℕ) + 0) := Schoenfeld1976Rows2.exp_lower 22 le_rfl
    _ = Real.exp 22 := by norm_num

/-- `39 x^{1/3} ≤ √x` for `x ≥ 3.58·10⁹` (`39⁶ < 3.52·10⁹`). -/
theorem cube_root_le {x : ℝ} (hx : 3580000000 ≤ x) :
    39 * x ^ ((3 : ℝ)⁻¹) ≤ Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have h6 : (39 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 39) hx0.le
      (by norm_num : (0 : ℝ) < 6)).2
    calc
      (39 : ℝ) ^ (6 : ℝ) ≤ 3580000000 := by norm_num [Real.rpow_natCast]
      _ ≤ x := hx
  have h := mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hx0.le ((3 : ℝ)⁻¹))
  rw [← Real.rpow_add hx0] at h
  rw [show (6 : ℝ)⁻¹ + (3 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow] at h
  exact h

/-- `700 x^{1/5} ≤ √x` for `x ≥ 3.58·10⁹` (`700¹⁰ < (3.58·10⁹)³`). -/
theorem fifth_root_le {x : ℝ} (hx : 3580000000 ≤ x) :
    700 * x ^ ((5 : ℝ)⁻¹) ≤ Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hbase : (700 : ℝ) ^ (10 : ℕ) ≤ x ^ (3 : ℕ) := by
    calc
      (700 : ℝ) ^ (10 : ℕ) ≤ (3580000000 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ x ^ (3 : ℕ) := by gcongr
  have h10 : (700 : ℝ) ≤ x ^ (3 / 10 : ℝ) := by
    apply (Real.rpow_le_rpow_iff (by norm_num)
      (Real.rpow_nonneg hx0.le (3 / 10 : ℝ))
      (by norm_num : (0 : ℝ) < 10)).mp
    rw [← Real.rpow_mul hx0.le]
    rw [show (3 / 10 : ℝ) * 10 = 3 by norm_num]
    simpa only [Real.rpow_ofNat] using hbase
  have h := mul_le_mul_of_nonneg_right h10 (Real.rpow_nonneg hx0.le ((5 : ℝ)⁻¹))
  rw [← Real.rpow_add hx0] at h
  rw [show (3 / 10 : ℝ) + (5 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow] at h
  exact h

/-- `ψ(x) − θ(x) ≤ 1.212 √x` for `x ≥ 3.58·10⁹`, under finite RH (used for `ψ(√x)`). -/
theorem psi_sub_theta_le_sharp (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : 3580000000 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 1.212 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hdec := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hsq : x ^ ((2 : ℝ)⁻¹) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]; norm_num
  rw [hsq] at hdec
  -- `ψ(√x)`: the chain at `y = √x`, with `√y ≥ 244` since `244⁴ ≤ x`.
  have hy1 : 1 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).mpr
    norm_num
    linarith
  have h244 : (244 : ℝ) ≤ Real.sqrt (Real.sqrt x) := by
    apply (Real.le_sqrt (by norm_num) hs0).mpr
    apply (Real.le_sqrt (by norm_num) hx0.le).mpr
    norm_num
    linarith
  have h2 := SchoenfeldRS75Chain.psi_le hRH hy1 (by norm_num) h244
  have hc2 : (1 + (0.0000422 + 3.21e-6 + 15.47 / (244 : ℝ) + 6 / 244 ^ 2 + 8000 / 244 ^ 3)) ≤
      (1.065 : ℝ) := by norm_num
  have h2' : Chebyshev.psi (Real.sqrt x) ≤ 1.065 * Real.sqrt x :=
    h2.trans (mul_le_mul_of_nonneg_right hc2 (by linarith))
  -- `ψ(x^{1/3})`, `ψ(x^{1/5})`: Mathlib's `ψ(y) ≤ (log 4 + 4) y < 5.4 y`.
  have hc := PsiThetaElementary.log_four_add_four_lt
  have h3 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le ((3 : ℝ)⁻¹))
  have h5 := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg hx0.le ((5 : ℝ)⁻¹))
  have r3 := cube_root_le hx
  have r5 := fifth_root_le hx
  have p3 : 0 ≤ x ^ ((3 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have p5 : 0 ≤ x ^ ((5 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have h3' : Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ 5.4 * x ^ ((3 : ℝ)⁻¹) :=
    h3.trans (mul_le_mul_of_nonneg_right hc.le p3)
  have h5' : Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ 5.4 * x ^ ((5 : ℝ)⁻¹) :=
    h5.trans (mul_le_mul_of_nonneg_right hc.le p5)
  -- `1.065 + 5.4/39 + 5.4/700 < 1.212`
  linarith

/-- **(5.6b*) for `e^22 ≤ x ≤ e^23`**, under finite RH. -/
theorem psiThetaLog_22_23 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 22 ≤ x)
    (hx' : x ≤ Real.exp 23) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hx3 : (3580000000 : ℝ) ≤ x := exp22_ge.trans hx
  have hxp : 0 < x := by linarith
  have hhi : Real.log x ≤ 23 := (Real.log_le_iff_le_exp hxp).mpr hx'
  have hlo : 22 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hl0 : 0 < Real.log x := by linarith
  have hL : (59800 : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hxp.le).mpr
    norm_num
    linarith
  set E : ℝ := 0.0000422 + 3.21e-6 + 15.47 / (59800 : ℝ) + 6 / 59800 ^ 2 + 8000 / 59800 ^ 3
    with hE
  clear_value E
  have hψ : |Chebyshev.psi x - x| ≤ E * x := by
    rw [hE]; exact SchoenfeldRS75Chain.psi_error_le hRH (by linarith) (by norm_num) hL
  have hpt := psi_sub_theta_le_sharp hRH hx3
  have htp := Chebyshev.theta_le_psi x
  -- `1.212 √x ≤ (1.212/59800) x`
  have hsq : 1.212 * Real.sqrt x ≤ 1.212 / 59800 * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    calc 1.212 * Real.sqrt x * 59800 ≤ 1.212 * Real.sqrt x * Real.sqrt x :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 1.212 * x := by rw [mul_assoc, Real.mul_self_sqrt hxp.le]
  have hcx : 0 ≤ 1.212 / 59800 * x := by positivity
  have he : (E + 1.212 / 59800) * x = E * x + 1.212 / 59800 * x := by ring
  have hθ : |Chebyshev.theta x - x| ≤ (E + 1.212 / 59800) * x := by
    rw [he, abs_le]
    constructor
    · linarith [neg_abs_le (Chebyshev.psi x - x)]
    · linarith [le_abs_self (Chebyshev.psi x - x)]
  have hψ' : |Chebyshev.psi x - x| ≤ (E + 1.212 / 59800) * x := by
    rw [he]; linarith
  have hnum : (E + 1.212 / 59800) * 23 < 0.0077629 := by rw [hE]; norm_num
  have hEp : 0 ≤ E + 1.212 / 59800 := by rw [hE]; norm_num
  have key : (E + 1.212 / 59800) * x < 0.0077629 * x / Real.log x := by
    rw [lt_div_iff₀ hl0]
    have h1 : (E + 1.212 / 59800) * Real.log x ≤ (E + 1.212 / 59800) * 23 :=
      mul_le_mul_of_nonneg_left hhi hEp
    have h2 : x * ((E + 1.212 / 59800) * Real.log x) ≤ x * ((E + 1.212 / 59800) * 23) :=
      mul_le_mul_of_nonneg_left h1 hxp.le
    have h3 : x * ((E + 1.212 / 59800) * 23) < x * 0.0077629 := mul_lt_mul_of_pos_left hnum hxp
    nlinarith
  exact ⟨hψ'.trans_lt key, hθ.trans_lt key⟩

/-- **(5.6b*) for `e^22 ≤ x ≤ e^313`**, under finite RH. -/
theorem psiThetaLog_22_313 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 22 ≤ x)
    (hx' : x ≤ Real.exp 313) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases le_or_gt x (Real.exp 23) with h1 | h1
  · exact psiThetaLog_22_23 hRH hx h1
  · exact Schoenfeld1976Rows38.psiThetaLog_23_313 hRH h1.le hx'

/-- **(5.6b*) for `x ≥ e^22` outside `(e^313, e^947)`**, under finite RH. -/
theorem psiThetaLog_ge22_off_gap (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 22 ≤ x)
    (hgap : x ≤ Real.exp 313 ∨ Real.exp 947 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases hgap with h | h
  · exact psiThetaLog_22_313 hRH hx h
  · exact Schoenfeld1976Rows4.psiThetaLog_ge947 hRH h

end TernaryGoldbach.RSBounds.Schoenfeld1976Rows22
