import RSBounds.SchoenfeldTheorem11Analytic

/-!
# Schoenfeld (1976), Theorem 7* for `x ≥ e^{1737}`

On `x ≥ e^{1737}`, `ε₀(x) log x ≤ 0.0045` (`eps0_mul_log_le`), so Theorem 11
(`SchoenfeldTheorem11Analytic`) gives (5.6b*) and (5.6*) there:
`|ψ(x) − x|, |θ(x) − x| < 0.0077629 x / log x` and `|θ(x) − x| < 0.0239922 x / log x`,
given `FiniteRH 1894438.5122`.

These are the target statements `Goals.Schoenfeld1976.PsiThetaLog` and `ThetaLog` restricted to
`x ≥ e^{1737}`. The ranges `e^{22} ≤ x < e^{1737}` and `758711 ≤ x < e^{1737}` need the paper's
table and finite checks (`docs/Schoenfeld1976Plan.md`) and are not covered here.
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Large

/-- `X³e^{−X}` decreases for `X ≥ 3` (via `e^s ≥ 1 + s + s²/2 + s³/6`, no derivatives). -/
theorem cube_exp_mono {X X0 : ℝ} (hX0 : 3 ≤ X0) (hX : X0 ≤ X) :
    X ^ 3 * Real.exp (-X) ≤ X0 ^ 3 * Real.exp (-X0) := by
  have hs0 : 0 ≤ X - X0 := by linarith
  have hT : ∑ i ∈ Finset.range 4, (X - X0) ^ i / (i.factorial : ℝ) ≤ Real.exp (X - X0) :=
    Real.sum_le_exp_of_nonneg hs0 4
  have hsum : ∑ i ∈ Finset.range 4, (X - X0) ^ i / (i.factorial : ℝ) =
      1 + (X - X0) + (X - X0) ^ 2 / 2 + (X - X0) ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]

  rw [hsum] at hT
  have hXe : Real.exp (-X0) = Real.exp (-X) * Real.exp (X - X0) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 0 ≤ X0 ^ 3 - 3 * X0 ^ 2 := by nlinarith
  have h2 : 0 ≤ X0 ^ 3 / 2 - 3 * X0 := by nlinarith
  have h3 : 0 ≤ X0 ^ 3 / 6 - 1 := by nlinarith
  have key : X ^ 3 ≤ X0 ^ 3 * (1 + (X - X0) + (X - X0) ^ 2 / 2 + (X - X0) ^ 3 / 6) := by
    nlinarith [mul_nonneg hs0 h1, mul_nonneg (sq_nonneg (X - X0)) h2,
      mul_nonneg (pow_nonneg hs0 3) h3]
  rw [hXe]
  have hpos : 0 < Real.exp (-X) := Real.exp_pos _
  have hc : 0 ≤ X0 ^ 3 := by positivity
  calc X ^ 3 * Real.exp (-X)
      ≤ X0 ^ 3 * (1 + (X - X0) + (X - X0) ^ 2 / 2 + (X - X0) ^ 3 / 6) * Real.exp (-X) :=
        mul_le_mul_of_nonneg_right key hpos.le
    _ ≤ X0 ^ 3 * Real.exp (X - X0) * Real.exp (-X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hc) hpos.le
    _ = X0 ^ 3 * (Real.exp (-X) * Real.exp (X - X0)) := by ring

/-- The value at `X = 13.4192`. -/
theorem cube_exp_numeric : (13.4192 : ℝ) ^ 3 * Real.exp (-13.4192) ≤ 3.7e-3 := by
  have he1 : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h13 : (2.7182818283 : ℝ) ^ 13 ≤ Real.exp 13 := by
    have : Real.exp 13 = Real.exp 1 ^ 13 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) he1.le 13
  have hq : 1 + 0.4192 + 0.4192 ^ 2 / 2 ≤ Real.exp 0.4192 :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hsplit : Real.exp 13.4192 = Real.exp 13 * Real.exp 0.4192 := by
    rw [← Real.exp_add]
    norm_num
  have hbig : (2.7182818283 : ℝ) ^ 13 * (1 + 0.4192 + 0.4192 ^ 2 / 2) ≤ Real.exp 13.4192 := by
    rw [hsplit]
    exact mul_le_mul h13 hq (by norm_num) (Real.exp_pos _).le
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc (13.4192 : ℝ) ^ 3
      ≤ 3.7e-3 * ((2.7182818283 : ℝ) ^ 13 * (1 + 0.4192 + 0.4192 ^ 2 / 2)) := by norm_num
    _ ≤ 3.7e-3 * Real.exp 13.4192 := mul_le_mul_of_nonneg_left hbig (by norm_num)

/-- `ε₀(x) log x ≤ 0.0045` for `x ≥ e^{1737}`. -/
theorem eps0_mul_log_le {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    Goals.Schoenfeld1976.epsilon0 x * Real.log x ≤ 0.0045 := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 1737 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hx
  obtain ⟨X, hXdef⟩ : ∃ X, X = Real.sqrt (Real.log x / 9.645908801) := ⟨_, rfl⟩
  have hX : 13.4192 ≤ X := by rw [hXdef]; exact SchoenfeldBalanceHeight.X_ge_of_log_ge hlogx
  have hXp : 0 < X := by linarith
  have hX2 : X ^ 2 = Real.log x / 9.645908801 := by
    rw [hXdef]
    exact SchoenfeldBalanceAlgebra.X_sq hx1.le
  have hε : Goals.Schoenfeld1976.epsilon0 x =
      Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X)) := by
    rw [hXdef]
    unfold Goals.Schoenfeld1976.epsilon0 Goals.Schoenfeld1976.X
    ring
  have hlog : Real.log x = 9.645908801 * X ^ 2 := by rw [hX2]; ring
  have hc0 := (SchoenfeldTheorem11Analytic.c0_bounds).2
  have hsq : 3.66 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hXp.le).mpr (by nlinarith)
  have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXp.le
  have hsX : Real.sqrt X ≤ X / 3.66 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hcube := (cube_exp_mono (by norm_num) hX).trans cube_exp_numeric
  have hE : 0 < Real.exp (-X) := Real.exp_pos _
  rw [hε, hlog]
  calc Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X)) * (9.645908801 * X ^ 2)
      ≤ 0.4 * (X / 3.66 * Real.exp (-X)) * (9.645908801 * X ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hc0 (mul_le_mul_of_nonneg_right hsX hE.le) (by positivity)
          (by norm_num)
    _ = 0.4 * 9.645908801 / 3.66 * (X ^ 3 * Real.exp (-X)) := by ring
    _ ≤ 0.4 * 9.645908801 / 3.66 * 3.7e-3 := mul_le_mul_of_nonneg_left hcube (by norm_num)
    _ ≤ 0.0045 := by norm_num

/-- `ε₀(x) ≤ c/log x` whenever `0.0045 ≤ c`, for `x ≥ e^{1737}`. -/
theorem eps0_le_div_log {x c : ℝ} (hx : Real.exp 1737 ≤ x) (hc : 0.0045 ≤ c) :
    x * Goals.Schoenfeld1976.epsilon0 x ≤ c * x / Real.log x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlogx : 1737 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hl : 0 < Real.log x := by linarith
  have h := eps0_mul_log_le hx
  rw [le_div_iff₀ hl]

  have : x * (Goals.Schoenfeld1976.epsilon0 x * Real.log x) ≤ x * c :=
    mul_le_mul_of_nonneg_left (h.trans hc) hxp.le
  linarith

/-- **(5.6b*) for `x ≥ e^{1737}`.** -/
theorem psiThetaLog_large (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hb := eps0_le_div_log hx (by norm_num : (0.0045 : ℝ) ≤ 0.0077629)
  exact ⟨lt_of_lt_of_le (SchoenfeldTheorem11Analytic.psi_lt hRH hx) hb,
    lt_of_lt_of_le (SchoenfeldTheorem11Analytic.theta_lt hRH hx) hb⟩

/-- **(5.6*) for `x ≥ e^{1737}`.** -/
theorem thetaLog_large (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1737 ≤ x) :
    |Chebyshev.theta x - x| < 0.0239922 * x / Real.log x :=
  lt_of_lt_of_le (SchoenfeldTheorem11Analytic.theta_lt hRH hx)
    (eps0_le_div_log hx (by norm_num))

end TernaryGoldbach.RSBounds.Schoenfeld1976Large
