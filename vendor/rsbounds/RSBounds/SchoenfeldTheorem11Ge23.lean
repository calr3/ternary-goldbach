import RSBounds.SchoenfeldTheorem11Far

/-!
# Schoenfeld (1976), Theorem 11 for every `x ≥ e^23`

* `e^23 ≤ x ≤ e^700`: the RS75 row `b = 23` (`SchoenfeldTheorem11B23`);
* `e^700 ≤ x < e^1737`: the far-only quadratic envelope with `δ = ε₀(x)/2` (`core_far`);
* `x ≥ e^1737`: Schoenfeld's analytic argument (`SchoenfeldTheorem11Analytic`).

All under `FiniteRH 1894438.5122`. The target propositions also cover `17 ≤ x`, `101 ≤ x` and `1 ≤ x`;
the range below `e^23` is not covered here.
-/

open Real

namespace TernaryGoldbach.RSBounds.SchoenfeldTheorem11Ge23

open SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldQuadraticEnvelope
open SchoenfeldTheorem11Far

/-- `e^{8.5} ≥ 4840`. -/
theorem exp_85_ge : (4840 : ℝ) ≤ Real.exp 8.5 := by
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have h8 : (2.7182818283 : ℝ) ^ 8 ≤ Real.exp 8 := by
    have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) he.le 8
  have h05 : 1 + 0.5 + 0.5 ^ 2 / 2 ≤ Real.exp 0.5 := Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hsplit : Real.exp 8.5 = Real.exp 8 * Real.exp 0.5 := by
    rw [← Real.exp_add]
    norm_num
  rw [hsplit]
  calc (4840 : ℝ) ≤ 2.7182818283 ^ 8 * (1 + 0.5 + 0.5 ^ 2 / 2) := by norm_num
    _ ≤ Real.exp 8 * Real.exp 0.5 := mul_le_mul h8 h05 (by norm_num) (Real.exp_pos _).le

set_option maxHeartbeats 800000 in
/-- The main estimate on `e^700 ≤ x < e^1737`, with room for `ψ(x) − θ(x) ≤ 6.5√x`. -/
theorem core_far

 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 700 ≤ x)
    (hx2 : x < Real.exp 1737) :
    |Chebyshev.psi x - x| + 6.5 * Real.sqrt x < x * Goals.Schoenfeld1976.epsilon0 x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 700 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hhi : Real.log x < 1737 := (Real.log_lt_iff_lt_exp hxp).mpr hx2
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hx
  obtain ⟨X, hXdef⟩ : ∃ X, X = Real.sqrt (Real.log x / 9.645908801) := ⟨_, rfl⟩
  have hX2 : X ^ 2 = Real.log x / 9.645908801 := by
    rw [hXdef]
    exact SchoenfeldBalanceAlgebra.X_sq hx1.le
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Real.sqrt_nonneg _
  have hXlo : 8.5 ≤ X := by
    have h : (8.5 : ℝ) ^ 2 ≤ X ^ 2 := by
      rw [hX2, le_div_iff₀ (by norm_num)]
      linarith
    nlinarith
  have hXhi : X ≤ 13.42 := by
    have h : X ^ 2 ≤ 13.42 ^ 2 := by
      rw [hX2, div_le_iff₀ (by norm_num)]
      linarith
    nlinarith
  have hε : Goals.Schoenfeld1976.epsilon0 x =
      Real.sqrt (8 / (17 * π)) * (Real.sqrt X * Real.exp (-X)) := by
    rw [hXdef]
    exact SchoenfeldTheorem11B23.eps0_eq x
  have hF := far_le hXlo hXhi
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt X * Real.exp (-X) := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c0, c0 = Real.sqrt (8 / (17 * π)) := ⟨_, rfl⟩
  rw [← hsdef, ← hc0def] at hε hF
  have hc0 : 0.386 ≤ c0 := by rw [hc0def]; exact c0_ge
  have hc0hi : c0 ≤ 0.4 := by rw [hc0def]; exact (SchoenfeldTheorem11Analytic.c0_bounds).2
  have hsX1 : 1 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) hX0).mpr (by nlinarith)
  have hs0 : 0 < s := by
    rw [hsdef]
    have : 0 < Real.sqrt X := by linarith
    positivity
  have hs_le : s ≤ 6.1e-4 := by
    have hmono := SchoenfeldTheorem11B23.sqrt_mul_exp_anti (X := 8.5) (X1 := X)
      (by norm_num) hXlo
    have hs85 : Real.sqrt 8.5 ≤ 2.916 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have he85 : Real.exp (-8.5) ≤ (4840 : ℝ)⁻¹ := by
      rw [Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr exp_85_ge
    rw [hsdef]
    calc Real.sqrt X * Real.exp (-X) ≤ Real.sqrt 8.5 * Real.exp (-8.5) := hmono
      _ ≤ 2.916 * (4840 : ℝ)⁻¹ := mul_le_mul hs85 he85 (Real.exp_pos _).le (by norm_num)
      _ ≤ 6.1e-4 := by norm_num
  have hc0pos : 0 < c0 := by linarith
  -- `δ = ε₀/2`.
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = c0 * s / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hcs : c0 * s ≤ 0.4 * 6.1e-4 :=
    mul_le_mul hc0hi hs_le hs0.le (by norm_num)
  have hδ1 : δ ≤ 0.001 := by rw [hδdef]; linarith
  have hδ2 : 2 * δ < 1 := by linarith
  have hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2 := by
    rw [← hX2]
    have hu := u_bounds.1
    have : (11.55 : ℝ) * 11.55 ≤ Real.log (1894438.5122 / 17) * Real.log (1894438.5122 / 17) :=
      mul_self_le_mul_self (by norm_num) hu
    nlinarith
  have henv := SchoenfeldQuadraticFar.psi_error_le_farEnvelope hRH hx1 hδ hδ2 hfar
  unfold SchoenfeldQuadraticFar.farEnvelope at henv
  rw [← hX2] at henv
  have hR2 : QuadraticZeroKernel.R2 δ ≤ 4.1 := by
    have := SchoenfeldBalanceTail.R2_le hδ.le (by linarith)
    linarith
  have hR20 : 0 ≤ QuadraticZeroKernel.R2 δ := by
    have := SchoenfeldBalanceMain.R2_ge hδ.le
    linarith
  have hlog8 : 8 * X + 80 ≤ Real.log x := by
    have e : Real.log x = 9.645908801 * X ^ 2 := by rw [hX2]; ring
    have : 8.5 * X ≤ X * X := mul_le_mul_of_nonneg_right hXlo hX0
    nlinarith
  have hδinv : 1 / δ ^ 2 ≤ 72.25 * Real.exp X ^ 2 := by
    have hEX : Real.exp (-X) * Real.exp X = 1 := by rw [← Real.exp_add]; simp
    have hde : δ * Real.exp X = c0 * Real.sqrt X / 2 := by
      rw [hδdef, hsdef]
      calc c0 * (Real.sqrt X * Real.exp (-X)) / 2 * Real.exp X =
          c0 * Real.sqrt X * (Real.exp (-X) * Real.exp X) / 2 := by ring
        _ = c0 * Real.sqrt X / 2 := by rw [hEX, mul_one]
    have hge : 0.193 ≤ δ * Real.exp X := by
      rw [hde]
      have := mul_le_mul hc0 hsX1 (by norm_num) hc0pos.le
      linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 0.193) hge]
  have hsmall := SchoenfeldBalanceTail.small_terms_le hx1 (by linarith) hlog8 hδ hδinv hR20 hR2
  rw [← hsdef] at hsmall
  -- `(R₂/δ²)·F ≤ 0.4428·c₀ s`.
  have hE0 : 0 < c0 * s := by positivity
  have hRF : QuadraticZeroKernel.R2 δ / δ ^ 2 * farAllowance (X ^ 2) 1894438.5122 ≤
      0.4428 * (c0 * s) := by
    have hδsq : δ ^ 2 = (c0 * s) ^ 2 / 4 := by rw [hδdef]; ring
    calc QuadraticZeroKernel.R2 δ / δ ^ 2 * farAllowance (X ^ 2) 1894438.5122
        ≤ QuadraticZeroKernel.R2 δ / δ ^ 2 * (0.027 * (c0 * s) ^ 3) :=
          mul_le_mul_of_nonneg_left hF (div_nonneg hR20 (sq_nonneg δ))
      _ ≤ 4.1 / δ ^ 2 * (0.027 * (c0 * s) ^ 3) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR2 (sq_nonneg δ))
            (by positivity)
      _ = 0.4428 * (c0 * s) := by
          rw [hδsq]
          field_simp
          ring
  have hxRF := mul_le_mul_of_nonneg_left hRF hxp.le
  have hu : s / (X + 1) ≤ s / 9.5 :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) (by linarith)
  have hxu : 1e-4 * x * (s / (X + 1)) ≤ 1e-4 * x * (s / 9.5) :=
    mul_le_mul_of_nonneg_left hu (by positivity)
  have hcs' : 0 ≤ (c0 - 0.386) * (x * s) := mul_nonneg (by linarith) (by positivity)
  have hxE : 0 < x * (c0 * s) := mul_pos hxp hE0
  have hδx : δ * x = c0 * s / 2 * x := by rw [hδdef]
  rw [hε]
  have step1 : |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ 1e-4 * x * (s / (X + 1)) +
      x * (QuadraticZeroKernel.R2 δ / δ ^ 2 * farAllowance (X ^ 2) 1894438.5122) + δ * x := by
    linarith
  have step3 : 1e-4 * x * (s / 9.5) ≤ 2.73e-5 * (x * (c0 * s)) := by
    have e2 : (c0 - 0.386) * (x * s) = x * (c0 * s) - 0.386 * (x * s) := by ring
    have h386 : 0.386 * (x * s) ≤ x * (c0 * s) := by
      have h := hcs'
      rw [e2] at h
      linarith
    calc 1e-4 * x * (s / 9.5) = (1e-4 / 9.5) * (x * s) := by ring
      _ ≤ (1e-4 / 9.5) * (x * (c0 * s) / 0.386) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [le_div_iff₀ (by norm_num)]
          linarith
      _ = (1e-4 / 9.5 / 0.386) * (x * (c0 * s)) := by ring
      _ ≤ 2.73e-5 * (x * (c0 * s)) := mul_le_mul_of_nonneg_right (by norm_num) hxE.le
  linarith



/-- `|θ(x) − x| < x ε₀(x)` on `e^700 ≤ x < e^1737`. -/
theorem theta_far (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 700 ≤ x)
    (hx2 : x < Real.exp 1737) :
    |Chebyshev.theta x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  have h := core_far hRH hx hx2
  have h23 : Real.exp 23 ≤ Real.exp 700 := Real.exp_le_exp.mpr (by norm_num)
  have hth := SchoenfeldTheorem11B23.theta_err_le
    (le_trans SchoenfeldTheorem11B23.exp23_ge (le_trans h23 hx))
  linarith

/-- **Theorem 11, (7.2), for every `x ≥ e^23`.** -/
theorem psi_lt (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x) :
    |Chebyshev.psi x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  rcases le_or_gt x (Real.exp 700) with h1 | h1
  · exact SchoenfeldTheorem11B23.psi_lt hRH hx h1
  rcases le_or_gt (Real.exp 1737) x with h2 | h2
  · exact SchoenfeldTheorem11Analytic.psi_lt hRH h2
  · have h := core_far hRH h1.le h2
    have : 0 ≤ 6.5 * Real.sqrt x := by positivity
    linarith

/-- **Theorem 11, (7.3), for every `x ≥ e^23`.** -/
theorem theta_lt (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x) :
    |Chebyshev.theta x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  rcases le_or_gt x (Real.exp 700) with h1 | h1
  · exact SchoenfeldTheorem11B23.theta_lt hRH hx h1
  rcases le_or_gt (Real.exp 1737) x with h2 | h2
  · exact SchoenfeldTheorem11Analytic.theta_lt hRH h2
  · exact theta_far hRH h1.le h2

/-- **Theorem 11, (7.4) as established on p. 349, for every `x ≥ e^23`.** -/
theorem psi_upper (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x) :
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧
      Chebyshev.psi x - x < x * Goals.Schoenfeld1976.epsilon0 x :=
  ⟨by linarith [Chebyshev.theta_le_psi x], lt_of_le_of_lt (le_abs_self _) (psi_lt hRH hx)⟩

end TernaryGoldbach.RSBounds.SchoenfeldTheorem11Ge23
