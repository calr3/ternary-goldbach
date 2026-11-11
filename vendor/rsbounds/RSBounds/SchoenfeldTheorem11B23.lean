import RSBounds.Schoenfeld1976Large
import RSBounds.RosserSchoenfeld1975

/-!
# Schoenfeld (1976), Theorem 11 for `e^23 ≤ x ≤ e^700`, from the RS75 row `b = 23`

`RosserSchoenfeld1975.psi_error_b23` gives `|ψ(x) − x| < 0.00020211 x` for `x ≥ e^23`, under
`FiniteRH 1894438.5122`. On `e^23 ≤ x ≤ e^700`, `ε₀(x) ≥ 2.1·10⁻⁴` (`eps0_ge`), so this row already gives
Theorem 11's bounds there. (`ε₀(x) > 0.00020211` holds up to about `log x = 719`.)
-/

open Real

namespace TernaryGoldbach.RSBounds.SchoenfeldTheorem11B23

/-- `√X e^{−X}` decreases for `X ≥ 1/2`. -/
theorem sqrt_mul_exp_anti {X X1 : ℝ} (hX : 1 / 2 ≤ X) (h : X ≤ X1) :
    Real.sqrt X1 * Real.exp (-X1) ≤ Real.sqrt X * Real.exp (-X) := by
  have hs : 0 ≤ X1 - X := by linarith
  have hX0 : 0 < X := by linarith
  have he : 1 + (X1 - X) ≤ Real.exp (X1 - X) := by linarith [Real.add_one_le_exp (X1 - X)]
  have hsq : Real.sqrt X1 ≤ Real.sqrt X * (1 + (X1 - X)) := by
    rw [Real.sqrt_le_left (mul_nonneg (Real.sqrt_nonneg _) (by linarith)), mul_pow,
      Real.sq_sqrt hX0.le]
    nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ 2 * X - 1),
      mul_nonneg hX0.le (sq_nonneg (X1 - X))]
  have hE : Real.exp (-X) = Real.exp (X1 - X) * Real.exp (-X1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE]
  have hpos := Real.exp_pos (-X1)
  calc Real.sqrt X1 * Real.exp (-X1) ≤ Real.sqrt X * (1 + (X1 - X)) * Real.exp (-X1) :=
        mul_le_mul_of_nonneg_right hsq hpos.le
    _ ≤ Real.sqrt X * Real.exp (X1 - X) * Real.exp (-X1) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        exact mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
    _ = Real.sqrt X * (Real.exp (X1 - X) * Real.exp (-X1)) := by ring

/-- `e^y ≤ 1/(1 − y)` for `y < 1`. -/
theorem exp_le_inv_one_sub {y : ℝ} (hy : y < 1) : Real.exp y ≤ 1 / (1 - y) := by
  rw [le_div_iff₀ (by linarith)]
  have h := Real.add_one_le_exp (-y)
  calc Real.exp y * (1 - y) ≤ Real.exp y * Real.exp (-y) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- `e^{8.52} ≤ 5250`. -/
theorem exp_852_le : Real.exp 8.52 ≤ 5250 := by
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h8 : Real.exp 8 ≤ 2.7182818286 ^ 8 := by
    have : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le he.le 8
  have h052 : Real.exp 0.52 ≤ (1 / (1 - 0.13)) ^ 4 := by
    have : Real.exp 0.52 = Real.exp 0.13 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_inv_one_sub (by norm_num)) 4
  have hsplit : Real.exp 8.52 = Real.exp 8 * Real.exp 0.52 := by
    rw [← Real.exp_add]
    norm_num
  rw [hsplit]
  calc Real.exp 8 * Real.exp 0.52 ≤ 2.7182818286 ^ 8 * (1 / (1 - 0.13)) ^ 4 :=
        mul_le_mul h8 h052 (Real.exp_pos _).le (by positivity)
    _ ≤ 5250 := by norm_num

/-- With `X = √(log x / R)`: `ε₀(x) = √(8/(17π)) √X e^{−X}`, the target file's definition. -/
theorem eps0_eq (x : ℝ) : Goals.Schoenfeld1976.epsilon0 x =
    Real.sqrt (8 / (17 * π)) * (Real.sqrt (Real.sqrt (Real.log x / 9.645908801)) *
      Real.exp (-Real.sqrt (Real.log x / 9.645908801))) := by
  unfold Goals.Schoenfeld1976.epsilon0 Goals.Schoenfeld1976.X
  ring

/-- `X ≥ 1/2` and `X ≤ Xmax` from bounds on `log x`. -/
theorem X_bounds {x L : ℝ} (hlo : 23 ≤ Real.log x) (hhi : Real.log x ≤ L) {Xmax : ℝ}
    (hXmax : 0 ≤ Xmax) (hL : L / 9.645908801 ≤ Xmax ^ 2) :
    1 / 2 ≤ Real.sqrt (Real.log x / 9.645908801) ∧
      Real.sqrt (Real.log x / 9.645908801) ≤ Xmax := by
  constructor
  · rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ (by norm_num)]
    nlinarith
  · rw [Real.sqrt_le_left hXmax]
    have : Real.log x / 9.645908801 ≤ L / 9.645908801 :=
      div_le_div_of_nonneg_right hhi (by norm_num)
    linarith

/-- `ε₀(x) ≥ 2.1·10⁻⁴` for `e^23 ≤ x ≤ e^700`. -/
theorem eps0_ge {x : ℝ} (hx : Real.exp 23 ≤ x) (hx2 : x ≤ Real.exp 700) :
    2.1e-4 ≤ Goals.Schoenfeld1976.epsilon0 x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 23 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hhi : Real.log x ≤ 700 := (Real.log_le_iff_le_exp hxp).mpr hx2
  obtain ⟨hX1, hX2⟩ := X_bounds hlo hhi (Xmax := 8.52) (by norm_num) (by norm_num)
  have hmono := sqrt_mul_exp_anti hX1 hX2
  have hc0 := (SchoenfeldTheorem11Analytic.c0_bounds).1
  have hs : 2.918 ≤ Real.sqrt 8.52 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he : (5250 : ℝ)⁻¹ ≤ Real.exp (-8.52) := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (by norm_num) (Real.exp_pos _)).mpr exp_852_le
  rw [eps0_eq]
  calc (2.1e-4 : ℝ) ≤ 0.38 * (2.918 * (5250 : ℝ)⁻¹) := by norm_num
    _ ≤ Real.sqrt (8 / (17 * π)) * (Real.sqrt 8.52 * Real.exp (-8.52)) :=
        mul_le_mul hc0 (mul_le_mul hs he (by norm_num) (Real.sqrt_nonneg _)) (by positivity)
          (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)

/-- `ε₀(x) ≥ 0.05` for `e^23 ≤ x ≤ e^28`. -/
theorem eps0_ge_small {x : ℝ} (hx : Real.exp 23 ≤ x) (hx2 : x ≤ Real.exp 28) :
    0.05 ≤ Goals.Schoenfeld1976.epsilon0 x := by

  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 23 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hhi : Real.log x ≤ 28 := (Real.log_le_iff_le_exp hxp).mpr hx2
  obtain ⟨hX1, hX2⟩ := X_bounds hlo hhi (Xmax := 2) (by norm_num) (by norm_num)
  have hmono := sqrt_mul_exp_anti hX1 hX2
  have hc0 := (SchoenfeldTheorem11Analytic.c0_bounds).1
  have hs : 1.41 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have he3 : Real.exp 1 < 3 := SchoenfeldBalanceVNumeric.exp_one_bounds.2
  have he : (9 : ℝ)⁻¹ ≤ Real.exp (-2) := by
    rw [Real.exp_neg]
    apply (inv_le_inv₀ (by norm_num) (Real.exp_pos _)).mpr
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  rw [eps0_eq]
  calc (0.05 : ℝ) ≤ 0.38 * (1.41 * (9 : ℝ)⁻¹) := by norm_num

    _ ≤ Real.sqrt (8 / (17 * π)) * (Real.sqrt 2 * Real.exp (-2)) :=
        mul_le_mul hc0 (mul_le_mul hs he (by norm_num) (Real.sqrt_nonneg _)) (by positivity)
          (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)

/-- `6.5√x ≤ c x` from `√x ≥ 6.5/c`. -/
theorem sqrt_term_le {x c E : ℝ} (hx : 0 < x) (hc : 0 < c) (hE : 6.5 ≤ c * E)
    (hEx : E ≤ Real.sqrt x) : 6.5 * Real.sqrt x ≤ c * x := by
  have hs := Real.mul_self_sqrt hx.le
  have h0 := Real.sqrt_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left hEx (mul_nonneg hc.le h0)]

/-- **Theorem 11, (7.2), for `e^23 ≤ x ≤ e^700`.** -/
theorem psi_lt (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x)
    (hx2 : x ≤ Real.exp 700) :
    |Chebyshev.psi x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h := RosserSchoenfeld1975.psi_error_b23 hRH x hx
  have he := eps0_ge hx hx2
  nlinarith

/-- `|θ(x) − x| ≤ |ψ(x) − x| + 6.5√x` for `x ≥ 10⁵`. -/
theorem theta_err_le {x : ℝ} (hx : 100000 ≤ x) :
    |Chebyshev.theta x - x| ≤ |Chebyshev.psi x - x| + 6.5 * Real.sqrt x := by
  have hpt := PsiThetaElementary.psi_sub_theta_le hx
  have htp := Chebyshev.theta_le_psi x
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Chebyshev.psi x - x)]
  · linarith [le_abs_self (Chebyshev.psi x - x)]

/-- `e^23 ≥ 10⁵`. -/
theorem exp23_ge : (100000 : ℝ) ≤ Real.exp 23 := by
  have he27 : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  have : Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc (100000 : ℝ) ≤ 2.7 ^ 23 := by norm_num
    _ ≤ Real.exp 1 ^ 23 := pow_le_pow_left₀ (by norm_num) he27.le 23


/-- **Theorem 11, (7.3), for `e^23 ≤ x ≤ e^700`.** -/
theorem theta_lt (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x)
    (hx2 : x ≤ Real.exp 700) :
    |Chebyshev.theta x - x| < x * Goals.Schoenfeld1976.epsilon0 x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have h := RosserSchoenfeld1975.psi_error_b23 hRH x hx
  have hth := theta_err_le (le_trans exp23_ge hx)
  have he27 : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  rcases le_or_gt x (Real.exp 28) with hsmall | hlarge

  · -- `√x ≥ e^{11.5} ≥ 65000`, so `6.5√x ≤ 10⁻⁴ x`; and `ε₀(x) ≥ 0.05`.

    have he := eps0_ge_small hx hsmall
    have hE : (65000 : ℝ) ≤ Real.exp 11.5 := by
      have h11 : (2.7 : ℝ) ^ 11 ≤ Real.exp 11 := by
        have : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
        rw [this]
        exact pow_le_pow_left₀ (by norm_num) he27.le 11
      have h05 : (1.5 : ℝ) ≤ Real.exp 0.5 := by linarith [Real.add_one_le_exp (0.5 : ℝ)]
      have hsplit : Real.exp 11.5 = Real.exp 11 * Real.exp 0.5 := by
        rw [← Real.exp_add]
        norm_num
      rw [hsplit]
      nlinarith [Real.exp_pos (11 : ℝ)]
    have hsx : Real.exp 11.5 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (Real.exp_pos _).le hxp.le]
      have : Real.exp 11.5 ^ 2 = Real.exp 23 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      exact hx
    have hst := sqrt_term_le hxp (by norm_num : (0 : ℝ) < 1e-4) (by nlinarith) hsx
    nlinarith
  · -- `√x ≥ e^{14} ≥ 10⁶`, so `6.5√x ≤ 6.5·10⁻⁶ x`; and `ε₀(x) ≥ 2.1·10⁻⁴`.
    have he := eps0_ge hx hx2
    have hE : (1000000 : ℝ) ≤ Real.exp 14 := by
      have : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc (1000000 : ℝ) ≤ 2.7 ^ 14 := by norm_num
        _ ≤ Real.exp 1 ^ 14 := pow_le_pow_left₀ (by norm_num) he27.le 14
    have hsx : Real.exp 14 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (Real.exp_pos _).le hxp.le]
      have : Real.exp 14 ^ 2 = Real.exp 28 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      exact hlarge.le
    have hst := sqrt_term_le hxp (by norm_num : (0 : ℝ) < 6.5e-6) (by nlinarith) hsx
    nlinarith

/-- **Theorem 11, (7.4) as established on p. 349, for `e^23 ≤ x ≤ e^700`.** -/
theorem psi_upper (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 23 ≤ x)
    (hx2 : x ≤ Real.exp 700) :
    Chebyshev.theta x - x ≤ Chebyshev.psi x - x ∧
      Chebyshev.psi x - x < x * Goals.Schoenfeld1976.epsilon0 x :=
  ⟨by linarith [Chebyshev.theta_le_psi x],
    lt_of_le_of_lt (le_abs_self _) (psi_lt hRH hx hx2)⟩

end TernaryGoldbach.RSBounds.SchoenfeldTheorem11B23
