import RSBounds.SchoenfeldTheorem11Ge23

/-!
# Schoenfeld (1976), (5.6b*) for `x ≥ e^1300`, from the far-only quadratic envelope

`Schoenfeld1976Large` gives (5.6b*) for `x ≥ e^1737` from Theorem 11. Below that, the far-only
quadratic envelope (`SchoenfeldQuadraticFar.psi_error_le_farEnvelope`) with a fixed `δ` on each
of three ranges of `log x` (`[1300, 1400]`, `[1400, 1550]`, `[1550, 1737]`) gives
`|ψ(x) − x|, |θ(x) − x| < 0.0077629 x / log x`. These are table rows of order `m = 2`, in the
sense of `docs/SchoenfeldOrderMPlan.md`; the paper's own route uses its table (p. 358).
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Rows2

open SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldQuadraticEnvelope
open SchoenfeldTheorem11Far

/-- The far allowance at `U = 1894438.5122` as `e^{−a/11.63}` times an explicit factor, for
`0 ≤ a ≤ ah ≤ 180.1`. -/
theorem far_le_W {a ah : ℝ} (ha0 : 0 ≤ a) (hah : a ≤ ah) (hah2 : ah ≤ 180.1) :
    farAllowance a 1894438.5122 ≤ Real.exp (-(a / 11.63)) *
      (0.16 * 13.126 * 135.26 / ((266.805 - ah) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3) := by
  obtain ⟨hu0, hu1⟩ := u_bounds
  obtain ⟨hR0, hR1⟩ := rosserR_A_bounds
  obtain ⟨hq0, hqA⟩ := SchoenfeldBalanceTail.q_bounds (le_refl (1894438.5122 : ℝ))
  have hd0 := SchoenfeldBalanceVNumeric.d_nonneg
  have hd1 := SchoenfeldBalanceTail.d_le
  have hpi : 3.1415 < π := by have := Real.pi_gt_d4; linarith
  set u := Real.log (1894438.5122 / 17) with hu
  have hu0' : 0 < u := by linarith
  have hden : 266.805 - ah ≤ 2 * u ^ 2 - a := by nlinarith
  have hden0 : 0 < 266.805 - ah := by linarith
  have hE2u : Real.exp (-(2 * u)) = 289 / 1894438.5122 ^ 2 := by
    have h1 : Real.exp u = 1894438.5122 / 17 := by rw [hu, Real.exp_log (by norm_num)]
    rw [show -(2 * u) = -(u + u) by ring, Real.exp_neg, Real.exp_add, h1]
    norm_num
  set E1 := Real.exp (-(a / u)) with hE1
  have hF : farAllowance a 1894438.5122 =
      E1 * ((1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
          ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3) := by
    unfold farAllowance farPrimitive Phi
    rw [← hu]
    have h1 : Real.exp (-(2 * u + a / u)) = Real.exp (-(2 * u)) * E1 := by
      rw [hE1, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-a / u) = E1 := by rw [hE1, neg_div]
    rw [h1, h2, hE2u]
    have hd : (2 : ℝ) * u ^ 2 - a ≠ 0 := by linarith
    field_simp
    ring
  have hpi2 : 1 / (2 * π) + q 1894438.5122 ≤ 0.16 := by
    have : 1 / (2 * π) ≤ 1 / (2 * 3.1415) := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) (by linarith)
    have hq' : q 1894438.5122 ≤ 0.015 / 1894438.5122 := hqA
    norm_num at this hq' ⊢
    linarith
  have hnum1 : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 ≤
      0.16 * 13.126 * 135.26 := by
    have h1 : 0 ≤ 1 / (2 * π) + q 1894438.5122 := by positivity
    have h2 : u + SchoenfeldWeightedZeros.d + 1 / 2 ≤ 13.126 := by linarith
    have h3 : u ^ 2 ≤ 135.26 := by nlinarith
    have h4 : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 2 := by linarith
    exact mul_le_mul (mul_le_mul hpi2 h2 h4 (by norm_num)) h3 (sq_nonneg u) (by norm_num)
  have hW : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
        ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3 ≤
      0.16 * 13.126 * 135.26 / ((266.805 - ah) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3 := by
    have hfrac : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
        ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) ≤
        0.16 * 13.126 * 135.26 / ((266.805 - ah) * 1894438.5122 ^ 2) := by
      apply div_le_div₀ (by norm_num) hnum1 (by positivity)
      exact mul_le_mul_of_nonneg_right hden (by norm_num)
    have hr : 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3 ≤ 20 / 1894438.5122 ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hWa0 : 0 ≤ (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 2) * u ^ 2 /
        ((2 * u ^ 2 - a) * 1894438.5122 ^ 2) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 3 := by
    have : 0 < 2 * u ^ 2 - a := by linarith
    have : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 2 := by linarith
    positivity
  have hE1le : E1 ≤ Real.exp (-(a / 11.63)) := by
    rw [hE1]
    apply Real.exp_le_exp.mpr
    have : a / 11.63 ≤ a / u := div_le_div_of_nonneg_left ha0 hu0' hu1
    linarith
  rw [hF]
  exact mul_le_mul hE1le hW hWa0 (Real.exp_pos _).le

/-- `e^{n + f} ≥ 2.7182818283^n (1 + f + f²/2 + f³/6)` for `f ≥ 0`. -/
theorem exp_lower (n : ℕ) {f : ℝ} (hf : 0 ≤ f) :
    (2.7182818283 : ℝ) ^ n * (1 + f + f ^ 2 / 2 + f ^ 3 / 6) ≤ Real.exp (n + f) := by
  have he : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hn : (2.7182818283 : ℝ) ^ n ≤ Real.exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) he.le n
  have hT : ∑ i ∈ Finset.range 4, f ^ i / (i.factorial : ℝ) ≤ Real.exp f :=
    Real.sum_le_exp_of_nonneg hf 4
  have hs : ∑ i ∈ Finset.range 4, f ^ i / (i.factorial : ℝ) = 1 + f + f ^ 2 / 2 + f ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hT
  rw [Real.exp_add]
  exact mul_le_mul hn hT (by positivity) (Real.exp_pos _).le

/-- `e^{−y} ≤ 1/L` from `y ≥ n + f` and `L ≤ 2.7182818283^n (1 + f + f²/2 + f³/6)`. -/
theorem exp_neg_le {y L f : ℝ} (n : ℕ) (hf : 0 ≤ f) (hy : n + f ≤ y) (hL : 0 < L)
    (hLe : L ≤ (2.7182818283 : ℝ) ^ n * (1 + f + f ^ 2 / 2 + f ^ 3 / 6)) :
    Real.exp (-y) ≤ 1 / L := by
  rw [Real.exp_neg, one_div]
  apply inv_anti₀ hL
  exact hLe.trans ((exp_lower n hf).trans (Real.exp_le_exp.mpr hy))

set_option maxHeartbeats 1000000 in
/-- **A row of order 2.** If `bl ≤ log x ≤ bh` within `[1300, 1737]` and the stated numerical
inequality holds for `δ`, then `|ψ(x) − x| + 6.5√x ≤ ε x`. -/
theorem row
 (hRH : Goals.FiniteRH 1894438.5122) {x bl bh δ En ε : ℝ} (hbl : 1300 ≤ bl)
    (hbh : bh ≤ 1737) (hx1 : Real.exp bl ≤ x) (hx2 : x ≤ Real.exp bh)
    (hδ0 : 1.5e-6 ≤ δ) (hδ1 : δ ≤ 1e-5)
    (hEn : Real.exp (-(bl / 9.645908801 / 11.63)) ≤ En)
    (hnum : δ + (4 + 12.3 * δ) / δ ^ 2 * (En * (0.16 * 13.126 * 135.26 /
        ((266.805 - bh / 9.645908801) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3)) + 1e-8 ≤ ε) :
    |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ ε * x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hlo : bl ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx1
  have hhi : Real.log x ≤ bh := (Real.log_le_iff_le_exp hxp).mpr hx2
  have hx1' : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by linarith)) hx1
  have hδ : 0 < δ := by linarith
  have hδ2 : 2 * δ < 1 := by linarith
  obtain ⟨a, hadef⟩ : ∃ a, a = Real.log x / 9.645908801 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [hadef]; exact div_nonneg (by linarith) (by norm_num)
  have hah : a ≤ bh / 9.645908801 := by
    rw [hadef]
    exact div_le_div_of_nonneg_right hhi (by norm_num)
  have hal : bl / 9.645908801 ≤ a := by
    rw [hadef]
    exact div_le_div_of_nonneg_right hlo (by norm_num)
  have hah2 : bh / 9.645908801 ≤ 180.1 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hfar : Real.log x / 9.645908801 < 2 * Real.log (1894438.5122 / 17) ^ 2 := by
    rw [← hadef]
    have hu := u_bounds.1
    have : (11.55 : ℝ) * 11.55 ≤ Real.log (1894438.5122 / 17) * Real.log (1894438.5122 / 17) :=
      mul_self_le_mul_self (by norm_num) hu
    nlinarith
  have henv := SchoenfeldQuadraticFar.psi_error_le_farEnvelope hRH hx1' hδ hδ2 hfar
  unfold SchoenfeldQuadraticFar.farEnvelope at henv
  rw [← hadef] at henv
  -- The far allowance.
  have hF := far_le_W ha0 hah hah2
  have hEa : Real.exp (-(a / 11.63)) ≤ En := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hEn
    have : bl / 9.645908801 / 11.63 ≤ a / 11.63 := div_le_div_of_nonneg_right hal (by norm_num)
    linarith
  have hEn0 : 0 ≤ En := le_trans (Real.exp_pos _).le hEn
  have hW0 : 0 ≤ 0.16 * 13.126 * 135.26 / ((266.805 - bh / 9.645908801) * 1894438.5122 ^ 2) +
      20 / 1894438.5122 ^ 3 := by
    have : 0 < 266.805 - bh / 9.645908801 := by linarith
    positivity
  have hF' : farAllowance a 1894438.5122 ≤ En * (0.16 * 13.126 * 135.26 /
      ((266.805 - bh / 9.645908801) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3) :=
    hF.trans (mul_le_mul_of_nonneg_right hEa hW0)
  have hR2 : QuadraticZeroKernel.R2 δ ≤ 4 + 12.3 * δ := SchoenfeldBalanceTail.R2_le hδ.le
    (by linarith)
  have hR20 : 0 ≤ QuadraticZeroKernel.R2 δ := by
    have := SchoenfeldBalanceMain.R2_ge hδ.le
    linarith
  have hRF : QuadraticZeroKernel.R2 δ / δ ^ 2 * farAllowance a 1894438.5122 ≤
      (4 + 12.3 * δ) / δ ^ 2 * (En * (0.16 * 13.126 * 135.26 /
        ((266.805 - bh / 9.645908801) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3)) := by
    calc QuadraticZeroKernel.R2 δ / δ ^ 2 * farAllowance a 1894438.5122
        ≤ QuadraticZeroKernel.R2 δ / δ ^ 2 * (En * (0.16 * 13.126 * 135.26 /
            ((266.805 - bh / 9.645908801) * 1894438.5122 ^ 2) + 20 / 1894438.5122 ^ 3)) :=
          mul_le_mul_of_nonneg_left hF' (div_nonneg hR20 (sq_nonneg δ))
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR2 (sq_nonneg δ))
          (mul_nonneg hEn0 hW0)
  have hxRF := mul_le_mul_of_nonneg_left hRF hxp.le
  -- The negligible terms.
  obtain ⟨X, hXdef⟩ : ∃ X, X = Real.sqrt a := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Real.sqrt_nonneg _
  have hX2 : X ^ 2 = a := by rw [hXdef]; exact Real.sq_sqrt ha0
  have hXlo : 11.5 ≤ X := by
    have h : (11.5 : ℝ) ^ 2 ≤ X ^ 2 := by
      rw [hX2]
      have : (11.5 : ℝ) ^ 2 ≤ bl / 9.645908801 := by
        rw [le_div_iff₀ (by norm_num)]
        nlinarith
      linarith
    nlinarith
  have hlog8 : 8 * X + 80 ≤ Real.log x := by
    have e : Real.log x = 9.645908801 * X ^ 2 := by rw [hX2, hadef]; ring
    have : 11.5 * X ≤ X * X := mul_le_mul_of_nonneg_right hXlo hX0
    nlinarith
  have hE23 : (2.7 : ℝ) ^ 23 ≤ Real.exp X ^ 2 := by
    have he27 : 2.7 < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
    have h1 : Real.exp 23 ≤ Real.exp X ^ 2 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      push_cast
      linarith
    have h2 : (2.7 : ℝ) ^ 23 ≤ Real.exp 23 := by
      have e : Real.exp 23 = Real.exp 1 ^ 23 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      exact pow_le_pow_left₀ (by norm_num) he27.le 23

    linarith
  have hδinv : 1 / δ ^ 2 ≤ 72.25 * Real.exp X ^ 2 := by
    have hδsq : (1.5e-6 : ℝ) ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ (by norm_num) hδ0 2
    have h1 : 1 / δ ^ 2 ≤ 1 / (1.5e-6 : ℝ) ^ 2 := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) hδsq
    have h2 : 1 / (1.5e-6 : ℝ) ^ 2 ≤ 72.25 * (2.7 : ℝ) ^ 23 := by norm_num
    linarith
  have hsmall := SchoenfeldBalanceTail.small_terms_le hx1' (by linarith) hlog8 hδ hδinv hR20
    (by linarith)
  have hsX : Real.sqrt X * Real.exp (-X) / (X + 1) ≤ 1e-4 := by
    have hmono := SchoenfeldTheorem11B23.sqrt_mul_exp_anti (X := 11.5) (X1 := X)
      (by norm_num) hXlo
    have hs115 : Real.sqrt 11.5 ≤ 3.4 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have he115 : Real.exp (-11.5) ≤ 1 / 80000 := by
      have := exp_neg_le (y := 11.5) (L := 80000) (f := 0.5) 11 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
      exact this
    have hs0 : 0 ≤ Real.sqrt X * Real.exp (-X) := by positivity
    calc Real.sqrt X * Real.exp (-X) / (X + 1) ≤ Real.sqrt X * Real.exp (-X) :=
          div_le_self hs0 (by linarith)
      _ ≤ Real.sqrt 11.5 * Real.exp (-11.5) := hmono
      _ ≤ 3.4 * (1 / 80000) := mul_le_mul hs115 he115 (Real.exp_pos _).le (by norm_num)
      _ ≤ 1e-4 := by norm_num
  have hsmall' : 1e-4 * x * (Real.sqrt X * Real.exp (-X) / (X + 1)) ≤ 1e-8 * x := by
    have := mul_le_mul_of_nonneg_left hsX (by positivity : (0 : ℝ) ≤ 1e-4 * x)
    nlinarith
  have hfin := mul_le_mul_of_nonneg_left hnum hxp.le
  nlinarith

/-- **(5.6b*) for `x ≥ e^1300`.** -/
theorem psiThetaLog_ge1300 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 1300 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases le_or_gt (Real.exp 1737) x with hbig | hsmall
  · exact Schoenfeld1976Large.psiThetaLog_large hRH hbig
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 1300 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hl0 : 0 < Real.log x := by linarith
  have h5 : (100000 : ℝ) ≤ x := by
    have := SchoenfeldTheorem11B23.exp23_ge
    have h : Real.exp 23 ≤ Real.exp 1300 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hth := SchoenfeldTheorem11B23.theta_err_le h5
  -- From a row bound `|ψ − x| + 6.5√x ≤ ε x` with `ε · bh < 0.0077629` and `log x ≤ bh`.
  have finish : ∀ ε bh : ℝ, 0 ≤ ε → ε * bh < 0.0077629 → Real.log x ≤ bh →
      |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ ε * x →
      |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
        |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
    intro ε bh hε hεb hlb hrow
    have hsq : 0 ≤ 6.5 * Real.sqrt x := by positivity
    have hlt : ε * x < 0.0077629 * x / Real.log x := by
      rw [lt_div_iff₀ hl0]
      have h1 : ε * Real.log x ≤ ε * bh := mul_le_mul_of_nonneg_left hlb hε
      have h2 : ε * x * Real.log x = x * (ε * Real.log x) := by ring
      rw [h2]
      have h3 : x * (ε * Real.log x) ≤ x * (ε * bh) := mul_le_mul_of_nonneg_left h1 hxp.le
      have h4 : x * (ε * bh) < x * 0.0077629 := mul_lt_mul_of_pos_left hεb hxp
      linarith
    constructor <;> linarith
  rcases le_or_gt x (Real.exp 1400) with h1 | h1
  · apply finish 5.5e-6 1400 (by norm_num) (by norm_num) ((Real.log_le_iff_le_exp hxp).mpr h1)
    exact row hRH (bl := 1300) (bh := 1400) (δ := 3.6e-6) (En := 1 / 107000) (by norm_num)
      (by norm_num) hx h1 (by norm_num) (by norm_num)
      (exp_neg_le (f := 0.588) 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 1550) with h2 | h2
  · apply finish 4.3e-6 1550 (by norm_num) (by norm_num) ((Real.log_le_iff_le_exp hxp).mpr h2)
    exact row hRH (bl := 1400) (bh := 1550) (δ := 2.83e-6) (En := 1 / 262000) (by norm_num)
      (by norm_num) h1.le h2 (by norm_num) (by norm_num)
      (exp_neg_le (f := 0.479) 12 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)
  · apply finish 3e-6 1737 (by norm_num) (by norm_num)
      ((Real.log_le_iff_le_exp hxp).mpr hsmall.le)
    exact row hRH (bl := 1550) (bh := 1737) (δ := 1.94e-6) (En := 1 / 990000) (by norm_num)
      (by norm_num) h2.le hsmall.le (by norm_num) (by norm_num)
      (exp_neg_le (f := 0.816) 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      (by norm_num)

end TernaryGoldbach.RSBounds.Schoenfeld1976Rows2
