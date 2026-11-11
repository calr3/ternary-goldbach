import RSBounds.SchoenfeldSexticFar
import RSBounds.Schoenfeld1976Rows4

/-!
# Schoenfeld (1976), (5.6b*) for `e^313 ≤ x ≤ e^947`, from the far-only sextic envelope

Order 4 is not enough on `[e^313, e^947]` (`Schoenfeld1976Rows4`): there `ε(b)·b` exceeds
`0.0077629` for every quartic step. The order-6 envelope
(`SchoenfeldSexticFar.psi_error_le_farEnvelope6`) with a fixed `δ` on each of eleven ranges of
`log x`,

    [313,457], [457,548], [548,614], [614,668], [668,714], [714,758],
    [758,800], [800,844], [844,892], [892,920], [920,947],

gives `|ψ(x) − x|, |θ(x) − x| < 0.0077629 x / log x` (`psiThetaLog_313_947`). The parameters come
from `scripts/schoenfeld_order6_rows.py` (planning only; Lean checks every inequality).

With `Schoenfeld1976Rows22.psiThetaLog_22_313` and `Schoenfeld1976Rows4.psiThetaLog_ge947`, this
proves the target `Goals.Schoenfeld1976.PsiThetaLog`, that is (5.6b*), for every `x ≥ e^22`
(`psiThetaLog`, `PsiThetaLog_proved`).
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Rows6

open SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldSexticFar SchoenfeldTheorem11Far
open SchoenfeldSexticKernel

/-- The sextic zero-kernel constant for small steps. -/
theorem R6_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1e-3) : R6 δ ≤ 64 + 2800 * δ := by
  have h2 : δ ^ 2 ≤ 1e-3 * δ := by nlinarith
  have h3 : δ ^ 3 ≤ 1e-6 * δ := by
    have : δ ^ 3 = δ * δ ^ 2 := by ring
    nlinarith
  have h4 : δ ^ 4 ≤ 1e-9 * δ := by
    have : δ ^ 4 = δ * δ ^ 3 := by ring
    nlinarith
  have h5 : δ ^ 5 ≤ 1e-12 * δ := by
    have : δ ^ 5 = δ * δ ^ 4 := by ring
    nlinarith
  have h6 : δ ^ 6 ≤ 1e-15 * δ := by
    have : δ ^ 6 = δ * δ ^ 5 := by ring
    nlinarith
  have h7 : δ ^ 7 ≤ 1e-18 * δ := by
    have : δ ^ 7 = δ * δ ^ 6 := by ring
    nlinarith
  have e : (1 + 6 * δ) ^ 7 = 1 + 42 * δ + 756 * δ ^ 2 + 7560 * δ ^ 3 + 45360 * δ ^ 4 +
      163296 * δ ^ 5 + 326592 * δ ^ 6 + 279936 * δ ^ 7 := by ring
  unfold R6
  rw [e]
  linarith

/-- The order-6 far allowance at `A = 1894438.5122` as `e^{−a/11.63}` times an explicit factor, for
`0 ≤ a ≤ ah ≤ 800`. -/
theorem far_le_W6 {a ah : ℝ} (ha0 : 0 ≤ a) (hah : a ≤ ah) (hah2 : ah ≤ 800) :
    farAllowance6 a 1894438.5122 ≤ Real.exp (-(a / 11.63)) *
      (0.16 * 12.793 * 135.26 / ((800.41 - ah) * 1894438.5122 ^ 6) + 20 / 1894438.5122 ^ 7) := by
  obtain ⟨hu0, hu1⟩ := u_bounds
  obtain ⟨hR0, hR1⟩ := rosserR_A_bounds
  obtain ⟨hq0, hqA⟩ := SchoenfeldBalanceTail.q_bounds (le_refl (1894438.5122 : ℝ))
  have hd0 := SchoenfeldBalanceVNumeric.d_nonneg
  have hd1 := SchoenfeldBalanceTail.d_le
  have hpi : 3.1415 < π := by have := Real.pi_gt_d4; linarith
  set u := Real.log (1894438.5122 / 17) with hu
  have hu0' : 0 < u := by linarith
  have hden : 800.41 - ah ≤ 6 * u ^ 2 - a := by nlinarith
  have hden0 : 0 < 800.41 - ah := by linarith
  have hE6u : Real.exp (-(6 * u)) = 17 ^ 6 / 1894438.5122 ^ 6 := by
    have h1 : Real.exp u = 1894438.5122 / 17 := by rw [hu, Real.exp_log (by norm_num)]
    rw [show -(6 * u) = -(u + u + u + u + u + u) by ring, Real.exp_neg, Real.exp_add,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, h1]
    norm_num
  set E1 := Real.exp (-(a / u)) with hE1
  have hF : farAllowance6 a 1894438.5122 =
      E1 * ((1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 6) * u ^ 2 /
          ((6 * u ^ 2 - a) * 1894438.5122 ^ 6) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 7) := by
    unfold farAllowance6 farPrimitive SchoenfeldZeroWeights.Phi
    rw [← hu]
    have h1 : Real.exp (-(6 * u + a / u)) = Real.exp (-(6 * u)) * E1 := by
      rw [hE1, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-a / u) = E1 := by rw [hE1, neg_div]
    rw [h1, h2, hE6u]
    have hd : (6 : ℝ) * u ^ 2 - a ≠ 0 := by linarith
    field_simp
    ring
  have hpi2 : 1 / (2 * π) + q 1894438.5122 ≤ 0.16 := by
    have : 1 / (2 * π) ≤ 1 / (2 * 3.1415) := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) (by linarith)
    have hq' : q 1894438.5122 ≤ 0.015 / 1894438.5122 := hqA
    norm_num at this hq' ⊢
    linarith
  have hnum1 : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 6) * u ^ 2 ≤
      0.16 * 12.793 * 135.26 := by
    have h1 : 0 ≤ 1 / (2 * π) + q 1894438.5122 := by positivity
    have h2 : u + SchoenfeldWeightedZeros.d + 1 / 6 ≤ 12.793 := by linarith
    have h3 : u ^ 2 ≤ 135.26 := by nlinarith
    have h4 : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 6 := by linarith
    exact mul_le_mul (mul_le_mul hpi2 h2 h4 (by norm_num)) h3 (sq_nonneg u) (by norm_num)
  have hW : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 6) * u ^ 2 /
        ((6 * u ^ 2 - a) * 1894438.5122 ^ 6) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 7 ≤
      0.16 * 12.793 * 135.26 / ((800.41 - ah) * 1894438.5122 ^ 6) + 20 / 1894438.5122 ^ 7 := by
    have hfrac : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 6) * u ^ 2 /
        ((6 * u ^ 2 - a) * 1894438.5122 ^ 6) ≤
        0.16 * 12.793 * 135.26 / ((800.41 - ah) * 1894438.5122 ^ 6) := by
      apply div_le_div₀ (by norm_num) hnum1 (by positivity)
      exact mul_le_mul_of_nonneg_right hden (by norm_num)
    have hr : 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 7 ≤ 20 / 1894438.5122 ^ 7 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hWa0 : 0 ≤ (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 6) * u ^ 2 /
        ((6 * u ^ 2 - a) * 1894438.5122 ^ 6) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 7 := by
    have : 0 < 6 * u ^ 2 - a := by linarith
    have : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 6 := by linarith
    positivity
  have hE1le : E1 ≤ Real.exp (-(a / 11.63)) := by
    rw [hE1]
    apply Real.exp_le_exp.mpr
    have : a / 11.63 ≤ a / u := div_le_div_of_nonneg_left ha0 hu0' hu1
    linarith
  rw [hF]
  exact mul_le_mul hE1le hW hWa0 (Real.exp_pos _).le

/-- `√x ≥ 10⁶⁴` for `x ≥ e^300`. -/
theorem sqrt_ge_of_exp300 {x : ℝ} (hx : Real.exp 300 ≤ x) : (1e64 : ℝ) ≤ Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have he : (2.7 : ℝ) < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  have h1 : (1e64 : ℝ) ≤ (2.7 : ℝ) ^ 150 := by norm_num
  have h2 : (2.7 : ℝ) ^ 150 ≤ Real.exp 150 := by
    have e : Real.exp 150 = Real.exp 1 ^ 150 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) he.le 150
  have h4 : Real.exp 150 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (Real.exp_pos 150).le hx0.le).mpr
    have e : Real.exp 150 ^ 2 = Real.exp 300 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact hx
  linarith

/-- The negligible terms of the sextic envelope, for `x ≥ e^300` and `10⁻⁶ ≤ δ ≤ 10⁻⁵`. -/
theorem small_terms_le6 {x δ : ℝ} (hx : Real.exp 300 ≤ x) (hδ0 : 1e-6 ≤ δ) (hδ1 : δ ≤ 1e-5) :
    (R6 δ / δ ^ 6) * Real.sqrt x * (0.0463 / 14.13 ^ 5) + 2300 / (δ ^ 6 * Real.sqrt x) +
      Real.log (2 * Real.pi) + 6.5 * Real.sqrt x ≤ 1e-20 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hs := sqrt_ge_of_exp300 hx
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt x := ⟨_, rfl⟩
  rw [← hsdef] at hs ⊢
  have hs0 : 0 < s := by linarith
  have hxs : x = s ^ 2 := by rw [hsdef, Real.sq_sqrt hx0.le]
  have hδ : 0 < δ := by linarith
  have hδ6 : (1e-36 : ℝ) ≤ δ ^ 6 := by
    calc (1e-36 : ℝ) = (1e-6) ^ 6 := by norm_num
      _ ≤ δ ^ 6 := pow_le_pow_left₀ (by norm_num) hδ0 6
  have hδ6' : 0 < δ ^ 6 := by positivity
  have hR6 : R6 δ ≤ 65 := by
    have := R6_le hδ.le (by linarith)
    linarith
  have hR60 : 0 ≤ R6 δ := R6_nonneg hδ.le
  have hK : R6 δ / δ ^ 6 ≤ 6.5e37 := by
    rw [div_le_iff₀ hδ6']
    nlinarith
  have hss : 1e64 * s ≤ s ^ 2 := by nlinarith
  -- term 1
  have h1 : (R6 δ / δ ^ 6) * s * (0.0463 / 14.13 ^ 5) ≤ 1e-21 * s ^ 2 := by
    have hc : (0.0463 : ℝ) / 14.13 ^ 5 ≤ 1e-7 := by norm_num
    have hc0 : (0 : ℝ) ≤ 0.0463 / 14.13 ^ 5 := by norm_num
    calc (R6 δ / δ ^ 6) * s * (0.0463 / 14.13 ^ 5) ≤ 6.5e37 * s * 1e-7 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hK hs0.le) hc hc0 (by positivity)
      _ ≤ 1e-21 * s ^ 2 := by nlinarith
  -- term 2
  have h2 : 2300 / (δ ^ 6 * s) ≤ 1e-21 * s ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1e-36 * s ≤ δ ^ 6 * s := mul_le_mul_of_nonneg_right hδ6 hs0.le
    have hs3 : 1e64 * s ^ 2 ≤ s ^ 3 := by nlinarith
    nlinarith
  -- term 3
  have h3 : Real.log (2 * Real.pi) ≤ 1e-21 * s ^ 2 := by
    have hl : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hpi := Real.pi_lt_d2
    nlinarith
  -- term 4
  have h4 : 6.5 * s ≤ 1e-21 * s ^ 2 := by nlinarith
  rw [hxs]
  linarith

set_option maxHeartbeats 1000000 in
/-- **A row of order 6.** If `bl ≤ log x ≤ bh` within `[300, 1737]` and the stated numerical
inequality holds for `δ`, then `|ψ(x) − x| + 6.5√x ≤ ε x`. -/
theorem row6
    (hRH : Goals.FiniteRH 1894438.5122) {x bl bh δ En ε : ℝ} (hbl : 300 ≤ bl)
    (hbh : bh ≤ 1737) (hx1 : Real.exp bl ≤ x) (hx2 : x ≤ Real.exp bh)
    (hδ0 : 1e-6 ≤ δ) (hδ1 : δ ≤ 1e-5)
    (hEn : Real.exp (-(bl / 9.645908801 / 11.63)) ≤ En)
    (hnum : 3 * δ + (64 + 2800 * δ) / δ ^ 6 * (En * (0.16 * 12.793 * 135.26 /
        ((800.41 - bh / 9.645908801) * 1894438.5122 ^ 6) + 20 / 1894438.5122 ^ 7)) + 1e-20 ≤ ε) :
    |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ ε * x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hlo : bl ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx1
  have hhi : Real.log x ≤ bh := (Real.log_le_iff_le_exp hxp).mpr hx2
  have hx1' : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by linarith)) hx1
  have hx300 : Real.exp 300 ≤ x := le_trans (Real.exp_le_exp.mpr hbl) hx1
  have hδ : 0 < δ := by linarith
  obtain ⟨a, hadef⟩ : ∃ a, a = Real.log x / 9.645908801 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [hadef]; exact div_nonneg (by linarith) (by norm_num)
  have hah : a ≤ bh / 9.645908801 := by
    rw [hadef]
    exact div_le_div_of_nonneg_right hhi (by norm_num)
  have hal : bl / 9.645908801 ≤ a := by
    rw [hadef]
    exact div_le_div_of_nonneg_right hlo (by norm_num)
  have hah2 : bh / 9.645908801 ≤ 800 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  have hfar : Real.log x / 9.645908801 < 6 * Real.log (1894438.5122 / 17) ^ 2 := by
    rw [← hadef]
    have hu := u_bounds.1
    have : (11.55 : ℝ) * 11.55 ≤ Real.log (1894438.5122 / 17) * Real.log (1894438.5122 / 17) :=
      mul_self_le_mul_self (by norm_num) hu
    have : a ≤ 180.1 := by
      have : bh / 9.645908801 ≤ 180.1 := by
        rw [div_le_iff₀ (by norm_num)]
        linarith
      linarith
    nlinarith
  have henv := psi_error_le_farEnvelope6 hRH hx1' hδ (by linarith) hfar
  unfold farEnvelope6 at henv
  rw [← hadef] at henv
  have hF := far_le_W6 ha0 hah hah2
  have hEa : Real.exp (-(a / 11.63)) ≤ En := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hEn
    have : bl / 9.645908801 / 11.63 ≤ a / 11.63 := div_le_div_of_nonneg_right hal (by norm_num)
    linarith
  have hEn0 : 0 ≤ En := le_trans (Real.exp_pos _).le hEn
  have hW0 : 0 ≤ 0.16 * 12.793 * 135.26 / ((800.41 - bh / 9.645908801) * 1894438.5122 ^ 6) +
      20 / 1894438.5122 ^ 7 := by
    have : 0 < 800.41 - bh / 9.645908801 := by linarith
    positivity
  have hF' : farAllowance6 a 1894438.5122 ≤ En * (0.16 * 12.793 * 135.26 /
      ((800.41 - bh / 9.645908801) * 1894438.5122 ^ 6) + 20 / 1894438.5122 ^ 7) :=
    hF.trans (mul_le_mul_of_nonneg_right hEa hW0)
  have hR6 : R6 δ ≤ 64 + 2800 * δ := R6_le hδ.le (by linarith)
  have hR60 : 0 ≤ R6 δ := R6_nonneg hδ.le
  have hRF : R6 δ / δ ^ 6 * farAllowance6 a 1894438.5122 ≤
      (64 + 2800 * δ) / δ ^ 6 * (En * (0.16 * 12.793 * 135.26 /
        ((800.41 - bh / 9.645908801) * 1894438.5122 ^ 6) + 20 / 1894438.5122 ^ 7)) := by
    calc R6 δ / δ ^ 6 * farAllowance6 a 1894438.5122
        ≤ R6 δ / δ ^ 6 * (En * (0.16 * 12.793 * 135.26 /
            ((800.41 - bh / 9.645908801) * 1894438.5122 ^ 6) + 20 / 1894438.5122 ^ 7)) :=
          mul_le_mul_of_nonneg_left hF' (div_nonneg hR60 (by positivity))
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR6 (by positivity))
          (mul_nonneg hEn0 hW0)
  have hxRF := mul_le_mul_of_nonneg_left hRF hxp.le
  have hsmall := small_terms_le6 hx300 hδ0 hδ1
  have hfin := mul_le_mul_of_nonneg_left hnum hxp.le
  nlinarith

/-- **(5.6b*) for `e^313 ≤ x ≤ e^947`**, from eleven rows of order 6. -/
theorem psiThetaLog_313_947 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 313 ≤ x)
    (hx' : x ≤ Real.exp 947) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 313 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hl0 : 0 < Real.log x := by linarith
  have h5 : (100000 : ℝ) ≤ x := by
    have := SchoenfeldTheorem11B23.exp23_ge
    have h : Real.exp 23 ≤ Real.exp 313 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  rcases le_or_gt x (Real.exp 457) with h1 | h1
  · apply Schoenfeld1976Rows4.finish h5 (ε := 1.698e-5) (bh := 457) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h1)
    exact row6 hRH (bl := 313) (bh := 457) (δ := 4.85e-6) (En := 1 / 16.139) (by norm_num)
      (by norm_num) hx h1 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.79) 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 548) with h2 | h2
  · apply Schoenfeld1976Rows4.finish h5 (ε := 1.414e-5) (bh := 548) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h2)
    exact row6 hRH (bl := 457) (bh := 548) (δ := 4.04e-6) (En := 1 / 58.732) (by norm_num)
      (by norm_num) h1.le h2 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.073) 4 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 614) with h3 | h3
  · apply Schoenfeld1976Rows4.finish h5 (ε := 1.264e-5) (bh := 614) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h3)
    exact row6 hRH (bl := 548) (bh := 614) (δ := 3.61e-6) (En := 1 / 130.482) (by norm_num)
      (by norm_num) h2.le h3 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.884) 4 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 668) with h4 | h4
  · apply Schoenfeld1976Rows4.finish h5 (ε := 1.161e-5) (bh := 668) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h4)
    exact row6 hRH (bl := 614) (bh := 668) (δ := 3.32e-6) (En := 1 / 237.832) (by norm_num)
      (by norm_num) h3.le h4 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.473) 5 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 714) with h5' | h5'
  · apply Schoenfeld1976Rows4.finish h5 (ε := 1.087e-5) (bh := 714) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h5')
    exact row6 hRH (bl := 668) (bh := 714) (δ := 3.1e-6) (En := 1 / 379.012) (by norm_num)
      (by norm_num) h4.le h5' (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.954) 5 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 758) with h6 | h6
  · apply Schoenfeld1976Rows4.finish h5 (ε := 1.024e-5) (bh := 758) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h6)
    exact row6 hRH (bl := 714) (bh := 758) (δ := 2.93e-6) (En := 1 / 580.246) (by norm_num)
      (by norm_num) h5'.le h6 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.364) 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 800) with h7 | h7
  · apply Schoenfeld1976Rows4.finish h5 (ε := 9.698e-6) (bh := 800) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h7)
    exact row6 hRH (bl := 758) (bh := 800) (δ := 2.77e-6) (En := 1 / 852.76) (by norm_num)
      (by norm_num) h6.le h7 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.756) 6 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 844) with h8 | h8
  · apply Schoenfeld1976Rows4.finish h5 (ε := 9.19e-6) (bh := 844) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h8)
    exact row6 hRH (bl := 800) (bh := 844) (δ := 2.63e-6) (En := 1 / 1250.112) (by norm_num)
      (by norm_num) h7.le h8 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.131) 7 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 892) with h9 | h9
  · apply Schoenfeld1976Rows4.finish h5 (ε := 8.701e-6) (bh := 892) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h9)
    exact row6 hRH (bl := 844) (bh := 892) (δ := 2.49e-6) (En := 1 / 1846.299) (by norm_num)
      (by norm_num) h8.le h9 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.523) 7 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 920) with h10 | h10
  · apply Schoenfeld1976Rows4.finish h5 (ε := 8.206e-6) (bh := 920) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr h10)
    exact row6 hRH (bl := 892) (bh := 920) (δ := 2.345e-6) (En := 1 / 2792.629) (by norm_num)
      (by norm_num) h9.le h10 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.951) 7 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  · apply Schoenfeld1976Rows4.finish h5 (ε := 7.906e-6) (bh := 947) (by norm_num) (by norm_num)
      hl0 ((Real.log_le_iff_le_exp hxp).mpr hx')
    exact row6 hRH (bl := 920) (bh := 947) (δ := 2.25e-6) (En := 1 / 3640.743) (by norm_num)
      (by norm_num) h10.le hx' (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.2) 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)

end TernaryGoldbach.RSBounds.Schoenfeld1976Rows6
