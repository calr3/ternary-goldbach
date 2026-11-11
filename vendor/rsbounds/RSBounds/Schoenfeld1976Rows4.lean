import RSBounds.SchoenfeldQuarticFar
import RSBounds.Schoenfeld1976Rows2

/-!
# Schoenfeld (1976), (5.6b*) for `x ≥ e^947`, from the far-only quartic envelope

`Schoenfeld1976Rows2` gives (5.6b*) for `x ≥ e^1300` from the order-2 far-only envelope. Below
that, the order-4 envelope (`SchoenfeldQuarticFar.psi_error_le_farEnvelope4`) with a fixed `δ` on
each of six ranges of `log x` (`[947, 957]`, `[957, 973]`, `[973, 1000]`, `[1000, 1046]`,
`[1046, 1129]`, `[1129, 1300]`) gives `|ψ(x) − x|, |θ(x) − x| < 0.0077629 x / log x`. These are
table rows of order `m = 4` in the sense of `docs/SchoenfeldOrderMPlan.md`. The order-4 envelope
cannot go much lower: with these constants its rows stop working near `log x = 921`.

The same envelope also works on a lower window. There the critical-line term
`(R4 δ/δ⁴) √x · 0.0463/14.13³` is no longer negligible and is kept (`row4low`): five rows
(`[100, 210]`, `[210, 265]`, `[265, 292]`, `[292, 306]`, `[306, 313]`) give (5.6b*) for
`e^100 ≤ x ≤ e^313` (`psiThetaLog_100_313`). Between `e^313` and `e^947` order 4 is not enough.
-/

open Real

namespace TernaryGoldbach.RSBounds.Schoenfeld1976Rows4

open SchoenfeldLaplaceTails SchoenfeldZeroWeights SchoenfeldQuarticFar SchoenfeldTheorem11Far
open PolynomialZeroKernel

/-- The quartic zero-kernel constant for small steps. -/
theorem R4_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1e-3) : R4 δ ≤ 16 + 200 * δ := by
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
  have hp : (1 + δ) ^ 5 + 1 ≤ 2 + 6 * δ := by
    have e : (1 + δ) ^ 5 = 1 + 5 * δ + 10 * δ ^ 2 + 10 * δ ^ 3 + 5 * δ ^ 4 + δ ^ 5 := by ring
    rw [e]
    linarith
  have hp0 : 0 ≤ (1 + δ) ^ 5 + 1 := by positivity
  have hq : ((1 + δ) ^ 5 + 1) ^ 4 ≤ (2 + 6 * δ) ^ 4 := pow_le_pow_left₀ hp0 hp 4
  have e2 : (2 + 6 * δ) ^ 4 = 16 + 192 * δ + 864 * δ ^ 2 + 1728 * δ ^ 3 + 1296 * δ ^ 4 := by ring
  unfold R4
  rw [e2] at hq
  linarith

/-- The order-4 far allowance at `A = 1894438.5122` as `e^{−a/11.63}` times an explicit factor, for
`0 ≤ a ≤ ah ≤ 180.1`. -/
theorem far_le_W4 {a ah : ℝ} (ha0 : 0 ≤ a) (hah : a ≤ ah) (hah2 : ah ≤ 180.1) :
    farAllowance4 a 1894438.5122 ≤ Real.exp (-(a / 11.63)) *
      (0.16 * 12.876 * 135.26 / ((533.61 - ah) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5) := by
  obtain ⟨hu0, hu1⟩ := u_bounds
  obtain ⟨hR0, hR1⟩ := rosserR_A_bounds
  obtain ⟨hq0, hqA⟩ := SchoenfeldBalanceTail.q_bounds (le_refl (1894438.5122 : ℝ))
  have hd0 := SchoenfeldBalanceVNumeric.d_nonneg
  have hd1 := SchoenfeldBalanceTail.d_le
  have hpi : 3.1415 < π := by have := Real.pi_gt_d4; linarith
  set u := Real.log (1894438.5122 / 17) with hu
  have hu0' : 0 < u := by linarith
  have hden : 533.61 - ah ≤ 4 * u ^ 2 - a := by nlinarith
  have hden0 : 0 < 533.61 - ah := by linarith
  have hE4u : Real.exp (-(4 * u)) = 17 ^ 4 / 1894438.5122 ^ 4 := by
    have h1 : Real.exp u = 1894438.5122 / 17 := by rw [hu, Real.exp_log (by norm_num)]
    rw [show -(4 * u) = -(u + u + u + u) by ring, Real.exp_neg, Real.exp_add, Real.exp_add,
      Real.exp_add, h1]
    norm_num
  set E1 := Real.exp (-(a / u)) with hE1
  have hF : farAllowance4 a 1894438.5122 =
      E1 * ((1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 4) * u ^ 2 /
          ((4 * u ^ 2 - a) * 1894438.5122 ^ 4) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 5) := by
    unfold farAllowance4 farPrimitive SchoenfeldZeroWeights.Phi
    rw [← hu]
    have h1 : Real.exp (-(4 * u + a / u)) = Real.exp (-(4 * u)) * E1 := by
      rw [hE1, ← Real.exp_add]
      congr 1
      ring
    have h2 : Real.exp (-a / u) = E1 := by rw [hE1, neg_div]
    rw [h1, h2, hE4u]
    have hd : (4 : ℝ) * u ^ 2 - a ≠ 0 := by linarith
    field_simp
    ring
  have hpi2 : 1 / (2 * π) + q 1894438.5122 ≤ 0.16 := by
    have : 1 / (2 * π) ≤ 1 / (2 * 3.1415) := div_le_div_of_nonneg_left (by norm_num)
      (by norm_num) (by linarith)
    have hq' : q 1894438.5122 ≤ 0.015 / 1894438.5122 := hqA
    norm_num at this hq' ⊢
    linarith
  have hnum1 : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 4) * u ^ 2 ≤
      0.16 * 12.876 * 135.26 := by
    have h1 : 0 ≤ 1 / (2 * π) + q 1894438.5122 := by positivity
    have h2 : u + SchoenfeldWeightedZeros.d + 1 / 4 ≤ 12.876 := by linarith
    have h3 : u ^ 2 ≤ 135.26 := by nlinarith
    have h4 : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 4 := by linarith
    exact mul_le_mul (mul_le_mul hpi2 h2 h4 (by norm_num)) h3 (sq_nonneg u) (by norm_num)
  have hW : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 4) * u ^ 2 /
        ((4 * u ^ 2 - a) * 1894438.5122 ^ 4) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 5 ≤
      0.16 * 12.876 * 135.26 / ((533.61 - ah) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5 := by
    have hfrac : (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 4) * u ^ 2 /
        ((4 * u ^ 2 - a) * 1894438.5122 ^ 4) ≤
        0.16 * 12.876 * 135.26 / ((533.61 - ah) * 1894438.5122 ^ 4) := by
      apply div_le_div₀ (by norm_num) hnum1 (by positivity)
      exact mul_le_mul_of_nonneg_right hden (by norm_num)
    have hr : 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 5 ≤ 20 / 1894438.5122 ^ 5 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith
  have hWa0 : 0 ≤ (1 / (2 * π) + q 1894438.5122) * (u + SchoenfeldWeightedZeros.d + 1 / 4) * u ^ 2 /
        ((4 * u ^ 2 - a) * 1894438.5122 ^ 4) + 2 * rosserR 1.588 1894438.5122 / 1894438.5122 ^ 5 := by
    have : 0 < 4 * u ^ 2 - a := by linarith
    have : 0 ≤ u + SchoenfeldWeightedZeros.d + 1 / 4 := by linarith
    positivity
  have hE1le : E1 ≤ Real.exp (-(a / 11.63)) := by
    rw [hE1]
    apply Real.exp_le_exp.mpr
    have : a / 11.63 ≤ a / u := div_le_div_of_nonneg_left ha0 hu0' hu1
    linarith
  rw [hF]
  exact mul_le_mul hE1le hW hWa0 (Real.exp_pos _).le

/-- `√x ≥ 10⁴³` for `x ≥ e^900`. -/
theorem sqrt_ge_of_exp900 {x : ℝ} (hx : Real.exp 900 ≤ x) : (1e43 : ℝ) ≤ Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have he : (2.7 : ℝ) < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  have h1 : (1e43 : ℝ) ≤ (2.7 : ℝ) ^ 100 := by norm_num
  have h2 : (2.7 : ℝ) ^ 100 ≤ Real.exp 100 := by
    have e : Real.exp 100 = Real.exp 1 ^ 100 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) he.le 100
  have h3 : Real.exp 100 ≤ Real.exp 450 := Real.exp_le_exp.mpr (by norm_num)
  have h4 : Real.exp 450 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (Real.exp_pos 450).le hx0.le).mpr
    have e : Real.exp 450 ^ 2 = Real.exp 900 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact hx
  linarith

/-- The negligible terms of the quartic envelope, for `x ≥ e^900` and `10⁻⁶ ≤ δ ≤ 10⁻⁵`. -/
theorem small_terms_le4 {x δ : ℝ} (hx : Real.exp 900 ≤ x) (hδ0 : 1e-6 ≤ δ) (hδ1 : δ ≤ 1e-5) :
    (R4 δ / δ ^ 4) * Real.sqrt x * (0.0463 / 14.13 ^ 3) + 700 / (δ ^ 4 * Real.sqrt x) +
      Real.log (2 * Real.pi) + 6.5 * Real.sqrt x ≤ 1e-8 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hs := sqrt_ge_of_exp900 hx
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt x := ⟨_, rfl⟩
  rw [← hsdef] at hs ⊢
  have hs0 : 0 < s := by linarith
  have hxs : x = s ^ 2 := by rw [hsdef, Real.sq_sqrt hx0.le]
  have hδ : 0 < δ := by linarith
  have hδ4 : (1e-24 : ℝ) ≤ δ ^ 4 := by
    calc (1e-24 : ℝ) = (1e-6) ^ 4 := by norm_num
      _ ≤ δ ^ 4 := pow_le_pow_left₀ (by norm_num) hδ0 4
  have hδ4' : 0 < δ ^ 4 := by positivity
  have hR4 : R4 δ ≤ 17 := by
    have := R4_le hδ.le (by linarith)
    linarith
  have hR40 : 0 ≤ R4 δ := by unfold R4; positivity
  have hK : R4 δ / δ ^ 4 ≤ 1.7e25 := by
    rw [div_le_iff₀ hδ4']
    nlinarith
  have hK0 : 0 ≤ R4 δ / δ ^ 4 := div_nonneg hR40 hδ4'.le
  have hss : 1e43 * s ≤ s ^ 2 := by nlinarith
  -- term 1
  have h1 : (R4 δ / δ ^ 4) * s * (0.0463 / 14.13 ^ 3) ≤ 1e-22 * s ^ 2 := by
    have hc : (0.0463 : ℝ) / 14.13 ^ 3 ≤ 1.7e-5 := by norm_num
    have hc0 : (0 : ℝ) ≤ 0.0463 / 14.13 ^ 3 := by norm_num
    calc (R4 δ / δ ^ 4) * s * (0.0463 / 14.13 ^ 3) ≤ 1.7e25 * s * 1.7e-5 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hK hs0.le) hc hc0 (by positivity)
      _ ≤ 1e-22 * s ^ 2 := by nlinarith
  -- term 2
  have h2 : 700 / (δ ^ 4 * s) ≤ 1e-16 * s ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1e-24 * s ≤ δ ^ 4 * s := mul_le_mul_of_nonneg_right hδ4 hs0.le
    have hs3 : 1e43 * s ^ 2 ≤ s ^ 3 := by nlinarith
    nlinarith
  -- term 3
  have h3 : Real.log (2 * Real.pi) ≤ 1e-16 * s ^ 2 := by
    have hl : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hpi := Real.pi_lt_d2
    nlinarith
  -- term 4
  have h4 : 6.5 * s ≤ 1e-16 * s ^ 2 := by nlinarith
  rw [hxs]
  linarith

set_option maxHeartbeats 1000000 in
/-- **A row of order 4.** If `bl ≤ log x ≤ bh` within `[900, 1737]` and the stated numerical
inequality holds for `δ`, then `|ψ(x) − x| + 6.5√x ≤ ε x`. -/
theorem row4
    (hRH : Goals.FiniteRH 1894438.5122) {x bl bh δ En ε : ℝ} (hbl : 900 ≤ bl)
    (hbh : bh ≤ 1737) (hx1 : Real.exp bl ≤ x) (hx2 : x ≤ Real.exp bh)
    (hδ0 : 1e-6 ≤ δ) (hδ1 : δ ≤ 1e-5)
    (hEn : Real.exp (-(bl / 9.645908801 / 11.63)) ≤ En)
    (hnum : 2 * δ + (16 + 200 * δ) / δ ^ 4 * (En * (0.16 * 12.876 * 135.26 /
        ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5)) + 1e-8 ≤ ε) :
    |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ ε * x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hlo : bl ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx1
  have hhi : Real.log x ≤ bh := (Real.log_le_iff_le_exp hxp).mpr hx2
  have hx1' : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by linarith)) hx1
  have hx900 : Real.exp 900 ≤ x := le_trans (Real.exp_le_exp.mpr hbl) hx1
  have hδ : 0 < δ := by linarith
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
  have hfar : Real.log x / 9.645908801 < 4 * Real.log (1894438.5122 / 17) ^ 2 := by
    rw [← hadef]
    have hu := u_bounds.1
    have : (11.55 : ℝ) * 11.55 ≤ Real.log (1894438.5122 / 17) * Real.log (1894438.5122 / 17) :=
      mul_self_le_mul_self (by norm_num) hu
    nlinarith
  have henv := psi_error_le_farEnvelope4 hRH hx1' hδ (by linarith) hfar
  unfold farEnvelope4 at henv
  rw [← hadef] at henv
  have hF := far_le_W4 ha0 hah hah2
  have hEa : Real.exp (-(a / 11.63)) ≤ En := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hEn
    have : bl / 9.645908801 / 11.63 ≤ a / 11.63 := div_le_div_of_nonneg_right hal (by norm_num)
    linarith
  have hEn0 : 0 ≤ En := le_trans (Real.exp_pos _).le hEn
  have hW0 : 0 ≤ 0.16 * 12.876 * 135.26 / ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) +
      20 / 1894438.5122 ^ 5 := by
    have : 0 < 533.61 - bh / 9.645908801 := by linarith
    positivity
  have hF' : farAllowance4 a 1894438.5122 ≤ En * (0.16 * 12.876 * 135.26 /
      ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5) :=
    hF.trans (mul_le_mul_of_nonneg_right hEa hW0)
  have hR4 : R4 δ ≤ 16 + 200 * δ := R4_le hδ.le (by linarith)
  have hR40 : 0 ≤ R4 δ := by unfold R4; positivity
  have hRF : R4 δ / δ ^ 4 * farAllowance4 a 1894438.5122 ≤
      (16 + 200 * δ) / δ ^ 4 * (En * (0.16 * 12.876 * 135.26 /
        ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5)) := by
    calc R4 δ / δ ^ 4 * farAllowance4 a 1894438.5122
        ≤ R4 δ / δ ^ 4 * (En * (0.16 * 12.876 * 135.26 /
            ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5)) :=
          mul_le_mul_of_nonneg_left hF' (div_nonneg hR40 (by positivity))
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hR4 (by positivity))
          (mul_nonneg hEn0 hW0)
  have hxRF := mul_le_mul_of_nonneg_left hRF hxp.le
  have hsmall := small_terms_le4 hx900 hδ0 hδ1
  have hfin := mul_le_mul_of_nonneg_left hnum hxp.le
  nlinarith

/-- `√x ≥ 3·10²¹` for `x ≥ e^100`. -/
theorem sqrt_ge_of_exp100 {x : ℝ} (hx : Real.exp 100 ≤ x) : (3e21 : ℝ) ≤ Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have he : (2.7 : ℝ) < Real.exp 1 := SchoenfeldBalanceVNumeric.exp_one_bounds.1
  have h1 : (3e21 : ℝ) ≤ (2.7 : ℝ) ^ 50 := by norm_num
  have h2 : (2.7 : ℝ) ^ 50 ≤ Real.exp 50 := by
    have e : Real.exp 50 = Real.exp 1 ^ 50 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) he.le 50
  have h4 : Real.exp 50 ≤ Real.sqrt x := by
    apply (Real.le_sqrt (Real.exp_pos 50).le hx0.le).mpr
    have e : Real.exp 50 ^ 2 = Real.exp 100 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact hx
  linarith

/-- The negligible terms for `x ≥ e^100` and `10⁻⁶ ≤ δ ≤ 10⁻⁴` (the critical-line term is kept
separately in `row4low`). -/
theorem small_terms_low {x δ : ℝ} (hx : Real.exp 100 ≤ x) (hδ0 : 1e-6 ≤ δ) :
    700 / (δ ^ 4 * Real.sqrt x) + Real.log (2 * Real.pi) + 6.5 * Real.sqrt x ≤ 1e-10 * x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hs := sqrt_ge_of_exp100 hx
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt x := ⟨_, rfl⟩
  rw [← hsdef] at hs ⊢
  have hs0 : 0 < s := by linarith
  have hxs : x = s ^ 2 := by rw [hsdef, Real.sq_sqrt hx0.le]
  have hδ4 : (1e-24 : ℝ) ≤ δ ^ 4 := by
    calc (1e-24 : ℝ) = (1e-6) ^ 4 := by norm_num
      _ ≤ δ ^ 4 := pow_le_pow_left₀ (by norm_num) hδ0 4
  have hss : 3e21 * s ≤ s ^ 2 := by nlinarith
  have h2 : 700 / (δ ^ 4 * s) ≤ 1e-11 * s ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1e-24 * s ≤ δ ^ 4 * s := mul_le_mul_of_nonneg_right hδ4 hs0.le
    have hs3 : 3e21 * s ^ 2 ≤ s ^ 3 := by nlinarith
    nlinarith
  have h3 : Real.log (2 * Real.pi) ≤ 1e-11 * s ^ 2 := by
    have hl : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hpi := Real.pi_lt_d2
    nlinarith
  have h4 : 6.5 * s ≤ 1e-11 * s ^ 2 := by nlinarith
  rw [hxs]
  linarith

set_option maxHeartbeats 1000000 in
/-- **A low row of order 4**, for `100 ≤ log x`, keeping the critical-line term
`(R4 δ/δ⁴) √x · 0.0463/14.13³ ≤ x (R4 δ/δ⁴) · 0.0463/14.13³ · e^{−bl/2}`. -/
theorem row4low
    (hRH : Goals.FiniteRH 1894438.5122) {x bl bh δ En Ec ε : ℝ} (hbl : 100 ≤ bl)
    (hbh : bh ≤ 1737) (hx1 : Real.exp bl ≤ x) (hx2 : x ≤ Real.exp bh)
    (hδ0 : 1e-6 ≤ δ) (hδ1 : δ ≤ 1e-4)
    (hEn : Real.exp (-(bl / 9.645908801 / 11.63)) ≤ En)
    (hEc : Real.exp (-(bl / 2)) ≤ Ec)
    (hnum : 2 * δ + (16 + 200 * δ) / δ ^ 4 * (Ec * (0.0463 / 14.13 ^ 3) +
        En * (0.16 * 12.876 * 135.26 / ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) +
          20 / 1894438.5122 ^ 5)) + 1e-10 ≤ ε) :
    |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ ε * x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hlo : bl ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx1
  have hhi : Real.log x ≤ bh := (Real.log_le_iff_le_exp hxp).mpr hx2
  have hx1' : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by linarith)) hx1
  have hx100 : Real.exp 100 ≤ x := le_trans (Real.exp_le_exp.mpr hbl) hx1
  have hδ : 0 < δ := by linarith
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
  have hfar : Real.log x / 9.645908801 < 4 * Real.log (1894438.5122 / 17) ^ 2 := by
    rw [← hadef]
    have hu := u_bounds.1
    have : (11.55 : ℝ) * 11.55 ≤ Real.log (1894438.5122 / 17) * Real.log (1894438.5122 / 17) :=
      mul_self_le_mul_self (by norm_num) hu
    nlinarith
  have henv := psi_error_le_farEnvelope4 hRH hx1' hδ (by linarith) hfar
  unfold farEnvelope4 at henv
  rw [← hadef] at henv
  have hF := far_le_W4 ha0 hah hah2
  have hEa : Real.exp (-(a / 11.63)) ≤ En := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hEn
    have : bl / 9.645908801 / 11.63 ≤ a / 11.63 := div_le_div_of_nonneg_right hal (by norm_num)
    linarith
  have hEn0 : 0 ≤ En := le_trans (Real.exp_pos _).le hEn
  have hW0 : 0 ≤ 0.16 * 12.876 * 135.26 / ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) +
      20 / 1894438.5122 ^ 5 := by
    have : 0 < 533.61 - bh / 9.645908801 := by linarith
    positivity
  have hF' : farAllowance4 a 1894438.5122 ≤ En * (0.16 * 12.876 * 135.26 /
      ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5) :=
    hF.trans (mul_le_mul_of_nonneg_right hEa hW0)
  have hR4 : R4 δ ≤ 16 + 200 * δ := R4_le hδ.le (by linarith)
  have hR40 : 0 ≤ R4 δ := by unfold R4; positivity
  have hK0 : 0 ≤ R4 δ / δ ^ 4 := div_nonneg hR40 (by positivity)
  have hK : R4 δ / δ ^ 4 ≤ (16 + 200 * δ) / δ ^ 4 :=
    div_le_div_of_nonneg_right hR4 (by positivity)
  -- The critical-line term.
  obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt x := ⟨_, rfl⟩
  rw [← hsdef] at henv
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hxp
  have hxs : x = s * s := by rw [hsdef, Real.mul_self_sqrt hxp.le]
  have hsE : 1 ≤ s * Ec := by
    have h1 : Real.exp (bl / 2) ≤ s := by
      rw [hsdef]
      apply (Real.le_sqrt (Real.exp_pos _).le hxp.le).mpr
      have e : Real.exp (bl / 2) ^ 2 = Real.exp bl := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [e]
      exact hx1
    have h2 : Real.exp (bl / 2) * Real.exp (-(bl / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hEc0 : 0 ≤ Real.exp (-(bl / 2)) := (Real.exp_pos _).le
    calc (1 : ℝ) = Real.exp (bl / 2) * Real.exp (-(bl / 2)) := h2.symm
      _ ≤ s * Ec := mul_le_mul h1 hEc hEc0 hs0.le
  have hc0 : (0 : ℝ) ≤ 0.0463 / 14.13 ^ 3 := by norm_num
  have hcrit : R4 δ / δ ^ 4 * s * (0.0463 / 14.13 ^ 3) ≤
      x * ((16 + 200 * δ) / δ ^ 4 * (Ec * (0.0463 / 14.13 ^ 3))) := by
    have hEc0 : 0 ≤ Ec := le_trans (Real.exp_pos _).le hEc
    calc R4 δ / δ ^ 4 * s * (0.0463 / 14.13 ^ 3)
        ≤ R4 δ / δ ^ 4 * s * (0.0463 / 14.13 ^ 3) * (s * Ec) :=
          le_mul_of_one_le_right (by positivity) hsE
      _ = (s * s) * (R4 δ / δ ^ 4 * (Ec * (0.0463 / 14.13 ^ 3))) := by ring
      _ ≤ (s * s) * ((16 + 200 * δ) / δ ^ 4 * (Ec * (0.0463 / 14.13 ^ 3))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK (by positivity))
            (by positivity)
      _ = _ := by rw [hxs]
  -- The far term.
  have hRF : R4 δ / δ ^ 4 * farAllowance4 a 1894438.5122 ≤
      (16 + 200 * δ) / δ ^ 4 * (En * (0.16 * 12.876 * 135.26 /
        ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5)) := by
    calc R4 δ / δ ^ 4 * farAllowance4 a 1894438.5122
        ≤ R4 δ / δ ^ 4 * (En * (0.16 * 12.876 * 135.26 /
            ((533.61 - bh / 9.645908801) * 1894438.5122 ^ 4) + 20 / 1894438.5122 ^ 5)) :=
          mul_le_mul_of_nonneg_left hF' hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (mul_nonneg hEn0 hW0)
  have hxRF := mul_le_mul_of_nonneg_left hRF hxp.le
  have hsmall := small_terms_low hx100 hδ0
  rw [← hsdef] at hsmall
  have hfin := mul_le_mul_of_nonneg_left hnum hxp.le
  nlinarith

/-- From a row bound `|ψ − x| + 6.5√x ≤ ε x` with `ε · bh < 0.0077629` and `log x ≤ bh`, the
(5.6b*) inequalities for `ψ` and `θ`. -/
theorem finish {x ε bh : ℝ} (hx : 100000 ≤ x) (hε : 0 ≤ ε) (hεb : ε * bh < 0.0077629)
    (hl0 : 0 < Real.log x) (hlb : Real.log x ≤ bh)
    (hrow : |Chebyshev.psi x - x| + 6.5 * Real.sqrt x ≤ ε * x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hxp : 0 < x := by linarith
  have hth := SchoenfeldTheorem11B23.theta_err_le hx
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

/-- **(5.6b*) for `x ≥ e^947`.** -/
theorem psiThetaLog_ge947 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 947 ≤ x) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  rcases le_or_gt (Real.exp 1300) x with hbig | hsmall
  · exact Schoenfeld1976Rows2.psiThetaLog_ge1300 hRH hbig
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 947 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hl0 : 0 < Real.log x := by linarith
  have h5 : (100000 : ℝ) ≤ x := by
    have := SchoenfeldTheorem11B23.exp23_ge
    have h : Real.exp 23 ≤ Real.exp 947 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  rcases le_or_gt x (Real.exp 957) with h1 | h1
  · apply finish h5 (ε := 8.06e-6) (bh := 957) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h1)
    exact row4 hRH (bl := 947) (bh := 957) (δ := 3.22e-6) (En := 1 / 4620) (by norm_num)
      (by norm_num) hx h1 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.441) 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 973) with h2 | h2
  · apply finish h5 (ε := 7.92e-6) (bh := 973) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h2)
    exact row4 hRH (bl := 957) (bh := 973) (δ := 3.16e-6) (En := 1 / 5050) (by norm_num)
      (by norm_num) h1.le h2 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.53) 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 1000) with h3 | h3
  · apply finish h5 (ε := 7.71e-6) (bh := 1000) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h3)
    exact row4 hRH (bl := 973) (bh := 1000) (δ := 3.08e-6) (En := 1 / 5810) (by norm_num)
      (by norm_num) h2.le h3 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.673) 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 1046) with h4 | h4
  · apply finish h5 (ε := 7.38e-6) (bh := 1046) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h4)
    exact row4 hRH (bl := 1000) (bh := 1046) (δ := 2.95e-6) (En := 1 / 7330) (by norm_num)
      (by norm_num) h3.le h4 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.914) 8 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 1129) with h6 | h6
  · apply finish h5 (ε := 6.82e-6) (bh := 1129) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h6)
    exact row4 hRH (bl := 1046) (bh := 1129) (δ := 2.72e-6) (En := 1 / 11100) (by norm_num)
      (by norm_num) h4.le h6 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.324) 9 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  · apply finish h5 (ε := 5.93e-6) (bh := 1300) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr hsmall.le)
    exact row4 hRH (bl := 1129) (bh := 1300) (δ := 2.37e-6) (En := 1 / 23400) (by norm_num)
      (by norm_num) h6.le hsmall.le (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.064) 10 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)

/-- **(5.6b*) for `e^100 ≤ x ≤ e^313`**, from five low rows of order 4. -/
theorem psiThetaLog_100_313 (hRH : Goals.FiniteRH 1894438.5122) {x : ℝ} (hx : Real.exp 100 ≤ x)
    (hx' : x ≤ Real.exp 313) :
    |Chebyshev.psi x - x| < 0.0077629 * x / Real.log x ∧
      |Chebyshev.theta x - x| < 0.0077629 * x / Real.log x := by
  have hxp : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hlo : 100 ≤ Real.log x := (Real.le_log_iff_exp_le hxp).mpr hx
  have hl0 : 0 < Real.log x := by linarith
  have h5 : (100000 : ℝ) ≤ x := by
    have := SchoenfeldTheorem11B23.exp23_ge
    have h : Real.exp 23 ≤ Real.exp 100 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hEc100 : ∀ bl : ℝ, 210 ≤ bl → Real.exp (-(bl / 2)) ≤ 1 / 2.68e43 := by
    intro bl hbl
    exact Schoenfeld1976Rows2.exp_neg_le (f := 0) 100 (by norm_num) (by linarith) (by norm_num)
      (by norm_num)
  rcases le_or_gt x (Real.exp 210) with h1 | h1
  · apply finish h5 (ε := 3.66e-5) (bh := 210) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h1)
    exact row4low hRH (bl := 100) (bh := 210) (δ := 1.46e-5) (En := 1 / 2.4)
      (Ec := 1 / 5.18e21) (by norm_num) (by norm_num) hx h1 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.891) 0 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (Schoenfeld1976Rows2.exp_neg_le (f := 0) 50 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (by norm_num)
  rcases le_or_gt x (Real.exp 265) with h2 | h2
  · apply finish h5 (ε := 2.91e-5) (bh := 265) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h2)
    exact row4low hRH (bl := 210) (bh := 265) (δ := 1.16e-5) (En := 1 / 6.41)
      (Ec := 1 / 2.68e43) (by norm_num) (by norm_num) h1.le h2 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.871) 1 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (hEc100 210 le_rfl) (by norm_num)
  rcases le_or_gt x (Real.exp 292) with h3 | h3
  · apply finish h5 (ε := 2.64e-5) (bh := 292) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h3)
    exact row4low hRH (bl := 265) (bh := 292) (δ := 1.05e-5) (En := 1 / 10.6)
      (Ec := 1 / 2.68e43) (by norm_num) (by norm_num) h2.le h3 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.362) 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (hEc100 265 (by norm_num)) (by norm_num)
  rcases le_or_gt x (Real.exp 306) with h4 | h4
  · apply finish h5 (ε := 2.52e-5) (bh := 306) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr h4)
    exact row4low hRH (bl := 292) (bh := 306) (δ := 1.01e-5) (En := 1 / 13.4)
      (Ec := 1 / 2.68e43) (by norm_num) (by norm_num) h3.le h4 (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.602) 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (hEc100 292 (by norm_num)) (by norm_num)
  · apply finish h5 (ε := 2.46e-5) (bh := 313) (by norm_num) (by norm_num) hl0
      ((Real.log_le_iff_le_exp hxp).mpr hx')
    exact row4low hRH (bl := 306) (bh := 313) (δ := 9.82e-6) (En := 1 / 15.1)
      (Ec := 1 / 2.68e43) (by norm_num) (by norm_num) h4.le hx' (by norm_num) (by norm_num)
      (Schoenfeld1976Rows2.exp_neg_le (f := 0.727) 2 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num))
      (hEc100 306 (by norm_num)) (by norm_num)

end TernaryGoldbach.RSBounds.Schoenfeld1976Rows4
