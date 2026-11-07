import TernaryGoldbach.Explicit.PsiWeil
import TernaryGoldbach.Explicit.PsiPlateau

/-!
# `|ψ(x) − x| ≤ c √x` on a range `[X, X']`

One smoothing `δ`, cutoff `K` and `y₀` for the whole range; each error term of `psi_upper_WH` /
`psi_lower_WH` is maximised separately over the range (`scripts/weil_psi_model.py`, `sep_c`), so the
conditions are a few rational inequalities about the atoms `log(1/δ)`, `e^{δ²/2+Kδ}`, `e^{Kδ/2}`,
`e^{δ²/8}`, `2e^{−K²/2}` and square roots.
-/

open Complex Set Filter MeasureTheory Finset
open scoped Real Interval Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Explicit

theorem LWH_nonneg (H : ℝ) : 0 ≤ LWH H := by
  unfold LWH
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun m _ => mul_nonneg
    (div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le)
    (one_div_nonneg.2 (le_trans (by norm_num) (le_max_left _ _))))

/-- `LWH H ≤ 1142` for `H ≤ 3·10¹⁰`: a sub-sum of `window_sum_le`. -/
theorem LWH_le {H : ℝ} (hH : H ≤ 3e10) : LWH H ≤ 1142 := by
  have hsub : Finset.range (JlH 6 H) ⊆ Finset.range (JlH 6 3e10) := by
    refine Finset.range_mono ?_
    unfold JlH
    exact Nat.add_le_add_right (Nat.floor_mono (div_le_div_of_nonneg_right hH (by norm_num))) 1
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun m : ℕ =>
      Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) / Real.log (10 / 3.36) * (1 / max (1 / 2 : ℝ) (6 * (m : ℝ))))
    fun m _ _ => mul_nonneg
      (div_nonneg (polyDatum_zeta2.log_pos _).le (log_ratio_pos (by norm_num) (by norm_num)).le)
      (one_div_nonneg.2 (le_trans (by norm_num) (le_max_left _ _)))
  unfold LWH
  linarith [window_sum_le]

theorem JW_le {δ LU : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 208) (hLU : Real.log (1 / δ) ≤ LU) :
    JW δ ≤ 0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ := by
  unfold JW
  have h5 : 2 ≤ Real.log (1 / δ) := by
    have h208 : (208 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have : Real.exp 2 ≤ 208 := by
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [Real.exp_pos 1]
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith
  nlinarith

theorem JW_pos {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 208) : 0 < JW δ := by
  unfold JW; nlinarith [sq_nonneg (Real.log (1 / δ) - 1.3)]

/-- The Vg constant: `(2/log 2 + 4.8)·82.6·√(2π)/(2π) ≤ 253.3`. -/
theorem Vc_le : (2 / Real.log 2 + 4.8) * 82.6 * √(2 * π) / (2 * π) ≤ 253.3 := by
  have hl := Real.log_two_gt_d9
  have hpi := Real.pi_gt_d6
  have hs : (2.5066 : ℝ) ≤ √(2 * π) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsp : 0 < √(2 * π) := by positivity
  have e : √(2 * π) / (2 * π) = 1 / √(2 * π) := by
    rw [div_eq_div_iff (by positivity) hsp.ne', one_mul, Real.mul_self_sqrt (by positivity)]
  have h2 : 2 / Real.log 2 ≤ 2 / 0.6931471803 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  rw [mul_div_assoc, e]
  have h3 : 1 / √(2 * π) ≤ 1 / 2.5066 := one_div_le_one_div_of_le (by norm_num) hs
  have h4 : 0 ≤ 2 / Real.log 2 + 4.8 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  calc (2 / Real.log 2 + 4.8) * 82.6 * (1 / √(2 * π)) ≤ (2 / 0.6931471803 + 4.8) * 82.6 * (1 / 2.5066) := by
        gcongr
    _ ≤ 253.3 := by norm_num

theorem exp_half_log {z : ℝ} (hz : 0 < z) : Real.exp (Real.log z / 2) = √z := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hz]; ring_nf

/-- The `Vg` term over the range: `x^{−1/2} Vg(a, log(y₀/x), δ)/(2π) ≤ √x · 253.3 E₈/δ (E/X + s_{YX})`,
where `e^{−a/2} ≤ E`. -/
theorem Vg_range_le {δ a y0 X x E8 E sYX : ℝ} (hδ : 0 < δ) (hy0 : 0 < y0) (hX : 0 < X) (hx : X ≤ x)
    (hE8 : Real.exp (δ ^ 2 / 8) ≤ E8) (ha : Real.exp (-(a / 2)) ≤ E) (hsYX : 1 / √(y0 * X) ≤ sYX) :
    x ^ (-(1 / 2) : ℝ) * Vg a (Real.log (y0 / x)) δ / (2 * π) ≤ √x * (253.3 * E8 / δ * (E / X + sYX)) := by
  have hx0 : 0 < x := lt_of_lt_of_le hX hx
  have hsx : x ^ (-(1 / 2) : ℝ) = 1 / √x := by rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, one_div]
  have hb : Real.exp (-(Real.log (y0 / x) / 2)) = √x / √y0 := by
    rw [show -(Real.log (y0 / x) / 2) = Real.log (x / y0) / 2 by
      rw [show x / y0 = (y0 / x)⁻¹ by field_simp, Real.log_inv]; ring, exp_half_log (by positivity),
      Real.sqrt_div hx0.le]
  have hsq : 0 < √x := Real.sqrt_pos.2 hx0
  have hsy : 0 < √y0 := Real.sqrt_pos.2 hy0
  have hV := Vc_le
  have hc0 : 0 ≤ (2 / Real.log 2 + 4.8) * 82.6 * √(2 * π) / (2 * π) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  unfold Vg
  rw [hsx, hb]
  have e : 1 / √x * ((2 / Real.log 2 + 4.8) * 82.6 * Real.exp (δ ^ 2 / 8) *
      (Real.exp (-(a / 2)) + √x / √y0) * (√(2 * π) / δ)) / (2 * π) =
      ((2 / Real.log 2 + 4.8) * 82.6 * √(2 * π) / (2 * π)) * (Real.exp (δ ^ 2 / 8) / δ) *
        (Real.exp (-(a / 2)) / √x + 1 / √y0) := by
    field_simp
  rw [e]
  have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans ha
  have h1 : Real.exp (-(a / 2)) / √x ≤ √x * (E / X) := by
    rw [div_le_iff₀ hsq]
    have e1 : √x * (E / X) * √x = x * (E / X) := by
      rw [mul_comm (√x) (E / X), mul_assoc, Real.mul_self_sqrt hx0.le, mul_comm]
    have hEX : E ≤ x * (E / X) := by
      rw [mul_div_assoc', le_div_iff₀ hX]; nlinarith
    rw [e1]; linarith
  have h2 : 1 / √y0 ≤ √x * sYX := by
    have hxy : √(y0 * X) ≤ √x * √y0 := by
      rw [← Real.sqrt_mul hx0.le]; exact Real.sqrt_le_sqrt (by nlinarith)
    have hpos : 0 < √(y0 * X) := Real.sqrt_pos.2 (by positivity)
    have h3 : 1 / (√x * √y0) ≤ 1 / √(y0 * X) := one_div_le_one_div_of_le hpos hxy
    calc 1 / √y0 = √x * (1 / (√x * √y0)) := by field_simp
      _ ≤ √x * (1 / √(y0 * X)) := mul_le_mul_of_nonneg_left h3 hsq.le
      _ ≤ √x * sYX := mul_le_mul_of_nonneg_left hsYX hsq.le
  have hE8' : 0 ≤ Real.exp (δ ^ 2 / 8) / δ := by positivity
  have hE80 : 0 ≤ E8 := (Real.exp_pos _).le.trans hE8
  have hsYX0 : 0 ≤ sYX := le_trans (by positivity) hsYX
  have hk : ((2 / Real.log 2 + 4.8) * 82.6 * √(2 * π) / (2 * π)) * (Real.exp (δ ^ 2 / 8) / δ) ≤
      253.3 * (E8 / δ) := mul_le_mul hV (div_le_div_of_nonneg_right hE8 hδ.le) hE8' (by norm_num)
  calc ((2 / Real.log 2 + 4.8) * 82.6 * √(2 * π) / (2 * π)) * (Real.exp (δ ^ 2 / 8) / δ) *
        (Real.exp (-(a / 2)) / √x + 1 / √y0)
      ≤ 253.3 * (E8 / δ) * (√x * (E / X) + √x * sYX) :=
        mul_le_mul hk (add_le_add h1 h2) (by positivity) (by positivity)
    _ = √x * (253.3 * E8 / δ * (E / X + sYX)) := by ring

/-! ### The same at a general RH height `H` -/

/-- The line term over the range at RH height `H`: `LineWH ≤ E₈ (E_h + s_Y)(JW⁺ + μ)` for `x ≥ X`,
where `e^{−δ²Y₁²/2} LWH(H) ≤ μ`. -/
theorem LineWH_range_le {δ a y0 X x LU E8 Eh sY Y₁ H μ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 208)
    (hy0 : 0 < y0) (hX : 0 < X) (hx : X ≤ x) (ha : Real.exp (a / 2) ≤ Eh) (hLU : Real.log (1 / δ) ≤ LU)
    (hE8 : Real.exp (δ ^ 2 / 8) ≤ E8) (hsY : √(y0 / X) ≤ sY)
    (hμ : Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H ≤ μ) :
    LineWH a (Real.log (y0 / x)) δ Y₁ H ≤
      E8 * (Eh + sY) * (0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ + μ) := by
  have hx0 : 0 < x := lt_of_lt_of_le hX hx
  unfold LineWH
  rw [exp_half_log (by positivity)]
  have h1 : √(y0 / x) ≤ sY := (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hy0.le hX hx)).trans hsY
  have hJ := JW_le hδ hδ1 hLU
  have hJ0 := JW_pos hδ hδ1
  have hg0 : 0 ≤ Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H := mul_nonneg (Real.exp_pos _).le (LWH_nonneg H)
  have hEh0 : 0 ≤ Eh := (Real.exp_pos _).le.trans ha
  have hsY0 : 0 ≤ sY := (Real.sqrt_nonneg _).trans hsY
  have hA : Real.exp (δ ^ 2 / 8) * (Real.exp (a / 2) + √(y0 / x)) ≤ E8 * (Eh + sY) :=
    mul_le_mul hE8 (add_le_add ha h1) (by positivity) ((Real.exp_pos _).le.trans hE8)
  have hB : JW δ + Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H ≤
      0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ + μ := by linarith
  exact mul_le_mul hA hB (by linarith) (mul_nonneg ((Real.exp_pos _).le.trans hE8) (by linarith))

set_option maxHeartbeats 2000000 in
/-- **`ψ(x) ≤ x + c√x` on `[X, X']`** under RH up to `H ∈ [10⁸, 3·10¹⁰]` (windows to `Y₁`), with
`TailBH ≤ τ` and `e^{−δ²Y₁²/2} LWH(H) ≤ μ`. -/
theorem psi_range_upH {δ K y0 X X' c LU E1 E8 Eh q sY sYX rX rX' H Y₁ τ μ : ℝ} (hRH : RHBelow H)
    (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10) (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + 13 ≤ H / 2) (hδ0 : 3 / Y₁ ≤ δ)
    (hδ1 : δ ≤ 1 / 208) (hτ : ∀ a : ℝ, |a| ≤ 1 → TailBH a δ H ≤ τ) (hτ0 : 0 ≤ τ)
    (hμ : Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H ≤ μ)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1) (hy0 : 0 < y0) (hX1 : 1 ≤ X) (hYX : y0 * Real.exp (K * δ) ≤ X)
    (hLU : Real.log (1 / δ) ≤ LU) (hE1 : Real.exp (δ ^ 2 / 2 + K * δ) ≤ E1) (hE8 : Real.exp (δ ^ 2 / 8) ≤ E8)
    (hEh : Real.exp (K * δ / 2) ≤ Eh) (hq : 2 * Real.exp (-(K ^ 2 / 2)) ≤ q) (hq1 : q < 1)
    (hsY : √(y0 / X) ≤ sY) (hsYX : 1 / √(y0 * X) ≤ sYX) (hrX0 : 0 < rX) (hrX : rX ≤ √X) (hrX' : √X' ≤ rX')
    (hc : (E1 / (1 - q) - 1) * rX' + E8 * (Eh + sY) * (0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ + μ) /
      (1 - q) + τ * rX' / (1 - q) + 4 * y0 * E1 / rX + 253.3 * E8 / δ / (1 - q) * (1 / X + sYX) ≤ c)
    {x : ℝ} (hx1 : X ≤ x) (hx2 : x ≤ X') : psiR x ≤ x + c * √x := by
  have hδ : 0 < δ := lt_of_lt_of_le (by have : 0 < Y₁ := by linarith
                                        positivity) hδ0
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := by linarith
  have hq0 : 0 < 1 - q := by linarith
  have hK1 : 2 * Real.exp (-(K ^ 2 / 2)) < 1 := lt_of_le_of_lt hq hq1
  have hU := psi_upper_WH (δ := δ) (K := K) (y0 := y0) (x := x) hRH hH1 hH2 hY₁0 hY₁ hδ0 hδ1 hK hK1 hy0
    (by linarith) (hYX.trans hx1)
  set s := √x with hs
  have hs2 : s * s = x := Real.mul_self_sqrt hx0.le
  have hs1 : rX ≤ s := hrX.trans (Real.sqrt_le_sqrt hx1)
  have hs2' : s ≤ rX' := (Real.sqrt_le_sqrt hx2).trans hrX'
  have hs0 : 0 < s := lt_of_lt_of_le hrX0 hs1
  -- the error
  set Lb := E8 * (Eh + sY) * (0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ + μ) with hLb
  set V := 253.3 * E8 / δ * (1 / X + sYX) with hV
  have hL := LineWH_range_le hδ hδ1 hy0 hX0 hx1 hEh hLU hE8 hsY hμ (a := K * δ)
  have hT := hτ (K * δ) (by rw [abs_of_nonneg (by positivity)]; exact hKδ)
  have hVg := Vg_range_le hδ hy0 hX0 hx1 hE8 (E := 1) (a := K * δ)
    (Real.exp_le_one_iff.2 (by nlinarith)) hsYX
  rw [← hLb] at hL
  rw [← hV] at hVg
  have hErr : ErrWH (K * δ) (Real.log (y0 / x)) δ Y₁ H x ≤ s * Lb + x * τ + s * V := by
    unfold ErrWH
    rw [← hs]
    have h1 := mul_le_mul_of_nonneg_left hL hs0.le
    have h2 := mul_le_mul_of_nonneg_left hT hx0.le
    linarith
  have hE1' : Real.exp (K * δ) ≤ E1 :=
    (Real.exp_le_exp.2 (by have := sq_nonneg δ; linarith)).trans hE1
  have hE11 : 1 ≤ E1 := (Real.one_le_exp (by positivity)).trans hE1
  have hJ0 := JW_pos hδ hδ1
  have hJ := JW_le hδ hδ1 hLU
  have hEh1 : 1 ≤ Eh := (Real.one_le_exp (by positivity)).trans hEh
  have hE81 : 1 ≤ E8 := (Real.one_le_exp (by positivity)).trans hE8
  have hsY0 : 0 ≤ sY := (Real.sqrt_nonneg _).trans hsY
  have hsYX0 : 0 ≤ sYX := le_trans (by positivity) hsYX
  have hμ0 : 0 ≤ μ := le_trans (mul_nonneg (Real.exp_pos _).le (LWH_nonneg H)) hμ
  have hLb0 : 0 ≤ Lb := by rw [hLb]; exact mul_nonneg (by positivity) (by linarith)
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  have hNb0 : 0 ≤ E1 * x + s * Lb + x * τ + s * V :=
    add_nonneg (add_nonneg (add_nonneg (mul_nonneg (by linarith) hx0.le) (mul_nonneg hs0.le hLb0))
      (mul_nonneg hx0.le hτ0)) (mul_nonneg hs0.le hV0)
  have hD : 1 - q ≤ 1 - 2 * Real.exp (-(K ^ 2 / 2)) := by linarith
  have hU2 : psiR x ≤ 4 * (y0 * E1) + (E1 * x + s * Lb + x * τ + s * V) / (1 - q) := by
    have h1 : Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrWH (K * δ) (Real.log (y0 / x)) δ Y₁ H x ≤
        E1 * x + s * Lb + x * τ + s * V := by
      have := mul_le_mul_of_nonneg_right hE1 hx0.le
      linarith
    have h2 : (Real.exp (δ ^ 2 / 2 + K * δ) * x + ErrWH (K * δ) (Real.log (y0 / x)) δ Y₁ H x) /
        (1 - 2 * Real.exp (-(K ^ 2 / 2))) ≤ (E1 * x + s * Lb + x * τ + s * V) / (1 - q) :=
      (div_le_div_of_nonneg_right h1 (by linarith)).trans (div_le_div_of_nonneg_left hNb0 hq0 hD)
    have h3 : 4 * (y0 * Real.exp (K * δ)) ≤ 4 * (y0 * E1) := by gcongr
    linarith
  -- the algebra
  have hcLV : (E1 / (1 - q) - 1) * rX' + Lb / (1 - q) + τ * rX' / (1 - q) + 4 * y0 * E1 / rX +
      V / (1 - q) ≤ c := by
    have e2 : 253.3 * E8 / δ / (1 - q) * (1 / X + sYX) = V / (1 - q) := by rw [hV]; ring
    rw [← e2, hLb]; exact hc
  have hc' := mul_le_mul_of_nonneg_left hcLV hs0.le
  simp only [mul_add] at hc'
  have hq00 : 0 ≤ q := le_trans (by positivity) hq
  have hA : 0 ≤ E1 / (1 - q) - 1 := by
    rw [sub_nonneg, le_div_iff₀ hq0]; linarith
  have hxs : x ≤ s * rX' := by rw [← hs2]; exact mul_le_mul_of_nonneg_left hs2' hs0.le
  have p1 : (E1 / (1 - q) - 1) * x ≤ s * ((E1 / (1 - q) - 1) * rX') := by
    have := mul_le_mul_of_nonneg_left hxs hA; linarith
  have p2 : τ * x / (1 - q) ≤ s * (τ * rX' / (1 - q)) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hq0]
    have := mul_le_mul_of_nonneg_left hxs hτ0
    linarith
  have p3 : 4 * (y0 * E1) ≤ s * (4 * y0 * E1 / rX) := by
    rw [mul_div_assoc', le_div_iff₀ hrX0]
    have h0 : 0 ≤ 4 * y0 * E1 := by positivity
    have := mul_le_mul_of_nonneg_left hs1 h0
    linarith
  have e : (E1 * x + s * Lb + x * τ + s * V) / (1 - q) = (E1 / (1 - q) - 1) * x + x + s * (Lb / (1 - q)) +
      τ * x / (1 - q) + s * (V / (1 - q)) := by
    field_simp; ring
  rw [e] at hU2
  linarith

/-- **`x − c√x ≤ ψ(x)` on `[X, X']`** under RH up to `H ∈ [10⁸, 3·10¹⁰]` (windows to `Y₁`), with
`TailBH ≤ τ` and `e^{−δ²Y₁²/2} LWH(H) ≤ μ`. -/
theorem psi_range_loH {δ K y0 X X' c LU E8 Eh q sY sYX rX rX' H Y₁ τ μ : ℝ} (hRH : RHBelow H)
    (hH1 : 1e8 ≤ H) (hH2 : H ≤ 3e10) (hY₁0 : 1 / 2 ≤ Y₁) (hY₁ : Y₁ + 13 ≤ H / 2) (hδ0 : 3 / Y₁ ≤ δ)
    (hδ1 : δ ≤ 1 / 208) (hτ : ∀ a : ℝ, |a| ≤ 1 → TailBH a δ H ≤ τ) (hτ0 : 0 ≤ τ)
    (hμ : Real.exp (-(δ ^ 2 * Y₁ ^ 2 / 2)) * LWH H ≤ μ)
    (hKδ0 : δ ≤ K) (hKδ : K * δ ≤ 1) (hy0 : 0 < y0) (hX1 : 1 ≤ X) (hYX : y0 * Real.exp (K * δ) ≤ X)
    (hLU : Real.log (1 / δ) ≤ LU) (hE8 : Real.exp (δ ^ 2 / 8) ≤ E8) (hEh : Real.exp (K * δ / 2) ≤ Eh)
    (hq : 2 * Real.exp (-(K ^ 2 / 2)) ≤ q) (hsY : √(y0 / X) ≤ sY) (hsYX : 1 / √(y0 * X) ≤ sYX)
    (hrX0 : 0 < rX) (hrX : rX ≤ √X) (hrX' : √X' ≤ rX')
    (hc : (K * δ + 2 * q) * rX' + 2 * y0 / rX +
      E8 * (Eh + sY) * (0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ + μ) + τ * rX' +
      253.3 * E8 / δ * (Eh / X + sYX) ≤ c)
    {x : ℝ} (hx1 : X ≤ x) (hx2 : x ≤ X') : x - c * √x ≤ psiR x := by
  have hδ : 0 < δ := lt_of_lt_of_le (by have : 0 < Y₁ := by linarith
                                        positivity) hδ0
  have hK : 0 ≤ K := hδ.le.trans hKδ0
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := by linarith
  have hb : Real.log (y0 / x) ≤ -(K * δ) := by
    rw [← Real.log_exp (-(K * δ))]
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hx0, Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _)]
    linarith
  have hL := psi_lower_WH hRH hH1 hH2 hY₁0 hY₁ hδ0 hδ1 hKδ0 hy0 (by linarith) hb
  set s := √x with hs
  have hs2 : s * s = x := Real.mul_self_sqrt hx0.le
  have hs1 : rX ≤ s := hrX.trans (Real.sqrt_le_sqrt hx1)
  have hs2' : s ≤ rX' := (Real.sqrt_le_sqrt hx2).trans hrX'
  have hs0 : 0 < s := lt_of_lt_of_le hrX0 hs1
  set Lb := E8 * (Eh + sY) * (0.16385 * LU ^ 2 - 0.4271 * LU + 7.2032 + 57.73 * δ + μ) with hLb
  set V := 253.3 * E8 / δ * (Eh / X + sYX) with hV
  have hEh1 : 1 ≤ Eh := (Real.one_le_exp (by positivity)).trans hEh
  have hLW := LineWH_range_le hδ hδ1 hy0 hX0 hx1 (a := -(K * δ)) (Eh := Eh)
    ((Real.exp_le_one_iff.2 (by nlinarith)).trans hEh1) hLU hE8 hsY hμ
  have hT := hτ (-(K * δ)) (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hKδ)
  have hVg := Vg_range_le hδ hy0 hX0 hx1 hE8 (E := Eh) (a := -(K * δ))
    (by rw [show -(-(K * δ) / 2) = K * δ / 2 by ring]; exact hEh) hsYX
  rw [← hLb] at hLW
  rw [← hV] at hVg
  have hErr : ErrWH (-(K * δ)) (Real.log (y0 / x)) δ Y₁ H x ≤ s * Lb + x * τ + s * V := by
    unfold ErrWH
    rw [← hs]
    have h1 := mul_le_mul_of_nonneg_left hLW hs0.le
    have h2 := mul_le_mul_of_nonneg_left hT hx0.le
    linarith
  have h1e : 1 - Real.exp (-(K * δ)) ≤ K * δ := by have := Real.add_one_le_exp (-(K * δ)); linarith
  have hq' : 4 * Real.exp (-(K ^ 2 / 2)) ≤ 2 * q := by linarith
  have hxs : x ≤ s * rX' := by rw [← hs2]; exact mul_le_mul_of_nonneg_left hs2' hs0.le
  have hKq : 0 ≤ K * δ + 2 * q := by
    have : 0 ≤ q := le_trans (by positivity) hq
    positivity
  have p1 : (K * δ + 2 * q) * x ≤ s * ((K * δ + 2 * q) * rX') := by
    have := mul_le_mul_of_nonneg_left hxs hKq; linarith
  have p2 : τ * x ≤ s * (τ * rX') := by
    have := mul_le_mul_of_nonneg_left hxs hτ0; linarith
  have p3 : 2 * y0 ≤ s * (2 * y0 / rX) := by
    rw [mul_div_assoc', le_div_iff₀ hrX0]
    have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 2 * y0)
    linarith
  have hc' := mul_le_mul_of_nonneg_left hc hs0.le
  simp only [mul_add] at hc'
  have h4 : (1 - Real.exp (-(K * δ))) * x ≤ K * δ * x := mul_le_mul_of_nonneg_right h1e hx0.le
  have h5 : 4 * x * Real.exp (-(K ^ 2 / 2)) ≤ 2 * q * x := by
    have := mul_le_mul_of_nonneg_right hq' hx0.le; linarith
  have e : (K * δ + 2 * q) * x = K * δ * x + 2 * q * x := by ring
  linarith

/-- At `H = 10⁸`: `TailBH a δ 10⁸ ≤ 10.7 e^{−δ²·10¹⁶/2}` for `|a| ≤ 1`, `7·10⁻⁸ ≤ δ ≤ 1/208`. -/
theorem TailBH_1e8_le {a δ : ℝ} (ha : |a| ≤ 1) (hδ0 : 7e-8 ≤ δ) (hδ1 : δ ≤ 1 / 208) :
    TailBH a δ 1e8 ≤ 10.7 * Real.exp (-(δ ^ 2 * (1e8 : ℝ) ^ 2 / 2)) := by
  unfold TailBH EBg rhoG
  set t : ℝ := 4.4 * δ ^ 2 * 1e8 with ht
  have ht1 : (2.156e-6 : ℝ) ≤ t := by rw [ht]; nlinarith
  have h1r : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    have h := Real.add_one_le_exp t
    rw [Real.exp_neg]
    have hp : 0 < Real.exp t := Real.exp_pos t
    rw [div_le_iff₀ (by linarith), sub_mul, one_mul, inv_mul_eq_div]
    have : (1 + t) / Real.exp t ≤ 1 := by rw [div_le_one hp]; linarith
    linarith
  have htv : (2.155e-6 : ℝ) ≤ t / (1 + t) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  have hr : (2.155e-6 : ℝ) ≤ 1 - Real.exp (-t) := htv.trans h1r
  have hr0 : 0 < 1 - Real.exp (-t) := lt_of_lt_of_le (by norm_num) hr
  have he : Real.exp (δ ^ 2 / 2 + |a|) ≤ 2.7184 := by
    have hδ0' : 0 ≤ δ := by linarith
    have h1 : δ ^ 2 / 2 + |a| ≤ 1 + 1.2e-5 := by
      have : δ ^ 2 ≤ (1 / 208) ^ 2 := pow_le_pow_left₀ hδ0' hδ1 2
      norm_num at this ⊢; linarith
    refine (Real.exp_le_exp.2 h1).trans ?_
    rw [Real.exp_add]
    have h2 := Real.exp_one_lt_d9
    have h3 := exp_small_le (t := 1.2e-5) (by norm_num) (by norm_num)
    nlinarith [Real.exp_pos 1, Real.exp_pos 1.2e-5]
  have hl := log_10_3_ge
  have hZ : Z3g BPz2 1e8 ≤ 210.6 := by
    refine le_trans ?_ Z3g_H_le
    unfold Z3g
    refine div_le_div_of_nonneg_right (polyDatum_zeta2.log_mono ?_) (log_ratio_pos (by norm_num) (by norm_num)).le
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1e8), abs_of_pos (by norm_num : (0 : ℝ) < 3e10)]; norm_num
  have hZ0 : 0 ≤ Z3g BPz2 1e8 :=
    div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) hl).le
  have hc : c3g 10 1e8 ≤ 3.66e-7 := by
    unfold c3g
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl)]
    nlinarith
  have hc0 : 0 ≤ c3g 10 1e8 := by
    unfold c3g; exact div_nonneg (by norm_num) (lt_of_lt_of_le (by norm_num) hl).le
  have hA : 2 * Z3g BPz2 1e8 / (1 - Real.exp (-t)) ≤ 2 * 210.6 / 2.155e-6 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hB : 2 * c3g 10 1e8 / (1 - Real.exp (-t)) ^ 2 ≤ 2 * 3.66e-7 / (2.155e-6) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2.155e-6 : ℝ) ^ 2 ≤ (1 - Real.exp (-t)) ^ 2 := pow_le_pow_left₀ (by norm_num) hr 2
    nlinarith
  set g := Real.exp (-(δ ^ 2 * (1e8 : ℝ) ^ 2 / 2)) with hg
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hE : 2 * Real.exp (δ ^ 2 / 2 + |a|) * g / 1e8 ≤ 2 * 2.7184 * g / 1e8 := by gcongr
  have hS0 : 0 ≤ 2 * Z3g BPz2 1e8 / (1 - Real.exp (-t)) + 2 * c3g 10 1e8 / (1 - Real.exp (-t)) ^ 2 :=
    add_nonneg (div_nonneg (by linarith) hr0.le) (div_nonneg (by linarith) (by positivity))
  calc 2 * Real.exp (δ ^ 2 / 2 + |a|) * g / 1e8 *
        (2 * Z3g BPz2 1e8 / (1 - Real.exp (-t)) + 2 * c3g 10 1e8 / (1 - Real.exp (-t)) ^ 2)
      ≤ (2 * 2.7184 * g / 1e8) * (2 * 210.6 / 2.155e-6 + 2 * 3.66e-7 / (2.155e-6) ^ 2) :=
        mul_le_mul hE (add_le_add hA hB) hS0 (by positivity)
    _ = g * (2 * 2.7184 / 1e8 * (2 * 210.6 / 2.155e-6 + 2 * 3.66e-7 / (2.155e-6) ^ 2)) := by ring
    _ ≤ g * 10.7 := mul_le_mul_of_nonneg_left (by norm_num) hg0
    _ = 10.7 * g := by ring

end TernaryGoldbach.Explicit
