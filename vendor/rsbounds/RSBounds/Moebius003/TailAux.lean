/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.Misc
import RSBounds.Moebius003.Weights
import RSBounds.Moebius003.CellsDefs

/-!
# Auxiliary results for §5 of the note

* monotonicity of `t/log t`, `t/log² t` and `(log t)/t`, by elementary inequalities;
* the bound (4) of the note for `|M(u)|` beyond `D_mid`;
* the sums `∑_{2 ≤ k ≤ Y} 1/(k log(D/k)) ≤ log(log D/log(D/Y))` and
  `∑_{2 ≤ k ≤ Y} 1/(k log²(D/k)) ≤ 1/log(D/Y) − 1/log D`, by telescoping.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real

/-! ### Monotonicity -/

theorem one_le_log_of {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
  exact Real.log_le_log (Real.exp_pos 1) hx

/-- `a/log a ≤ b/log b` for `e ≤ a ≤ b`. -/
theorem div_log_mono {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hla := one_le_log_of ha
  have hlb := one_le_log_of (ha.trans hab)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 : Real.log b ≤ Real.log a + (b / a - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    rw [Real.log_div hb0.ne' ha0.ne'] at this; linarith
  have h2 : a * Real.log b ≤ a * Real.log a + (b - a) := by
    have := mul_le_mul_of_nonneg_left h1 ha0.le
    rw [mul_add, mul_sub, mul_div_cancel₀ _ ha0.ne', mul_one] at this; linarith
  nlinarith

/-- `a/log² a ≤ b/log² b` for `e² ≤ a ≤ b`. -/
theorem div_log_sq_mono {a b : ℝ} (ha : Real.exp 2 ≤ a) (hab : a ≤ b) :
    a / Real.log a ^ 2 ≤ b / Real.log b ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 2) ha
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hla : 2 ≤ Real.log a := by
    rw [show (2 : ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 2) ha
  set s := Real.log (b / a) with hs
  have hs0 : 0 ≤ s := Real.log_nonneg (by rw [le_div_iff₀ ha0]; linarith)
  have hlb : Real.log b = Real.log a + s := by
    rw [hs, Real.log_div hb0.ne' ha0.ne']; ring
  have hr : b / a = Real.exp s := by rw [hs, Real.exp_log (div_pos hb0 ha0)]
  have hexp := Real.quadratic_le_exp_of_nonneg hs0
  -- `(1 + s/log a)² ≤ (1 + s/2)² ≤ e^s = b/a`
  have hla0 : 0 < Real.log a := by linarith
  have key : (Real.log a + s) ^ 2 ≤ Real.log a ^ 2 * (b / a) := by
    rw [hr]
    have h1 : (Real.log a + s) ^ 2 = Real.log a ^ 2 * (1 + s / Real.log a) ^ 2 := by
      field_simp
    have h2 : (1 + s / Real.log a) ^ 2 ≤ (1 + s / 2) ^ 2 := by
      have : s / Real.log a ≤ s / 2 := div_le_div_of_nonneg_left hs0 (by norm_num) hla
      have : 0 ≤ s / Real.log a := div_nonneg hs0 hla0.le
      nlinarith
    have h3 : (1 + s / 2) ^ 2 ≤ Real.exp s := by nlinarith
    rw [h1]
    exact mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by rw [hlb]; positivity), hlb]
  have := mul_le_mul_of_nonneg_left key ha0.le
  calc a * (Real.log a + s) ^ 2 ≤ a * (Real.log a ^ 2 * (b / a)) := this
    _ = b * Real.log a ^ 2 := by field_simp

/-- `log y/y ≤ log x/x` for `e ≤ x ≤ y`. -/
theorem log_div_anti {x y : ℝ} (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    Real.log y / y ≤ Real.log x / x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hlx := one_le_log_of hx
  rw [div_le_div_iff₀ hy0 hx0]
  have h1 : Real.log y ≤ Real.log x + (y / x - 1) := by
    have := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at this; linarith
  have h2 : x * Real.log y ≤ x * Real.log x + (y - x) := by
    have := mul_le_mul_of_nonneg_left h1 hx0.le
    rw [mul_add, mul_sub, mul_div_cancel₀ _ hx0.ne', mul_one] at this; linarith
  nlinarith

/-! ### The bound for `|M|` used beyond `D_mid` -/

/-- A form of the note's (4): for `X₀ ≤ u ≤ D`, `|M(u)| ≤ C₀ + |N(u)|/log u + ν̄ λ₀ u/log² u`
(with `C₀ ≤ 1743`), given `|N| ≤ ν̄` on `[X₀, D)`. The note's (4) then inserts `|N(u)| ≤ ν_∞ u`. -/
theorem M_tail (h : Inputs) {D : ℕ} (hN : ∀ t : ℕ, X0 ≤ t → t < D → |N t| ≤ 0.017 * t)
    {u : ℕ} (hu1 : X0 ≤ u) (hu2 : u ≤ D) :
    |M u| ≤ C0B + |N u| / Real.log u + 0.017 * lam0 * u / Real.log u ^ 2 := by
  have h1 := abs_M_le_of_N hu1
  have hC := abs_C0_le_C0B h
  have h2 : Iint X0 u ≤ 0.017 * ∑ t ∈ Ico X0 u, 1 / Real.log t ^ 2 := by
    unfold Iint
    rw [mul_sum]
    refine sum_le_sum fun t ht => ?_
    obtain ⟨ht1, ht2⟩ := mem_Ico.1 ht
    have ht2' : 2 ≤ t := by unfold X0 at ht1; omega
    have hd := inv_log_sub_nonneg ht2'
    have hb := hN t ht1 (lt_of_lt_of_le ht2 hu2)
    have hm := mul_inv_log_sub_le ht2'
    calc |N t| * (1 / Real.log t - 1 / Real.log (t + 1)) ≤ 0.017 * t * (1 / Real.log t - 1 / Real.log (t + 1)) :=
          mul_le_mul_of_nonneg_right hb hd
      _ = 0.017 * (t * (1 / Real.log t - 1 / Real.log (t + 1))) := by ring
      _ ≤ 0.017 * (1 / Real.log t ^ 2) := by gcongr
  have h3 := sum_inv_log_sq_le hu1
  have : 0.017 * ∑ t ∈ Ico X0 u, 1 / Real.log t ^ 2 ≤ 0.017 * (lam0 * u / Real.log u ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (by norm_num)
  have e : 0.017 * (lam0 * u / Real.log u ^ 2) = 0.017 * lam0 * u / Real.log u ^ 2 := by ring
  linarith

/-! ### Two sums over `k` -/

theorem log_one_add_ge {v : ℝ} (hv : 0 ≤ v) : 2 * v / (2 + v) ≤ Real.log (1 + v) := by
  set t : ℝ := v / (2 + v)
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hs := LogCert.hasSum_atanh ht0 ht1
  have := sum_le_hasSum (range 1) (fun k _ => by positivity) hs
  simp at this
  have e : (1 + t) / (1 - t) = 1 + v := by simp only [t]; field_simp; ring
  rw [e] at this
  calc 2 * v / (2 + v) = 2 * t := by simp only [t]; ring
    _ ≤ _ := by linarith

/-- `log(k/(k−1)) ≥ 2/(2k−1)` and `≤ 1/(k−1)`. -/
theorem log_k_bounds {k : ℕ} (hk : 2 ≤ k) :
    2 / (2 * (k : ℝ) - 1) ≤ Real.log k - Real.log ((k : ℝ) - 1) ∧
      Real.log k - Real.log ((k : ℝ) - 1) ≤ 1 / ((k : ℝ) - 1) := by
  have hk1 : 1 ≤ k - 1 := by omega
  have e1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have e2 : (((k - 1 : ℕ) : ℝ) + 1) = k := by rw [e1]; ring
  have hlog := log_succ_sub_log (n := k - 1) hk1
  rw [e2, e1] at hlog
  rw [hlog]
  constructor
  · have := two_div_le_log (k - 1) hk1
    rw [e1] at this
    calc 2 / (2 * (k : ℝ) - 1) = 2 / (2 * ((k : ℝ) - 1) + 1) := by ring_nf
      _ ≤ _ := this
  · have := log_one_add_inv_le (k - 1) hk1
    rw [e1] at this; exact this

/-- The step for `∑ 1/(k log(D/k))`. -/
theorem inv_klog_le {D : ℝ} {k : ℕ} (hk : 2 ≤ k) (hD : (k : ℝ) < D)
    (hB : 2 ≤ Real.log (D / k)) :
    1 / (k * Real.log (D / k)) ≤
      Real.log (Real.log (D / ((k : ℝ) - 1))) - Real.log (Real.log (D / k)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hDpos : 0 < D := by linarith
  set B := Real.log (D / k)
  set Δ := Real.log k - Real.log ((k : ℝ) - 1)
  obtain ⟨hΔ1, hΔ2⟩ := log_k_bounds hk
  have hA : Real.log (D / ((k : ℝ) - 1)) = B + Δ := by
    simp only [B, Δ]
    rw [Real.log_div hDpos.ne' (by linarith), Real.log_div hDpos.ne' (by linarith)]; ring
  have hB0 : 0 < B := by linarith
  have hΔ0 : 0 ≤ Δ := le_trans (div_nonneg (by norm_num) (by linarith)) hΔ1
  rw [hA, ← Real.log_div (by linarith) hB0.ne']
  have e : (B + Δ) / B = 1 + Δ / B := by field_simp
  rw [e]
  have h1 := log_one_add_ge (div_nonneg hΔ0 hB0.le)
  refine le_trans ?_ h1
  -- `1/(kB) ≤ 2(Δ/B)/(2 + Δ/B) = 2Δ/(2B + Δ)`
  have e2 : 2 * (Δ / B) / (2 + Δ / B) = 2 * Δ / (2 * B + Δ) := by field_simp
  rw [e2, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  -- `2B + Δ ≤ 2 k B Δ`
  have hkΔ : 1 / (2 * (k : ℝ) - 1) ≤ k * Δ - 1 := by
    have := mul_le_mul_of_nonneg_left hΔ1 (by positivity : (0 : ℝ) ≤ k)
    have hk2 : (2 : ℝ) * k - 1 ≠ 0 := by linarith
    have e3 : (k : ℝ) * (2 / (2 * k - 1)) - 1 = 1 / (2 * k - 1) := by
      rw [eq_div_iff hk2, sub_mul, mul_assoc, div_mul_cancel₀ _ hk2]; ring
    linarith
  have hΔ3 : Δ ≤ 2 * B / (2 * (k : ℝ) - 1) := by
    refine hΔ2.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have : Δ ≤ 2 * B * (k * Δ - 1) := by
    calc Δ ≤ 2 * B / (2 * (k : ℝ) - 1) := hΔ3
      _ = 2 * B * (1 / (2 * (k : ℝ) - 1)) := by ring
      _ ≤ 2 * B * (k * Δ - 1) := by gcongr
  nlinarith

/-- The step for `∑ 1/(k log²(D/k))`. -/
theorem inv_klog_sq_le {D : ℝ} {k : ℕ} (hk : 2 ≤ k) (hD : (k : ℝ) < D)
    (hB : 4 ≤ Real.log (D / k)) :
    1 / (k * Real.log (D / k) ^ 2) ≤ 1 / Real.log (D / k) - 1 / Real.log (D / ((k : ℝ) - 1)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hDpos : 0 < D := by linarith
  set B := Real.log (D / k)
  set Δ := Real.log k - Real.log ((k : ℝ) - 1)
  obtain ⟨hΔ1, hΔ2⟩ := log_k_bounds hk
  have hA : Real.log (D / ((k : ℝ) - 1)) = B + Δ := by
    simp only [B, Δ]
    rw [Real.log_div hDpos.ne' (by linarith), Real.log_div hDpos.ne' (by linarith)]; ring
  have hB0 : 0 < B := by linarith
  have hΔ0 : 0 ≤ Δ := le_trans (div_nonneg (by norm_num) (by linarith)) hΔ1
  rw [hA, div_sub_div _ _ hB0.ne' (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
  have hkΔ : 1 / (2 * (k : ℝ) - 1) ≤ k * Δ - 1 := by
    have := mul_le_mul_of_nonneg_left hΔ1 (by positivity : (0 : ℝ) ≤ k)
    have hk2 : (2 : ℝ) * k - 1 ≠ 0 := by linarith
    have e3 : (k : ℝ) * (2 / (2 * k - 1)) - 1 = 1 / (2 * k - 1) := by
      rw [eq_div_iff hk2, sub_mul, mul_assoc, div_mul_cancel₀ _ hk2]; ring
    linarith
  have hΔ3 : Δ ≤ B / (2 * (k : ℝ) - 1) := by
    refine hΔ2.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have : Δ ≤ B * (k * Δ - 1) := by
    calc Δ ≤ B / (2 * (k : ℝ) - 1) := hΔ3
      _ = B * (1 / (2 * (k : ℝ) - 1)) := by ring
      _ ≤ B * (k * Δ - 1) := by gcongr
  nlinarith

/-- `∑_{2 ≤ k ≤ Y} 1/(k log(D/k)) ≤ log log D − log log(D/Y)`. -/
theorem sum_inv_klog_le {D : ℝ} {Y : ℕ} (hY : 2 ≤ Y) (hYD : (Y : ℝ) < D)
    (hB : 4 ≤ Real.log (D / Y)) :
    ∑ k ∈ Icc 2 Y, 1 / (k * Real.log (D / k)) ≤
      Real.log (Real.log D) - Real.log (Real.log (D / Y)) := by
  induction Y, hY using Nat.le_induction with
  | base =>
    simp only [Icc_self, sum_singleton]
    have := inv_klog_le (D := D) (k := 2) le_rfl (by exact_mod_cast hYD) (by linarith)
    norm_num at this ⊢; exact this
  | succ Y hY ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hYD' : (Y : ℝ) < D := by push_cast at hYD; linarith
    have hDpos : 0 < D := by linarith [(by exact_mod_cast (by omega : 0 < Y) : (0 : ℝ) < Y)]
    have hBY : 4 ≤ Real.log (D / Y) := by
      refine hB.trans (Real.log_le_log (by positivity) ?_)
      apply div_le_div_of_nonneg_left hDpos.le (by exact_mod_cast (by omega : 0 < Y)); push_cast; linarith
    have := inv_klog_le (D := D) (k := Y + 1) (by omega) hYD (by linarith)
    push_cast at this ⊢
    rw [add_sub_cancel_right] at this
    linarith [ih hYD' hBY]

/-- `∑_{2 ≤ k ≤ Y} 1/(k log²(D/k)) ≤ 1/log(D/Y) − 1/log D`. -/
theorem sum_inv_klog_sq_le {D : ℝ} {Y : ℕ} (hY : 2 ≤ Y) (hYD : (Y : ℝ) < D)
    (hB : 4 ≤ Real.log (D / Y)) :
    ∑ k ∈ Icc 2 Y, 1 / (k * Real.log (D / k) ^ 2) ≤ 1 / Real.log (D / Y) - 1 / Real.log D := by
  induction Y, hY using Nat.le_induction with
  | base =>
    simp only [Icc_self, sum_singleton]
    have := inv_klog_sq_le (D := D) (k := 2) le_rfl (by exact_mod_cast hYD) hB
    norm_num at this ⊢; exact this
  | succ Y hY ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hYD' : (Y : ℝ) < D := by push_cast at hYD; linarith
    have hDpos : 0 < D := by linarith [(by exact_mod_cast (by omega : 0 < Y) : (0 : ℝ) < Y)]
    have hBY : 4 ≤ Real.log (D / Y) := by
      refine hB.trans (Real.log_le_log (by positivity) ?_)
      apply div_le_div_of_nonneg_left hDpos.le (by exact_mod_cast (by omega : 0 < Y)); push_cast; linarith
    have := inv_klog_sq_le (D := D) (k := Y + 1) (by omega) hYD hB
    push_cast at this ⊢
    rw [add_sub_cancel_right] at this
    linarith [ih hYD' hBY]

end TernaryGoldbach.RSBounds.Moebius003
