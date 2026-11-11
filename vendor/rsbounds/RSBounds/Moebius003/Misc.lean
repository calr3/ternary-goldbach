/-
Copyright (c) 2026 Harald Andrés Helfgott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harald Andrés Helfgott, Claude
-/
import RSBounds.Moebius003.SmallM
import RSBounds.Moebius003.Inputs
import RSBounds.Moebius003.MofN
import RSBounds.Moebius003.Squarefree
import RSBounds.Moebius003.LogCert

/-!
# Lemma 7 of the note: consequences of (M), and two sums

* (M) in the form `|M(n)| ≤ 0.571 √n`, `33 ≤ n ≤ 10⁹`.
* (a) `S(33) ≤ 5.33`, `S(x) ≤ S(33) + 2c_M(√(x−1) − √32)` for `33 ≤ x ≤ X₀ + 1`; `S(X₀) ≤ I₀ = 36113`.
* (b) `|C₀| ≤ 1743`.
* (d) `∑_{X₀ ≤ t < u} 1/log² t ≤ λ₀ u/log² u` with `λ₀ = 1.107`.
* (e) `∑_{a ≤ t < b} 1/log t ≤ b/(log b − 2) − a/(log a − 2)` for `log a ≥ 5`.

Lemma 7(c) is `Range2`.
-/

namespace TernaryGoldbach.RSBounds.Moebius003

open ArithmeticFunction Finset Real
open scoped ArithmeticFunction.Moebius

/-- `c_M = 0.571`. -/
noncomputable def cM : ℝ := 0.571

/-- (M) as `|M(n)| ≤ 0.571 √n`. -/
theorem abs_M_le_sqrt (h : Inputs) {n : ℕ} (h1 : 33 ≤ n) (h2 : n ≤ X0) :
    |M n| ≤ cM * Real.sqrt n := by
  have hM := h.Mert n h1 (by simpa [X0] using h2)
  have hcast : M n = ((∑ k ∈ Icc 1 n, μ k : ℤ) : ℝ) := by rw [M]; push_cast; rfl
  have hR : (10 : ℝ) ^ 6 * M n ^ 2 ≤ 326041 * n := by
    rw [hcast]; exact_mod_cast hM
  have hsq : M n ^ 2 ≤ (cM * Real.sqrt n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; simp only [cM]; nlinarith
  exact abs_le_of_sq_le_sq' hsq (by unfold cM; positivity) |> fun h => abs_le.2 h

theorem log_one_add_inv_le (t : ℕ) (ht : 1 ≤ t) : Real.log (1 + 1 / (t : ℝ)) ≤ 1 / t := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / (t : ℝ) by positivity)
  linarith

/-- `S(33) ≤ 5.33`. -/
theorem S33_le : S 33 ≤ 5.33 := by
  have h1 : S 33 ≤ ∑ t ∈ Ico 1 33, |M t| * (1 / (t : ℝ)) := by
    refine sum_le_sum fun t ht => ?_
    exact mul_le_mul_of_nonneg_left (log_one_add_inv_le t (mem_Ico.1 ht).1) (abs_nonneg _)
  refine h1.trans (le_of_eq_of_le ?_ (show (384190016043739 / 72201776446800 : ℝ) ≤ 5.33 by norm_num))
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.cast_ofNat, M_val_1, M_val_2, M_val_3, M_val_4, M_val_5, M_val_6, M_val_7, M_val_8, M_val_9, M_val_10, M_val_11, M_val_12, M_val_13, M_val_14, M_val_15, M_val_16, M_val_17, M_val_18, M_val_19, M_val_20, M_val_21, M_val_22, M_val_23, M_val_24, M_val_25, M_val_26, M_val_27, M_val_28, M_val_29, M_val_30, M_val_31, M_val_32]
  norm_num

/-- Lemma 7(a). -/
theorem S_le (h : Inputs) {x : ℕ} (h1 : 33 ≤ x) (h2 : x ≤ X0 + 1) :
    S x ≤ S 33 + 2 * cM * (Real.sqrt (x - 1 : ℕ) - Real.sqrt 32) := by
  induction x, h1 using Nat.le_induction with
  | base => norm_num
  | succ x hx ih =>
    rw [S_succ (by omega)]
    have ih' := ih (by omega)
    have hM := abs_M_le_sqrt h hx (by omega)
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    have hl := log_one_add_inv_le x (by omega)
    have hcM : (0 : ℝ) ≤ cM := by unfold cM; norm_num
    have hlog0 : 0 ≤ Real.log (1 + 1 / (x : ℝ)) := by
      have : 0 ≤ 1 / (x : ℝ) := by positivity
      exact Real.log_nonneg (by linarith)
    have hterm : |M x| * Real.log (1 + 1 / (x : ℝ)) ≤ cM * (1 / Real.sqrt x) := by
      have hsq : Real.sqrt (x : ℝ) * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
      have e : (cM * Real.sqrt x) * (1 / (x : ℝ)) = cM * (1 / Real.sqrt x) := by
        have h1 : Real.sqrt (x : ℝ) / x = 1 / Real.sqrt x := by
          rw [div_eq_div_iff hxpos.ne' hsx.ne', one_mul, hsq]
        rw [mul_assoc, mul_one_div, h1]
      calc |M x| * Real.log (1 + 1 / (x : ℝ)) ≤ (cM * Real.sqrt x) * (1 / x) :=
            mul_le_mul hM hl hlog0 (by positivity)
        _ = cM * (1 / Real.sqrt x) := e
    have h3 : 1 / Real.sqrt x ≤ 2 * (Real.sqrt x - Real.sqrt (x - 1 : ℕ)) := by
      have := inv_sqrt_le_two_mul_sub (k := x - 1) (by omega)
      rw [show x - 1 + 1 = x by omega] at this
      exact this
    rw [show x + 1 - 1 = x by omega]
    nlinarith

/-- `I₀ = 36113`. -/
noncomputable def I0B : ℝ := 36113

/-- `C₀ ≤ 1743`. -/
noncomputable def C0B : ℝ := 1743

theorem S_X0_le (h : Inputs) : S X0 ≤ I0B := by
  have h1 := S_le h (x := X0) (by norm_num [X0]) (by omega)
  have h2 := S33_le
  have h3 : Real.sqrt ((X0 - 1 : ℕ) : ℝ) ≤ 31623 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num [X0]
  have h4 : (5.656 : ℝ) ≤ Real.sqrt 32 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  unfold I0B; unfold cM at h1; linarith

theorem log_X0_ge : (20.72 : ℝ) ≤ Real.log X0 := by
  have h2 : (20.72 : ℚ) ≤ LogCert.logLo (10 ^ 9) := by decide +kernel
  calc (20.72 : ℝ) = ((20.72 : ℚ) : ℝ) := by norm_num
    _ ≤ ((LogCert.logLo (10 ^ 9) : ℚ) : ℝ) := Rat.cast_le.mpr h2
    _ ≤ Real.log (((10 ^ 9 : ℚ)) : ℝ) := LogCert.logLo_le (by norm_num)
    _ = Real.log X0 := by norm_num [X0]

theorem abs_C0_le_C0B (h : Inputs) : |C0| ≤ C0B := by
  have h1 := abs_C0_le
  have h2 := S_X0_le h
  have h3 := log_X0_ge
  have hS : 0 ≤ S X0 := sum_nonneg fun t _ => mul_nonneg (abs_nonneg _)
    (Real.log_nonneg (by have : (0 : ℝ) ≤ 1 / (t : ℝ) := by positivity
                         linarith))
  calc |C0| ≤ S X0 / Real.log X0 := h1
    _ ≤ I0B / 20.72 := div_le_div₀ (by unfold I0B; norm_num) h2 (by norm_num) h3
    _ ≤ C0B := by unfold I0B C0B; norm_num

/-- `λ₀ = 1.107 ≥ (1 − 2/log X₀)⁻¹`. -/
noncomputable def lam0 : ℝ := 1.107

theorem log_succ_sub_le {t : ℕ} (ht : 1 ≤ t) :
    Real.log ((t : ℝ) + 1) - Real.log t ≤ 1 / t := by
  rw [log_succ_sub_log ht]; exact log_one_add_inv_le t ht

/-- The step of Lemma 7(d). -/
theorem inv_log_sq_le_step {t : ℕ} (ht : X0 ≤ t) :
    1 / Real.log t ^ 2 ≤ lam0 * (((t : ℝ) + 1) / Real.log ((t : ℝ) + 1) ^ 2 - t / Real.log t ^ 2) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (by unfold X0 at ht; omega : 0 < t)
  have hX : (10 ^ 9 : ℝ) ≤ t := by exact_mod_cast (show 10 ^ 9 ≤ t by simpa [X0] using ht)
  set a := Real.log (t : ℝ)
  set b := Real.log ((t : ℝ) + 1)
  have ha : 20.72 ≤ a := log_X0_ge.trans (Real.log_le_log (by norm_num [X0]) (by exact_mod_cast ht))
  have hab : a ≤ b := Real.log_le_log htpos (by linarith)
  have hε : b - a ≤ 1 / t := log_succ_sub_le (by unfold X0 at ht; omega)
  have hε' : b - a ≤ 1 / 10 ^ 9 := hε.trans (one_div_le_one_div_of_le (by norm_num) hX)
  have htε : (t : ℝ) * (b - a) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hε htpos.le
    rwa [mul_one_div_cancel htpos.ne'] at this
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  -- `(t+1)/b² − t/a² ≥ (a² − a − b)/(a² b²)`
  have h1 : (a ^ 2 - a - b) / (a ^ 2 * b ^ 2) ≤ ((t : ℝ) + 1) / b ^ 2 - t / a ^ 2 := by
    rw [div_sub_div _ _ (by positivity) (by positivity), mul_comm (b ^ 2) (a ^ 2)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right htε (by linarith : (0 : ℝ) ≤ b + a)]
  -- `b² ≤ λ₀ (a² − a − b)`
  have h2 : b ^ 2 ≤ lam0 * (a ^ 2 - a - b) := by
    unfold lam0
    have hε0 : 0 ≤ b - a := by linarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - 20.72) (by linarith : (0 : ℝ) ≤ a - 20.72),
      mul_nonneg hε0 (by linarith : (0 : ℝ) ≤ a)]
  have hpos : 0 < a ^ 2 - a - b := by nlinarith
  calc 1 / a ^ 2 ≤ lam0 * ((a ^ 2 - a - b) / (a ^ 2 * b ^ 2)) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul,
          div_le_iff₀ (by positivity)]
        nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by unfold lam0; norm_num)

/-- **Lemma 7(d)** (discrete): `∑_{X₀ ≤ t < u} 1/log² t ≤ λ₀ u/log² u`. -/
theorem sum_inv_log_sq_le {u : ℕ} (hu : X0 ≤ u) :
    ∑ t ∈ Ico X0 u, 1 / Real.log t ^ 2 ≤ lam0 * u / Real.log u ^ 2 := by
  induction u, hu using Nat.le_induction with
  | base => simp; unfold lam0; positivity
  | succ u hu ih =>
    rw [sum_Ico_succ_top hu]
    have := inv_log_sq_le_step hu
    push_cast
    have e : lam0 * ((u : ℝ) + 1) / Real.log ((u : ℝ) + 1) ^ 2 =
        lam0 * u / Real.log u ^ 2 + lam0 * (((u : ℝ) + 1) / Real.log ((u : ℝ) + 1) ^ 2 -
          u / Real.log u ^ 2) := by ring
    rw [e]; linarith

/-- The step of Lemma 7(e). -/
theorem inv_log_le_step {t : ℕ} (ht : Real.exp 5 ≤ t) :
    1 / Real.log t ≤ ((t : ℝ) + 1) / (Real.log ((t : ℝ) + 1) - 2) - t / (Real.log t - 2) := by
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (Real.exp_pos 5) ht
  have ht1 : 1 ≤ t := by exact_mod_cast (show (1 : ℝ) ≤ t by
    have : (1 : ℝ) ≤ Real.exp 5 := Real.one_le_exp (by norm_num)
    linarith)
  set a := Real.log (t : ℝ)
  set b := Real.log ((t : ℝ) + 1)
  have ha : 5 ≤ a := by
    rw [show (5 : ℝ) = Real.log (Real.exp 5) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 5) ht
  have hab : a ≤ b := Real.log_le_log htpos (by linarith)
  have hε : b - a ≤ 1 / t := log_succ_sub_le ht1
  have htε : (t : ℝ) * (b - a) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hε htpos.le
    rwa [mul_one_div_cancel htpos.ne'] at this
  -- `(a − 2)(b − a) ≤ 1`: since `a ≤ t − 1` and `t (b − a) ≤ 1`
  have hat : a ≤ t := by have := Real.log_le_sub_one_of_pos htpos; linarith
  have h3 : (a - 2) * (b - a) ≤ 1 := by
    have : (a - 2) * (b - a) ≤ t * (b - a) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  rw [div_sub_div _ _ (by linarith) (by linarith), div_le_div_iff₀ (by linarith) (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left htε (by linarith : (0 : ℝ) ≤ a)]

/-- **Lemma 7(e)** (discrete): `∑_{a ≤ t < b} 1/log t ≤ b/(log b − 2) − a/(log a − 2)`. -/
theorem sum_inv_log_le {a b : ℕ} (ha : Real.exp 5 ≤ a) (hab : a ≤ b) :
    ∑ t ∈ Ico a b, 1 / Real.log t ≤ b / (Real.log b - 2) - a / (Real.log a - 2) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [sum_Ico_succ_top hb]
    have hb' : Real.exp 5 ≤ b := ha.trans (by exact_mod_cast hb)
    have := inv_log_le_step hb'
    push_cast
    linarith

end TernaryGoldbach.RSBounds.Moebius003
