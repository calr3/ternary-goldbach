import TernaryGoldbach.Prelim.EOneBound

/-!
# Numerical form of the pointwise bound for `E(y)`

* `wsq_window_sum_le`: the line-zero sum with the weight `1/max(2.39, t)²` is at most `9.62`
  (Jensen counts `logBPz2_3_le`, `logB_window_le`; `∑ log d/d² ≤ 2`, `∑ 1/d² ≤ 2`), so
  `LQW a 0 δ H ≤ e^{δ²/2}(e^{a/2} + 1) · 19.24`.
* `TailBH a 10⁻⁴ 10⁸` is negligible and `V(a, 0, 10⁻⁴) ≤ 3.2·10⁷`.
* `E_bound_sqrt`: with the window `a = 3`, `δ = 10⁻⁴`, `κ = 0.003`: if `|ψ(n) − n| ≤ C√n` on
  `[Y e^{−0.003}, Y e^{3.003}]` and `Y ≥ 10⁶`, then `|E₁Λ(Y) + γ| ≤ (3.01 C + 5.8)/√Y + 10⁻¹³`.
-/

open MeasureTheory Set Filter
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.Prelim
open TernaryGoldbach.PNTMertens TernaryGoldbach.Explicit

/-- `∑_{d ≤ k} log d/d² ≤ 2` (telescoping against `(log d + 2)/d`). -/
theorem sum_log_div_sq_le (k : ℕ) :
    ∑ m ∈ Finset.range k, Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2 ≤ 2 := by
  set G : ℕ → ℝ := fun m => (Real.log ((m : ℝ) + 1) + 2) / ((m : ℝ) + 1) with hG
  have hstep : ∀ m : ℕ, Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2 ≤ G m - G (m + 1) := by
    intro m
    set d : ℝ := (m : ℝ) + 1 with hd
    have hd1 : 1 ≤ d := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    have hd0 : 0 < d := by linarith
    have e1 : ((m + 1 : ℕ) : ℝ) + 1 = d + 1 := by rw [hd]; push_cast; ring
    simp only [hG, e1]
    have hl : d * Real.log ((d + 1) / d) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show 0 < (d + 1) / d by positivity)
      have e : (d + 1) / d - 1 = 1 / d := by field_simp; ring
      rw [e] at this
      calc d * Real.log ((d + 1) / d) ≤ d * (1 / d) := mul_le_mul_of_nonneg_left this hd0.le
        _ = 1 := by field_simp
    have hsplit : Real.log (d + 1) = Real.log d + Real.log ((d + 1) / d) := by
      rw [Real.log_div (by positivity) hd0.ne']; ring
    have hLd : Real.log d ≤ d := (Real.log_le_sub_one_of_pos hd0).trans (by linarith)
    have hL0 : 0 ≤ Real.log d := Real.log_nonneg hd1
    rw [div_sub_div _ _ hd0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity), hsplit]
    nlinarith [mul_nonneg hL0 hd0.le]
  have hsum : ∑ m ∈ Finset.range k, Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2 ≤ G 0 - G k := by
    rw [← Finset.sum_range_sub' G k]
    exact Finset.sum_le_sum fun m _ => hstep m
  have hG0 : G 0 = 2 := by simp [hG]
  have hGk : 0 ≤ G k := by
    simp only [hG]
    exact div_nonneg (by have := Real.log_nonneg (show (1 : ℝ) ≤ (k : ℝ) + 1 by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith); linarith) (by positivity)
  linarith

/-- **The line-zero sum with the weight `1/max(2.39, t)²`.** -/
theorem wsq_window_sum_le (J : ℕ) :
    ∑ m ∈ Finset.range J, Real.log (BPz2 (((m : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * Wsq (6 * (m : ℝ)) ≤ 9.62 := by
  have hL := log_10_336_ge
  have hL0 : 0 < Real.log (10 / 3.36) := lt_of_lt_of_le (by norm_num) hL
  rcases Nat.eq_zero_or_pos J with hJ | hJ
  · rw [hJ]; norm_num
  obtain ⟨k, rfl⟩ : ∃ k, J = k + 1 := ⟨J - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : Real.log (BPz2 ((((0 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) / Real.log (10 / 3.36) *
      Wsq (6 * ((0 : ℕ) : ℝ)) ≤ 39.15 / 1.0906 / 2.39 ^ 2 := by
    have e : (((0 : ℕ) : ℝ) + 1 / 2) * 6 = 3 := by norm_num
    have e2 : Wsq (6 * ((0 : ℕ) : ℝ)) = 1 / 2.39 ^ 2 := by
      unfold Wsq; rw [Nat.cast_zero, mul_zero, max_eq_left (by norm_num)]
    rw [e, e2]
    have h3 := logBPz2_3_le
    have hpos := (polyDatum_zeta2.log_pos 3).le
    have : Real.log (BPz2 3 / 0.355) / Real.log (10 / 3.36) ≤ 39.15 / 1.0906 := by
      rw [div_le_div_iff₀ hL0 (by norm_num)]; nlinarith
    rw [mul_one_div, div_div, div_div]
    calc Real.log (BPz2 3 / 0.355) / (Real.log (10 / 3.36) * 2.39 ^ 2)
        = Real.log (BPz2 3 / 0.355) / Real.log (10 / 3.36) / 2.39 ^ 2 := by rw [div_div]
      _ ≤ 39.15 / 1.0906 / 2.39 ^ 2 := by gcongr
      _ = 39.15 / (1.0906 * 2.39 ^ 2) := by rw [div_div]
  have hterm : ∀ m ∈ Finset.range k, Real.log (BPz2 ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * Wsq (6 * ((m + 1 : ℕ) : ℝ)) ≤
      1 / (36 * 1.0906) * (30.17 * (1 / ((m : ℝ) + 1) ^ 2) +
        10 * (Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ 2) + 25.17 * (1 / ((m : ℝ) + 1) ^ 2)) := by
    intro m _
    have hm := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hw := logB_window_le m
    have hpos := (polyDatum_zeta2.log_pos ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6)).le
    set d : ℝ := (m : ℝ) + 1 with hdd
    have hd1 : 1 ≤ d := by linarith
    have hd0 : 0 < d := by linarith
    have hW : Wsq (6 * ((m + 1 : ℕ) : ℝ)) = 1 / (36 * d ^ 2) := by
      unfold Wsq
      have e : (6 : ℝ) * ((m + 1 : ℕ) : ℝ) = 6 * d := by rw [hdd]; push_cast; ring
      rw [e, max_eq_right (by linarith)]; ring
    rw [hW]
    set X := Real.log (BPz2 ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) with hX
    have hXL : X / Real.log (10 / 3.36) ≤ X / 1.0906 :=
      div_le_div_of_nonneg_left hpos (by norm_num) hL
    have h25 : 25.17 / d ≤ 25.17 := by rw [div_le_iff₀ hd0]; nlinarith
    calc X / Real.log (10 / 3.36) * (1 / (36 * d ^ 2)) ≤ X / 1.0906 * (1 / (36 * d ^ 2)) :=
          mul_le_mul_of_nonneg_right hXL (by positivity)
      _ ≤ (30.17 + 10 * Real.log d + 25.17) / 1.0906 * (1 / (36 * d ^ 2)) := by gcongr; linarith
      _ = _ := by field_simp
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hA := sum_inv_sq_le_two k
  have hB := sum_log_div_sq_le k
  have hS : ∑ m ∈ Finset.range k, Real.log (BPz2 ((((m + 1 : ℕ) : ℝ) + 1 / 2) * 6) / 0.355) /
      Real.log (10 / 3.36) * Wsq (6 * ((m + 1 : ℕ) : ℝ)) ≤ 1 / (36 * 1.0906) * (30.17 * 2 + 10 * 2 + 25.17 * 2) := by
    refine hsum.trans ?_
    gcongr
  have : (39.15 : ℝ) / 1.0906 / 2.39 ^ 2 + 1 / (36 * 1.0906) * (30.17 * 2 + 10 * 2 + 25.17 * 2) ≤ 9.62 := by
    norm_num
  linarith

theorem LQW_le {a δ H : ℝ} : LQW a 0 δ H ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + 1) * 19.24 := by
  unfold LQW
  rw [show (0 : ℝ) / 2 = 0 by norm_num, Real.exp_zero]
  have h := wsq_window_sum_le (JlH 6 H)
  have hpos : 0 ≤ Real.exp (δ ^ 2 / 2) * (Real.exp (a / 2) + 1) := by positivity
  nlinarith

theorem TailBH_le {a : ℝ} (ha : 0 ≤ a) (ha3 : a ≤ 3) : TailBH a 1e-4 1e8 ≤ 1e-15 := by
  unfold TailBH EBg rhoG
  have hr : (0.98 : ℝ) ≤ 1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8)) := by
    have : Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8)) ≤ Real.exp (-4) :=
      Real.exp_le_exp.2 (by norm_num)
    have h4 : Real.exp (-4) ≤ 0.02 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := Real.add_one_le_exp 4
      have h1 := Real.exp_one_gt_d9
      have e : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [pow_le_pow_left₀ (by norm_num) h1.le 4]
    linarith
  have hr0 : 0 < 1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8)) := by linarith
  have he : Real.exp ((1e-4 : ℝ) ^ 2 / 2 + |a|) ≤ 21 := by
    rw [abs_of_nonneg ha]
    have : Real.exp ((1e-4 : ℝ) ^ 2 / 2 + a) ≤ Real.exp 3.01 := Real.exp_le_exp.2 (by norm_num; linarith)
    refine this.trans ?_
    have h1 := Real.exp_one_lt_d9
    have h2 := exp_small_le (t := 0.01) (by norm_num) (by norm_num)
    have e : Real.exp 3.01 = Real.exp 1 ^ 3 * Real.exp 0.01 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    rw [e]
    have : Real.exp 1 ^ 3 ≤ 2.7182818286 ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 3
    nlinarith [Real.exp_pos 0.01, pow_pos (Real.exp_pos 1) 3]
  have hg : Real.exp (-((1e-4 : ℝ) ^ 2 * (1e8 : ℝ) ^ 2 / 2)) ≤ 1.3e-14 :=
    le_trans (Real.exp_le_exp.2 (by norm_num)) exp_neg32_le
  have hl := log_10_3_ge
  have hZ : Z3g BPz2 1e8 ≤ 210.6 := by
    refine le_trans ?_ Z3g_H_le
    unfold Z3g
    refine div_le_div_of_nonneg_right (polyDatum_zeta2.log_mono ?_)
      (log_ratio_pos (by norm_num) (by norm_num)).le
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1e8), abs_of_pos (by norm_num : (0 : ℝ) < 3e10)]; norm_num
  have hZ0 : 0 ≤ Z3g BPz2 1e8 :=
    div_nonneg (polyDatum_zeta2.log_pos _).le (lt_of_lt_of_le (by norm_num) hl).le
  have hc : c3g 10 1e8 ≤ 3.66e-7 := by
    unfold c3g
    rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hl)]
    nlinarith
  have hc0 : 0 ≤ c3g 10 1e8 := by
    unfold c3g; exact div_nonneg (by norm_num) (lt_of_lt_of_le (by norm_num) hl).le
  have hA : 2 * Z3g BPz2 1e8 / (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) ≤ 2 * 210.6 / 0.98 := by
    rw [div_le_div_iff₀ hr0 (by norm_num)]; nlinarith
  have hB : 2 * c3g 10 1e8 / (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) ^ 2 ≤ 2 * 3.66e-7 / 0.98 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0.98 : ℝ) ^ 2 ≤ (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hr 2
    nlinarith
  have hE : 2 * Real.exp ((1e-4 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((1e-4 : ℝ) ^ 2 * (1e8 : ℝ) ^ 2 / 2)) /
      1e8 ≤ 2 * 21 * 1.3e-14 / 1e8 := by gcongr
  have hS0 : 0 ≤ 2 * Z3g BPz2 1e8 / (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) +
      2 * c3g 10 1e8 / (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) ^ 2 :=
    add_nonneg (div_nonneg (by linarith) hr0.le) (div_nonneg (by linarith) (by positivity))
  calc 2 * Real.exp ((1e-4 : ℝ) ^ 2 / 2 + |a|) * Real.exp (-((1e-4 : ℝ) ^ 2 * (1e8 : ℝ) ^ 2 / 2)) / 1e8 *
        (2 * Z3g BPz2 1e8 / (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) +
          2 * c3g 10 1e8 / (1 - Real.exp (-(4.4 * (1e-4 : ℝ) ^ 2 * 1e8))) ^ 2)
      ≤ (2 * 21 * 1.3e-14 / 1e8) * (2 * 210.6 / 0.98 + 2 * 3.66e-7 / 0.98 ^ 2) :=
        mul_le_mul hE (add_le_add hA hB) hS0 (by norm_num)
    _ ≤ 1e-15 := by norm_num

theorem Vg_le {a : ℝ} (ha : 0 ≤ a) : Vg a 0 1e-4 ≤ 3.2e7 := by
  unfold Vg
  have hc1 : 2 / Real.log 2 + 4.8 ≤ 7.6856 := by
    have h := Real.log_two_gt_d9
    have : 2 / Real.log 2 ≤ 2.8856 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hc0 : 0 ≤ 2 / Real.log 2 + 4.8 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have he1 : Real.exp ((1e-4 : ℝ) ^ 2 / 8) ≤ 1.0001 := by
    have h := exp_small_le (t := (1e-4 : ℝ) ^ 2 / 8) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he2 : Real.exp (-(a / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he3 : Real.exp (-((0 : ℝ) / 2)) = 1 := by simp
  have hpi : √(2 * Real.pi) ≤ 2.5067 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith [Real.pi_lt_d4]
  rw [he3]
  calc (2 / Real.log 2 + 4.8) * 82.6 * Real.exp ((1e-4 : ℝ) ^ 2 / 8) * (Real.exp (-(a / 2)) + 1) *
        (√(2 * Real.pi) / 1e-4)
      ≤ 7.6856 * 82.6 * 1.0001 * (1 + 1) * (2.5067 / 1e-4) := by gcongr
    _ ≤ 3.2e7 := by norm_num

/-- `Z(Y)/M(1) ≤ 5.53/√Y + 1.8·10⁵/Y^{3/2} + 10⁻¹³` for `a = 3`, `δ = 10⁻⁴`. -/
theorem Zsm_div_le {Y : ℝ} (hY : 1 ≤ Y) :
    (Zsm 3 1e-4 Y + (22 + 36 * Real.exp (3 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4))) /
        (Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 3 - 1)) ≤
      5.53 / √Y + 1.8e5 * Y ^ (-(3 / 2) : ℝ) + 1e-13 := by
  have hY0 : 0 < Y := by linarith
  have hLQ := LQW_le (a := 3) (δ := 1e-4) (H := 1e8)
  have hT := TailBH_le (a := 3) (by norm_num) le_rfl
  have hV := Vg_le (a := 3) (by norm_num)
  have he1 : Real.exp ((1e-4 : ℝ) ^ 2 / 2) ≤ 1.0001 := by
    have h := exp_small_le (t := (1e-4 : ℝ) ^ 2 / 2) (by positivity) (by norm_num)
    norm_num at h ⊢; linarith
  have he1' : 1 ≤ Real.exp ((1e-4 : ℝ) ^ 2 / 2) := Real.one_le_exp (by positivity)
  have h3 : 20.0855 ≤ Real.exp 3 ∧ Real.exp 3 ≤ 20.0856 := by
    constructor
    · have h1 := Real.exp_one_gt_d9
      have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith [pow_le_pow_left₀ (by norm_num) h1.le 3]
    · exact exp_three_le
  have h15 : Real.exp (3 / 2) ≤ 4.4818 := by
    have e : Real.exp (3 / 2) ^ 2 = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (3 / 2)]
  have hM1 : 19.08 ≤ Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 3 - 1) := by nlinarith
  have hLQ' : LQW 3 0 1e-4 1e8 ≤ 105.5 := by
    refine hLQ.trans ?_; nlinarith [Real.exp_pos (3 / 2)]
  have htail : (22 + 36 * Real.exp (3 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4)) ≤ 1e-14 := by
    have e1 : Real.exp (3 + 0.003) ≤ 21 := by
      rw [Real.exp_add]
      have := exp_small_le (t := 0.003) (by norm_num) (by norm_num)
      have := h3.2
      nlinarith [Real.exp_pos 0.003, Real.exp_pos 3]
    have e2 : Real.exp (-(0.003 / 1e-4)) ≤ 1e-13 := by
      have h32 := exp_neg32_le
      have e : Real.exp (-(0.003 / 1e-4)) = Real.exp (-32) * Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      rw [e]; nlinarith [exp_two_le, Real.exp_pos 2, Real.exp_pos (-32)]
    have : (22 + 36 * Real.exp (3 + 0.003)) * 1e-4 * Real.exp (-(0.003 / 1e-4)) ≤
        (22 + 36 * 21) * 1e-4 * 1e-13 := by gcongr
    linarith [show ((22 : ℝ) + 36 * 21) * 1e-4 * 1e-13 ≤ 1e-14 by norm_num]
  have hsY : Y ^ (-(1 / 2) : ℝ) = 1 / √Y := by
    rw [Real.rpow_neg hY0.le, ← Real.sqrt_eq_rpow, one_div]
  have hp0 : 0 ≤ Y ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hY0.le _
  have hp1 : 0 ≤ Y ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hY0.le _
  have hpi : 3.14 ≤ Real.pi := Real.pi_gt_d2.le
  unfold Zsm
  rw [div_le_iff₀ (by linarith)]
  have hZ1 : Y ^ (-(1 / 2) : ℝ) * LQW 3 0 1e-4 1e8 ≤ 105.5 * Y ^ (-(1 / 2) : ℝ) := by nlinarith
  have hZ3 : 2 / 3 * Y ^ (-(3 / 2) : ℝ) * Vg 3 0 1e-4 / (2 * Real.pi) ≤ 3.4e6 * Y ^ (-(3 / 2) : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have : Vg 3 0 1e-4 ≤ 3.2e7 := hV
    nlinarith
  have hT0 : 2 * TailBH 3 1e-4 1e8 / 1e8 ≤ 1e-22 := by
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  have hsY' : 5.53 / √Y = 5.53 * Y ^ (-(1 / 2) : ℝ) := by rw [hsY]; ring
  rw [hsY']
  set M1 := Real.exp ((1e-4 : ℝ) ^ 2 / 2) * (Real.exp 3 - 1) with hM1d
  have hM1u : M1 ≤ 1.0001 * 19.0856 := by rw [hM1d]; nlinarith
  nlinarith

/-- `|E₁Λ(t) − E₁Λ(⌊t⌋)| ≤ 1/⌊t⌋` for `t ≥ 1`. -/
theorem abs_E1_sub_floor_le {t : ℝ} (ht : 1 ≤ t) : |E₁Λ t - E₁Λ ⌊t⌋₊| ≤ 1 / ⌊t⌋₊ := by
  have hM1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hM0 : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast hM1
  have hle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have e : E₁Λ t - E₁Λ ⌊t⌋₊ = Real.log ⌊t⌋₊ - Real.log t := by
    simp only [E₁Λ, Nat.floor_natCast]; ring
  rw [e, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hM0 hle))]
  have := Real.log_le_sub_one_of_pos (x := t / ⌊t⌋₊) (by positivity)
  rw [Real.log_div (by linarith) hM0.ne'] at this
  have h2 : t / ⌊t⌋₊ - 1 ≤ 1 / ⌊t⌋₊ := by
    rw [div_sub_one hM0.ne', div_le_div_iff_of_pos_right hM0]; linarith
  linarith

variable [Fact TernaryGoldbach.PlattGRH] in
/-- **`|E(Y)| ≤ (3.01 C + 5.8)/√Y + 10⁻¹³`** for `Y ≥ 10⁶` if `|ψ(n) − n| ≤ C√n` on
`[⌊Y e^{−0.003}⌋, Y e^{3.003}]`. -/
theorem E_bound_sqrt {Y C : ℝ} (hY : 1e6 ≤ Y) (hC : 0 ≤ C)
    (hψ : ∀ n : ℕ, ⌊Y * Real.exp (-0.003)⌋₊ ≤ n → (n : ℝ) ≤ Y * Real.exp (3 + 0.003) →
      |psiN n - n| ≤ C * √(n : ℝ)) :
    |E₁Λ Y + Real.eulerMascheroniConstant| ≤ (3.01 * C + 5.8) / √Y + 1e-13 := by
  have hY0 : 0 < Y := by linarith
  set M₂ := ⌊Y * Real.exp (-0.003)⌋₊ with hM₂
  have hek : 0.997 ≤ Real.exp (-0.003) := by
    have := Real.add_one_le_exp (-0.003); linarith
  have hek1 : Real.exp (-0.003) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have hM₂ge : 0.9969 * Y ≤ (M₂ : ℝ) := by
    have h1 : Y * Real.exp (-0.003) < (M₂ : ℝ) + 1 := Nat.lt_floor_add_one _
    have := mul_le_mul_of_nonneg_left hek hY0.le
    nlinarith
  have hM₂1 : 1 ≤ M₂ := by
    have : (1 : ℝ) ≤ M₂ := by linarith
    exact_mod_cast this
  have hM₂0 : (0 : ℝ) < M₂ := by linarith
  have hM₂le : (M₂ : ℝ) ≤ Y := (Nat.floor_le (by positivity)).trans (by nlinarith)
  set A := 4 / (M₂ : ℝ) + 3 * C / √(M₂ : ℝ) with hA
  have hA0 : 0 ≤ A := by positivity
  -- the window
  have hwin : ∀ v : ℝ, Real.exp (-0.003) ≤ v → v ≤ Real.exp (3 + 0.003) →
      |E₁Λ (Y * v) - E₁Λ Y| ≤ A := by
    intro v hv1 hv2
    have hv0 : 0 < v := lt_of_lt_of_le (Real.exp_pos _) hv1
    have hYv0 : 0 < Y * v := by positivity
    rcases le_or_gt Y (Y * v) with hge | hlt
    · -- `t = Yv ≥ Y`
      set M₀ := ⌊Y⌋₊ with hM₀
      have hM₀1 : 1 ≤ M₀ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ Y))
      have hM₀le : (M₀ : ℝ) ≤ Y := Nat.floor_le hY0.le
      have hM₂M₀ : M₂ ≤ M₀ := Nat.floor_mono (by nlinarith)
      have h1 := E1_diff_sqrt hM₀1 (hM₀le.trans hge) hC fun n hn1 hn2 => by
        refine hψ n (hM₂M₀.trans hn1) ?_
        have : (n : ℝ) ≤ Y * v := le_trans (by exact_mod_cast hn2) (Nat.floor_le hYv0.le)
        nlinarith
      have h2 := abs_E1_sub_floor_le (t := Y) (by linarith)
      rw [← hM₀] at h2
      have hM₀0 : (0 : ℝ) < M₀ := by exact_mod_cast hM₀1
      have hM₂M₀' : (M₂ : ℝ) ≤ M₀ := by exact_mod_cast hM₂M₀
      have k1 : 3 / (M₀ : ℝ) + 1 / M₀ ≤ 4 / M₂ := by
        rw [← add_div]; norm_num; exact div_le_div_of_nonneg_left (by norm_num) hM₂0 hM₂M₀'
      have k2 : 3 * C / √(M₀ : ℝ) ≤ 3 * C / √(M₂ : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hM₂0) (Real.sqrt_le_sqrt hM₂M₀')
      calc |E₁Λ (Y * v) - E₁Λ Y| ≤ |E₁Λ (Y * v) - E₁Λ M₀| + |E₁Λ Y - E₁Λ M₀| := by
            have := abs_sub_le (E₁Λ (Y * v)) (E₁Λ M₀) (E₁Λ Y)
            rwa [abs_sub_comm (E₁Λ M₀) (E₁Λ Y)] at this
        _ ≤ (3 / M₀ + 3 * C / √(M₀ : ℝ)) + 1 / M₀ := add_le_add h1 h2
        _ ≤ A := by rw [hA]; linarith
    · -- `t = Yv < Y`
      set M₁ := ⌊Y * v⌋₊ with hM₁
      have hM₂M₁ : M₂ ≤ M₁ := Nat.floor_mono (by nlinarith)
      have hM₁1 : 1 ≤ M₁ := hM₂1.trans hM₂M₁
      have hM₁0 : (0 : ℝ) < M₁ := by exact_mod_cast hM₁1
      have hM₁le : (M₁ : ℝ) ≤ Y := (Nat.floor_le hYv0.le).trans hlt.le
      have h1 := E1_diff_sqrt hM₁1 hM₁le hC fun n hn1 hn2 => by
        refine hψ n (hM₂M₁.trans hn1) ?_
        have : (n : ℝ) ≤ Y := le_trans (by exact_mod_cast hn2) (Nat.floor_le hY0.le)
        have : Y ≤ Y * Real.exp (3 + 0.003) := le_mul_of_one_le_right hY0.le (Real.one_le_exp (by norm_num))
        linarith
      have hYv1 : 1 ≤ Y * v := by
        have : (1 : ℝ) ≤ M₁ := by exact_mod_cast hM₁1
        have := Nat.floor_le hYv0.le (a := Y * v)
        linarith
      have h2 := abs_E1_sub_floor_le hYv1
      rw [← hM₁] at h2
      have hM₂M₁' : (M₂ : ℝ) ≤ M₁ := by exact_mod_cast hM₂M₁
      have k1 : 3 / (M₁ : ℝ) + 1 / M₁ ≤ 4 / M₂ := by
        rw [← add_div]; norm_num; exact div_le_div_of_nonneg_left (by norm_num) hM₂0 hM₂M₁'
      have k2 : 3 * C / √(M₁ : ℝ) ≤ 3 * C / √(M₂ : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 hM₂0) (Real.sqrt_le_sqrt hM₂M₁')
      calc |E₁Λ (Y * v) - E₁Λ Y| ≤ |E₁Λ (Y * v) - E₁Λ M₁| + |E₁Λ Y - E₁Λ M₁| := by
            have := abs_sub_le (E₁Λ (Y * v)) (E₁Λ M₁) (E₁Λ Y)
            rwa [abs_sub_comm (E₁Λ M₁) (E₁Λ Y)] at this
        _ ≤ 1 / M₁ + (3 / M₁ + 3 * C / √(M₁ : ℝ)) := add_le_add h2 h1
        _ ≤ A := by rw [hA]; linarith
  have hE := E_bound_win (a := 3) (δ := 1e-4) (κ := 0.003) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) hA0 hwin
  have hZ := Zsm_div_le (Y := Y) (by linarith)
  refine hE.trans ?_
  -- numerics
  have hsY : 1000 ≤ √Y := by rw [Real.le_sqrt (by norm_num) hY0.le]; norm_num; linarith
  have hsM : √(0.9969 * Y) ≤ √(M₂ : ℝ) := Real.sqrt_le_sqrt hM₂ge
  have hsq : √(0.9969 * Y) = √0.9969 * √Y := Real.sqrt_mul (by norm_num) Y
  have hs99 : 0.9984 ≤ √(0.9969 : ℝ) := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsMY : 0.9984 * √Y ≤ √(M₂ : ℝ) := by nlinarith [Real.sqrt_nonneg Y]
  have hspos : 0 < √Y := by linarith
  have hk1 : 3 * C / √(M₂ : ℝ) ≤ 3.01 * C / √Y := by
    rw [div_le_div_iff₀ (by linarith) hspos]
    nlinarith
  have hk2 : 4 / (M₂ : ℝ) ≤ 0.005 / √Y := by
    rw [div_le_div_iff₀ hM₂0 hspos]
    have : Y = √Y * √Y := (Real.mul_self_sqrt hY0.le).symm
    nlinarith
  have hk3 : 1.8e5 * Y ^ (-(3 / 2) : ℝ) ≤ 0.18 / √Y := by
    have e : Y ^ (-(3 / 2) : ℝ) = 1 / (Y * √Y) := by
      rw [Real.rpow_neg hY0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hY0,
        Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
    rw [e, mul_one_div, div_le_div_iff₀ (by positivity) hspos]
    nlinarith
  have e2 : (3.01 * C + 5.8) / √Y = 3.01 * C / √Y + 5.53 / √Y + 0.18 / √Y + 0.005 / √Y + 0.085 / √Y := by
    field_simp; ring
  rw [e2, hA]
  have : 0 ≤ 0.085 / √Y := by positivity
  linarith

end TernaryGoldbach.Prelim
